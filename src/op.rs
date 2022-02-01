use crate::token::Token;
use core::iter::Peekable;

#[derive(Debug, PartialEq)]
pub enum Op<'a> {
	Call {
		function: &'a str,
		arguments: Box<[Expression<'a>]>,
		pipe_out: Box<[(&'a str, &'a str)]>,
		pipe_in: Box<[(&'a str, &'a str)]>,
	},
	If {
		condition: Expression<'a>,
		if_true: Box<[Self]>,
		if_false: Box<[Self]>,
	},
	While {
		condition: Box<[Self]>,
		while_true: Box<[Self]>,
	},
	For {
		range: ForRange,
	},
	Assign {
		variable: &'a str,
		expression: Expression<'a>,
	},
}

#[derive(Debug, PartialEq)]
pub enum Expression<'a> {
	String(Box<str>),
	Variable(&'a str),
	Integer(isize),
	Statement(Box<[Op<'a>]>),
}

#[derive(Debug, PartialEq)]
pub enum ForRange {}

pub fn parse<'a>(mut tokens: impl Iterator<Item = Token<'a>>) -> Result<Box<[Op<'a>]>, ParseError> {
	parse_inner(Default::default(), &mut tokens.peekable(), false).map(|v| v.into())
}

/// Parse an argument, i.e. `print <arg> <arg> ...`
fn parse_arg<'a, I>(tokens: &mut Peekable<I>) -> Result<Expression<'a>, ParseError>
where
	I: Iterator<Item = Token<'a>>,
{
	match tokens.next().unwrap() {
		Token::ScopeOpen => todo!("scope open"),
		Token::ScopeClose => todo!("scope close"),
		Token::Word(s) => Ok(Expression::String(s.into())),
		Token::String(s) => {
			// TODO unescape
			Ok(Expression::String(s.into()))
		}
		Token::Variable(v) => Ok(Expression::Variable(v)),
		Token::Integer(i) => Ok(Expression::Integer(i)),
		t => todo!("parse {:?}", t),
	}
}

/// Parse an "expression", i.e. `if <expr>`, `for v in <expr>`, ..
fn parse_expr<'a, I>(tokens: &mut Peekable<I>) -> Result<Expression<'a>, ParseError>
where
	I: Iterator<Item = Token<'a>>,
{
	match tokens.next().expect("todo") {
		Token::ScopeOpen => todo!("scope open"),
		Token::ScopeClose => todo!("scope close"),
		Token::Word(f) => {
			let mut args = Vec::new();
			while let Some(tk) = tokens.peek() {
				if tk == &Token::Separator {
					tokens.next().unwrap();
					break;
				}
				args.push(parse_arg(tokens)?);
			}
			Ok(Expression::Statement(
				[Op::Call {
					function: f,
					arguments: args.into(),
					pipe_out: [].into(),
					pipe_in: [].into(),
				}]
				.into(),
			))
		}
		Token::String(s) => Ok(Expression::String(s.into())),
		Token::Variable(s) => {
			assert_eq!(tokens.next(), Some(Token::Separator));
			Ok(Expression::Variable(s))
		}
		Token::Integer(s) => Ok(Expression::Integer(s)),
		Token::Separator => todo!("unexpected separator (should we allow this?)"),
		t => todo!("parse {:?}", t),
	}
}

fn parse_inner<'a>(
	mut ops: Vec<Op<'a>>,
	tokens: &mut Peekable<impl Iterator<Item = Token<'a>>>,
	in_scope: bool,
) -> Result<Vec<Op<'a>>, ParseError> {
	while let Some(tk) = tokens.next() {
		let next_is_close = tokens.peek().map_or(true, |t| t == &Token::ScopeClose);
		match tk {
			Token::ScopeOpen => ops = parse_inner(ops, tokens, true)?,
			Token::ScopeClose => {
				return in_scope
					.then(|| ops.into())
					.ok_or(ParseError::CloseScopeWithoutOpen);
			}
			Token::Word("if") => {
				ops.push(Op::If {
					condition: parse_expr(tokens)?,
					if_true: match parse_expr(tokens)? {
						Expression::Statement(c) => c,
						_ => [].into(), // TODO
					},
					if_false: [].into(), // TODO
				})
			}
			Token::Word("for") => todo!("for"),
			Token::Word("while") => todo!("for"),
			Token::Word(f) => {
				let mut args = Vec::new();
				let mut pipe_out = Vec::new();
				let mut pipe_in = Vec::new();
				while tokens.peek().map_or(false, |t| t != &Token::Separator) {
					match tokens.next().unwrap() {
						Token::ScopeOpen => todo!("scope open"),
						Token::ScopeClose => todo!("scope close"),
						Token::Word(s) => args.push(Expression::String(s.into())),
						Token::String(s) => {
							// TODO unescape
							args.push(Expression::String(s.into()))
						}
						Token::Variable(v) => args.push(Expression::Variable(v)),
						Token::Integer(i) => args.push(Expression::Integer(i)),
						Token::PipeOut { from, to } => pipe_out.push((from, to)),
						Token::PipeIn { from, to } => pipe_in.push((from, to)),
						t => todo!("parse {:?}", t),
					}
				}
				ops.push(Op::Call {
					function: f,
					arguments: args.into(),
					pipe_out: pipe_out.into(),
					pipe_in: pipe_in.into(),
				});
			}
			Token::Variable(s) if tokens.peek() == Some(&Token::Word("=")) => {
				tokens.next().unwrap();
				ops.push(Op::Assign {
					variable: s,
					// TODO parse_expr would be a better fit
					expression: parse_arg(tokens)?,
				})
			}
			Token::Variable(_) | Token::String(_) | Token::Integer(_) => {
				// TODO add warning for redundant integer
			}
			Token::Separator => {}
			t => todo!("parse {:?}", t),
		}
	}
	(!in_scope)
		.then(|| ops.into())
		.ok_or(ParseError::UnclosedScope)
}

#[derive(Debug)]
pub enum ParseError {
	CloseScopeWithoutOpen,
	UnclosedScope,
}

#[cfg(test)]
mod test {
	use super::*;
	use crate::token::TokenParser;

	#[test]
	fn print() {
		let s = "print Hello world!";
		assert_eq!(
			&*parse(TokenParser::new(s).map(Result::unwrap)).unwrap(),
			[Op::Call {
				function: "print".into(),
				arguments: [
					Expression::String("Hello".into()),
					Expression::String("world!".into()),
				]
				.into(),
				pipe_out: [].into(),
				pipe_in: [].into(),
			}]
		);
	}

	#[test]
	fn print_twice() {
		let s = "print Hello; print world!";
		assert_eq!(
			&*parse(TokenParser::new(s).map(Result::unwrap)).unwrap(),
			[
				Op::Call {
					function: "print".into(),
					arguments: [Expression::String("Hello".into()),].into(),
					pipe_out: [].into(),
					pipe_in: [].into(),
				},
				Op::Call {
					function: "print".into(),
					arguments: [Expression::String("world!".into()),].into(),
					pipe_out: [].into(),
					pipe_in: [].into(),
				}
			]
		);
	}

	#[test]
	fn cond_if() {
		let s = "if some_cond; print it is true";
		assert_eq!(
			&*parse(TokenParser::new(s).map(Result::unwrap)).unwrap(),
			[Op::If {
				condition: Expression::Statement(
					[Op::Call {
						function: "some_cond".into(),
						arguments: [].into(),
						pipe_out: [].into(),
						pipe_in: [].into(),
					},]
					.into()
				),
				if_true: [Op::Call {
					function: "print".into(),
					arguments: [
						Expression::String("it".into()),
						Expression::String("is".into()),
						Expression::String("true".into()),
					]
					.into(),
					pipe_out: [].into(),
					pipe_in: [].into(),
				},]
				.into(),
				if_false: [].into(),
			}]
		);
	}

	#[test]
	fn variable() {
		let s = "@a = $5; @b = \"five\"; print @a is pronounced as @b";
		assert_eq!(
			&*parse(TokenParser::new(s).map(Result::unwrap)).unwrap(),
			[
				Op::Assign {
					variable: "a".into(),
					expression: Expression::Integer(5),
				},
				Op::Assign {
					variable: "b".into(),
					expression: Expression::String("five".into()),
				},
				Op::Call {
					function: "print".into(),
					arguments: [
						Expression::Variable("a".into()),
						Expression::String("is".into()),
						Expression::String("pronounced".into()),
						Expression::String("as".into()),
						Expression::Variable("b".into()),
					]
					.into(),
					pipe_out: [].into(),
					pipe_in: [].into(),
				},
			]
		);
	}
}
