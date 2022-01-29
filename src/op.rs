use crate::token::Token;
use core::iter::Peekable;

#[derive(Debug, PartialEq)]
pub enum Op {
	Call {
		function: Box<str>,
		arguments: Box<[Argument]>,
	},
	If {
		condition: Box<[Self]>,
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
		variable: Box<str>,
		statement: Argument,
	},
	Return {
		statement: Argument,
	},
}

#[derive(Debug, PartialEq)]
pub enum Argument {
	String(Box<str>),
	Variable(Box<str>),
	Integer(isize),
	Statement(Box<[Op]>),
}

#[derive(Debug, PartialEq)]
pub enum ForRange {}

pub fn parse<'a>(mut tokens: impl Iterator<Item = Token<'a>>) -> Result<Box<[Op]>, ParseError> {
	parse_inner(Default::default(), &mut tokens.peekable(), false).map(|v| v.into())
}

/// Parse an argument, i.e. `print <arg> <arg> ...`
fn parse_arg<'a, I>(tokens: &mut Peekable<I>) -> Result<Argument, ParseError>
where
	I: Iterator<Item = Token<'a>>,
{
	match tokens.next().unwrap() {
		Token::ScopeOpen => todo!("scope open"),
		Token::ScopeClose => todo!("scope close"),
		Token::Word(s) => Ok(Argument::String(s.into())),
		Token::String(s) => {
			// TODO unescape
			Ok(Argument::String(s.into()))
		}
		Token::Variable(v) => Ok(Argument::Variable(v.into())),
		Token::Integer(i) => Ok(Argument::Integer(i)),
		t => todo!("parse {:?}", t),
	}
}

/// Parse an "expression", i.e. `if <expr>`, `for v in <expr>`, ..
fn parse_expr<'a, I>(tokens: &mut Peekable<I>) -> Result<Box<[Op]>, ParseError>
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
			Ok([Op::Call {
				function: f.into(),
				arguments: args.into(),
			}]
			.into())
		}
		Token::String(s) => Ok([Op::Return {
			statement: Argument::String(s.into()),
		}]
		.into()),
		Token::Variable(s) => Ok([Op::Return {
			statement: Argument::Variable(s.into()),
		}]
		.into()),
		Token::Integer(s) => Ok([Op::Return {
			statement: Argument::Integer(s),
		}]
		.into()),
		Token::Separator => todo!("unexpected separator (should we allow this?)"),
		t => todo!("parse {:?}", t),
	}
}

fn parse_inner<'a>(
	mut ops: Vec<Op>,
	tokens: &mut Peekable<impl Iterator<Item = Token<'a>>>,
	in_scope: bool,
) -> Result<Vec<Op>, ParseError> {
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
					if_true: parse_expr(tokens)?,
					if_false: [].into(), // TODO
				})
			}
			Token::Word("for") => todo!("for"),
			Token::Word("while") => todo!("for"),
			Token::Word(f) => {
				let mut args = Vec::new();
				while tokens.peek().map_or(false, |t| t != &Token::Separator) {
					match tokens.next().unwrap() {
						Token::ScopeOpen => todo!("scope open"),
						Token::ScopeClose => todo!("scope close"),
						Token::Word(s) => args.push(Argument::String(s.into())),
						Token::String(s) => {
							// TODO unescape
							args.push(Argument::String(s.into()))
						}
						Token::Variable(v) => args.push(Argument::Variable(v.into())),
						Token::Integer(i) => args.push(Argument::Integer(i)),
						t => todo!("parse {:?}", t),
					}
				}
				ops.push(Op::Call {
					function: f.into(),
					arguments: args.into(),
				});
			}
			Token::String(s) => {
				if next_is_close {
					// TODO unescape string
					ops.push(Op::Return {
						statement: Argument::String(s.into()),
					})
				}
			}
			Token::Variable(s) => {
				if next_is_close {
					ops.push(Op::Return {
						statement: Argument::Variable(s.into()),
					})
				}
			}
			Token::Integer(s) => {
				if next_is_close {
					ops.push(Op::Return {
						statement: Argument::Integer(s),
					})
				}
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
					Argument::String("Hello".into()),
					Argument::String("world!".into()),
				]
				.into(),
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
					arguments: [Argument::String("Hello".into()),].into(),
				},
				Op::Call {
					function: "print".into(),
					arguments: [Argument::String("world!".into()),].into(),
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
				condition: [Op::Call {
					function: "some_cond".into(),
					arguments: [].into(),
				},]
				.into(),
				if_true: [Op::Call {
					function: "print".into(),
					arguments: [
						Argument::String("it".into()),
						Argument::String("is".into()),
						Argument::String("true".into()),
					]
					.into(),
				},]
				.into(),
				if_false: [].into(),
			}]
		);
	}
}
