use crate::token::Token;
use bitflags::bitflags;
use core::iter::Peekable;
use std::collections::BTreeMap;

#[derive(Debug, PartialEq)]
pub enum Op<'a> {
	Call {
		function: &'a str,
		arguments: Box<[Expression<'a>]>,
		pipe_out: Box<[(&'a str, RegisterIndex)]>,
		pipe_in: Box<[(RegisterIndex, &'a str)]>,
	},
	If {
		condition: Expression<'a>,
		if_true: Box<[Self]>,
		if_false: Box<[Self]>,
	},
	While {
		condition: Expression<'a>,
		while_true: Box<[Self]>,
	},
	For {
		variable: RegisterIndex,
		range: ForRange,
		for_each: Box<[Self]>,
	},
	Assign {
		variable: RegisterIndex,
		expression: Expression<'a>,
	},
}

#[derive(Debug, PartialEq)]
pub enum Expression<'a> {
	String(Box<str>),
	Variable(RegisterIndex),
	Integer(isize),
	Statement(Box<[Op<'a>]>),
}

#[derive(Debug, PartialEq)]
pub enum ForRange {
	Variable(RegisterIndex),
}

/// A `qsh` function defined with `fn`.
#[derive(Debug, PartialEq)]
pub struct Function<'a> {
	pub arguments: Box<[&'a str]>,
	pub ops: Box<[Op<'a>]>,
	/// A list of registers to their corresponding variables.
	///
	/// The first few correspond with the arguments.
	///
	/// There may be multiple registers per variable.
	pub registers: Box<[Register<'a>]>,
}

/// An AST.
#[derive(Debug)]
pub struct OpTree<'a> {
	/// The "opcode" tree.
	pub ops: Box<[Op<'a>]>,
	/// A list of registers to their corresponding variables.
	///
	/// There may be multiple registers per variable.
	pub registers: Vec<Register<'a>>,
	/// All functions found in the script.
	pub functions: BTreeMap<&'a str, Function<'a>>,
	/// How many layers of loops we are in.
	loop_depth: usize,
}

impl<'a> OpTree<'a> {
	/// Convert a series of tokens.
	pub fn new(mut tokens: impl Iterator<Item = Token<'a>>) -> Result<Self, ParseError> {
		let mut s = Self {
			ops: Default::default(),
			registers: Default::default(),
			functions: Default::default(),
			loop_depth: 0,
		};
		s.ops = s
			.parse_inner(Default::default(), &mut tokens.peekable(), false)?
			.into();
		assert!(
			u16::try_from(s.registers.len()).is_ok(),
			"too many registers used"
		);
		Ok(s)
	}

	/// Get the root of the opcode tree.
	pub fn root(&self) -> &[Op<'a>] {
		&self.ops
	}

	/// Get all registers that correspond to a variable
	pub fn variable_registers<'b>(
		&'b self,
		variable: &'b str,
	) -> impl Iterator<Item = (RegisterIndex, Register<'a>)> + 'b {
		self.registers
			.iter()
			.copied()
			.enumerate()
			.filter(move |(_, r)| r.variable == variable)
			.map(|(i, r)| (RegisterIndex(i as u16), r))
	}

	/// Parse an argument, i.e. `print <arg> <arg> ...`
	fn parse_arg<I>(&mut self, tokens: &mut Peekable<I>) -> Result<Expression<'a>, ParseError>
	where
		I: Iterator<Item = Token<'a>>,
	{
		match tokens.next().unwrap() {
			Token::BlockOpen => todo!("scope open"),
			Token::BlockClose => todo!("scope close"),
			Token::Word(s) => Ok(Expression::String(s.into())),
			Token::String(s) => {
				// TODO unescape
				Ok(Expression::String(s.into()))
			}
			Token::Variable(v) => Ok(Expression::Variable(self.alloc_register(v, false))),
			Token::Integer(i) => Ok(Expression::Integer(i)),
			t => todo!("parse {:?}", t),
		}
	}

	/// Parse an `if` expression.
	fn parse_if<I>(&mut self, tokens: &mut Peekable<I>) -> Result<Op<'a>, ParseError>
	where
		I: Iterator<Item = Token<'a>>,
	{
		Ok(Op::If {
			condition: self.parse_expr(tokens)?,
			if_true: match self.parse_expr(tokens)? {
				Expression::Statement(c) => c,
				_ => [].into(), // TODO
			},
			if_false: [].into(), // TODO
		})
	}

	/// Parse a `for` expression.
	fn parse_for<I>(&mut self, tokens: &mut Peekable<I>) -> Result<Op<'a>, ParseError>
	where
		I: Iterator<Item = Token<'a>>,
	{
		self.loop_depth += 1;
		let ret = if let Some(Token::Word(variable)) = tokens.next() {
			if tokens.next() != Some(Token::Word("in")) {
				Err(ParseError::ExpectedIn)
			} else {
				let range = match self.parse_expr(tokens)? {
					Expression::Variable(v) => ForRange::Variable(v),
					t => todo!("{:?} range in for loop", t),
				};
				Ok(Op::For {
					variable: self.alloc_register(variable, true),
					range,
					for_each: match self.parse_expr(tokens)? {
						Expression::Statement(v) => v,
						t => todo!("{:?} for_each in for loop", t),
					},
				})
			}
		} else {
			Err(ParseError::ExpectedVariable)
		};
		self.loop_depth -= 1;
		ret
	}

	/// Parse a `while` expression.
	fn parse_while<I>(&mut self, tokens: &mut Peekable<I>) -> Result<Op<'a>, ParseError>
	where
		I: Iterator<Item = Token<'a>>,
	{
		self.loop_depth += 1;
		let op = Op::While {
			condition: self.parse_expr(tokens)?,
			while_true: match self.parse_expr(tokens)? {
				Expression::Statement(c) => c,
				_ => [].into(), // TODO
			},
		};
		self.loop_depth -= 1;
		Ok(op)
	}

	/// Parse an "expression", i.e. `if <expr>`, `for v in <expr>`, ..
	fn parse_expr<I>(&mut self, tokens: &mut Peekable<I>) -> Result<Expression<'a>, ParseError>
	where
		I: Iterator<Item = Token<'a>>,
	{
		match tokens.next().expect("todo") {
			Token::BlockOpen => Ok(Expression::Statement(
				self.parse_inner(Default::default(), tokens, true)?.into(),
			)),
			Token::BlockClose => todo!("scope close"),
			Token::Word("if") => Ok(Expression::Statement([self.parse_if(tokens)?].into())),
			Token::Word("for") => Ok(Expression::Statement([self.parse_for(tokens)?].into())),
			Token::Word("while") => Ok(Expression::Statement([self.parse_while(tokens)?].into())),
			Token::Word(f) => {
				let mut args = Vec::new();
				while let Some(tk) = tokens.peek() {
					if tk == &Token::Separator {
						tokens.next().unwrap();
						break;
					}
					args.push(self.parse_arg(tokens)?);
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
				let s = self.alloc_register(s, false);
				Ok(Expression::Variable(s))
			}
			Token::Integer(s) => Ok(Expression::Integer(s)),
			Token::Separator => todo!("unexpected separator (should we allow this?)"),
			t => todo!("parse {:?}", t),
		}
	}

	fn parse_inner(
		&mut self,
		mut ops: Vec<Op<'a>>,
		tokens: &mut Peekable<impl Iterator<Item = Token<'a>>>,
		in_scope: bool,
	) -> Result<Vec<Op<'a>>, ParseError> {
		while let Some(tk) = tokens.next() {
			let next_is_close = tokens.peek().map_or(true, |t| t == &Token::BlockClose);
			match tk {
				Token::BlockOpen => ops = self.parse_inner(ops, tokens, true)?,
				Token::BlockClose => {
					return in_scope
						.then(|| ops.into())
						.ok_or(ParseError::CloseBlockWithoutOpen);
				}
				Token::Word("if") => ops.push(self.parse_if(tokens)?),
				Token::Word("for") => ops.push(self.parse_for(tokens)?),
				Token::Word("while") => ops.push(self.parse_while(tokens)?),
				Token::Word(f) => {
					let mut args = Vec::new();
					let mut pipe_out = Vec::new();
					let mut pipe_in = Vec::new();
					while tokens.peek().map_or(false, |t| t != &Token::Separator) {
						match tokens.next().unwrap() {
							Token::BlockOpen => todo!("scope open"),
							Token::BlockClose => todo!("scope close"),
							Token::Word(s) => args.push(Expression::String(s.into())),
							Token::String(s) => {
								// TODO unescape
								args.push(Expression::String(s.into()))
							}
							Token::Variable(v) => {
								let v = self.alloc_register(v, false);
								args.push(Expression::Variable(v))
							}
							Token::Integer(i) => args.push(Expression::Integer(i)),
							Token::PipeOut { from, to } => {
								pipe_out.push((from, self.alloc_register(to, true)))
							}
							Token::PipeIn { from, to } => {
								pipe_in.push((self.alloc_register(from, false), to))
							}
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
						variable: self.alloc_register(s, true),
						// TODO parse_expr would be a better fit
						expression: self.parse_arg(tokens)?,
					})
				}
				Token::Variable(_) | Token::String(_) | Token::Integer(_) => {
					// TODO add warning for redundant integer
				}
				Token::Separator => {}
				Token::Function => {
					if let Some(Token::Word(name)) = tokens.next() {
						// Collect arguments
						let mut args = Vec::new();
						let mut registers = Vec::new();
						while let tk = tokens.next() {
							match tk {
								Some(Token::Word(arg)) => {
									args.push(arg);
									registers.push(Register {
										variable: arg,
										constant: false,
										types: Types::ALL,
									});
								}
								Some(Token::Separator) => break,
								_ => todo!(),
							}
						}
						// Create new tree for function (with separate variables etc).
						let mut func = OpTree {
							ops: Default::default(),
							registers,
							functions: Default::default(),
							loop_depth: 0,
						};
						// Parse function body
						match func.parse_expr(tokens)? {
							Expression::Statement(ops) => func.ops = ops,
							Expression::Integer(_) | Expression::String(_) | Expression::Variable(_) => (),
						}
						self.functions.try_insert(name, Function {
							arguments: args.into(),
							ops: func.ops,
							registers: func.registers.into(),
						}).expect("todo");
					} else {
						todo!();
					}
				}
				t => todo!("parse {:?}", t),
			}
		}
		(!in_scope)
			.then(|| ops.into())
			.ok_or(ParseError::UnclosedBlock)
	}

	/// Allocate or get an existing register.
	fn alloc_register(&mut self, var: &'a str, overwrite: bool) -> RegisterIndex {
		if let Some((i, r)) = (!overwrite || !self.inside_loop())
			.then(|| {
				self.registers
					.iter_mut()
					.enumerate()
					.rev()
					.find(|(_, r)| r.variable == var)
			})
			.flatten()
		{
			// Register overflow checks are deferred until the end.
			RegisterIndex(i as u16)
		} else {
			let i = self.registers.len();
			self.registers.push(Register {
				variable: var,
				constant: false,
				types: Types::ALL,
			});
			// Ditto
			RegisterIndex(i as u16)
		}
	}

	/// Whether we're inside a `for` or `while` loop.
	fn inside_loop(&self) -> bool {
		self.loop_depth > 0
	}
}

/// A virtual register.
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct Register<'a> {
	/// The variable this register corresponds to.
	pub variable: &'a str,
	/// Whether this register is constant, i.e. the value in this register is set only once
	/// and is known at compile time.
	pub constant: bool,
	/// The types of variable this registers can hold.
	pub types: Types,
}

bitflags! {
	pub struct Types: u8 {
		const NIL = 1 << 0;
		const STRING = 1 << 1;
		const INTEGER = 1 << 2;
		const PIPE = 1 << 3;
		const ARRAY = 1 << 4;
		const ALL = 0xff;
	}
}

/// The index / ID of a register.
// 65536 ought to be quite enough.
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct RegisterIndex(pub(crate) u16);

#[derive(Debug)]
pub enum ParseError {
	CloseBlockWithoutOpen,
	UnclosedBlock,
	ExpectedVariable,
	ExpectedIn,
}

#[cfg(test)]
mod test {
	use super::*;
	use crate::token::TokenParser;

	fn parse(s: &str) -> OpTree<'_> {
		OpTree::new(TokenParser::new(s).map(Result::unwrap)).unwrap()
	}

	/// Get exactly one register for a variable.
	#[track_caller]
	fn reg_1<'a>(tp: &OpTree<'a>, var: &str) -> (RegisterIndex, Register<'a>) {
		let mut it = tp.variable_registers(var);
		let r = it.next().expect("no registers for variable");
		assert!(
			it.next().is_none(),
			"multiple registers for variable \"{}\"",
			var
		);
		r
	}

	#[test]
	fn print() {
		assert_eq!(
			parse("print Hello world!").root(),
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
		assert_eq!(
			parse("print Hello; print world!").root(),
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
		assert_eq!(
			parse("if some_cond; print it is true").root(),
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
		let t = parse("@a = $5; @b = \"five\"; print @a is pronounced as @b");
		let (a, _) = reg_1(&t, "a");
		let (b, _) = reg_1(&t, "b");
		assert_eq!(
			t.root(),
			[
				Op::Assign {
					variable: a,
					expression: Expression::Integer(5),
				},
				Op::Assign {
					variable: b,
					expression: Expression::String("five".into()),
				},
				Op::Call {
					function: "print".into(),
					arguments: [
						Expression::Variable(a),
						Expression::String("is".into()),
						Expression::String("pronounced".into()),
						Expression::String("as".into()),
						Expression::Variable(b),
					]
					.into(),
					pipe_out: [].into(),
					pipe_in: [].into(),
				},
			]
		);
	}

	#[test]
	fn for_loop() {
		let t = parse("for a in @; if test -n @a; print @a");
		let (v_, _) = reg_1(&t, "");
		let (v_a, _) = reg_1(&t, "a");
		assert_eq!(
			t.root(),
			[Op::For {
				variable: v_a,
				range: ForRange::Variable(v_),
				for_each: [Op::If {
					condition: Expression::Statement(
						[Op::Call {
							function: "test",
							arguments:
								[Expression::String("-n".into()), Expression::Variable(v_a),].into(),
							pipe_in: [].into(),
							pipe_out: [].into(),
						},]
						.into()
					),
					if_true: [Op::Call {
						function: "print",
						arguments: [Expression::Variable(v_a)].into(),
						pipe_in: [].into(),
						pipe_out: [].into(),
					},]
					.into(),
					if_false: [].into(),
				}]
				.into(),
			},]
		);
	}

	#[test]
	fn while_loop() {
		assert_eq!(
			parse("while true; print y").root(),
			[Op::While {
				condition: Expression::Statement(
					[Op::Call {
						function: "true",
						arguments: [].into(),
						pipe_in: [].into(),
						pipe_out: [].into()
					}]
					.into()
				),
				while_true: [Op::Call {
					function: "print",
					arguments: [Expression::String("y".into())].into(),
					pipe_in: [].into(),
					pipe_out: [].into(),
				},]
				.into(),
			},]
		);
	}

	#[test]
	fn block() {
		let t = parse("if true; (print x; print @y)");
		let (y, _) = reg_1(&t, "y");
		assert_eq!(
			t.root(),
			[Op::If {
				condition: Expression::Statement(
					[Op::Call {
						function: "true",
						arguments: [].into(),
						pipe_in: [].into(),
						pipe_out: [].into()
					}]
					.into()
				),
				if_true: [
					Op::Call {
						function: "print",
						arguments: [Expression::String("x".into())].into(),
						pipe_in: [].into(),
						pipe_out: [].into(),
					},
					Op::Call {
						function: "print",
						arguments: [Expression::Variable(y)].into(),
						pipe_in: [].into(),
						pipe_out: [].into(),
					},
				]
				.into(),
				if_false: [].into(),
			},]
		);
	}

	#[test]
	fn print_pipe_print() {
		let t = parse("print abc > ; print @");
		let (v_, _) = reg_1(&t, "");
		assert_eq!(
			t.root(),
			[
				Op::Call {
					function: "print",
					arguments: [Expression::String("abc".into())].into(),
					pipe_in: [].into(),
					pipe_out: [("", v_)].into(),
				},
				Op::Call {
					function: "print",
					arguments: [Expression::Variable(v_)].into(),
					pipe_in: [].into(),
					pipe_out: [].into(),
				},
			]
		);
	}

	#[test]
	fn function() {
		let t = parse("fn foo; bar");
		assert_eq!(
			t.functions["foo"],
			Function {
				arguments: [].into(),
				ops: [Op::Call {
					function: "bar",
					arguments: [].into(),
					pipe_in: [].into(),
					pipe_out: [].into(),
				}].into(),
				registers: [].into(),
			}
		);
	}

	#[test]
	fn function_args() {
		let t = parse("fn foo x y; bar");
		assert_eq!(
			t.functions["foo"],
			Function {
				arguments: ["x", "y"].into(),
				ops: [Op::Call {
					function: "bar",
					arguments: [].into(),
					pipe_in: [].into(),
					pipe_out: [].into(),
				}].into(),
				registers: [
					Register {
						variable: "x",
						constant: false,
						types: Types::ALL,
					},
					Register {
						variable: "y",
						constant: false,
						types: Types::ALL,
					},
				].into(),
			}
		);
	}
}
