mod reduce;
mod validate;

use super::{Expression, ForRange, Function, Op, Register, RegisterIndex, Types};
use crate::runtime::QFunction;
use crate::token::Token;
use core::fmt;
use core::iter::Peekable;
use core::mem;
use std::collections::BTreeMap;

/// A token to AST converter.
#[derive(Debug)]
pub(super) struct Parser<'a, F>
where
	F: (Fn(&str) -> Option<QFunction>) + Clone,
{
	/// A list of registers to their corresponding variables.
	///
	/// There may be multiple registers per variable.
	pub registers: Vec<Register<'a>>,
	/// All functions found in the script.
	///
	/// If this is `None`, no new function may be defined.
	pub functions: Option<BTreeMap<&'a str, Function<'a>>>,
	/// How many layers of loops we are in.
	loop_depth: usize,
	/// Built-in function resolver.
	resolve_fn: F,
}

impl<'a, F> Parser<'a, F>
where
	F: (Fn(&str) -> Option<QFunction>) + Clone,
{
	/// Convert a series of tokens in a script.
	pub fn parse_script<I>(
		tokens: &mut Peekable<I>,
		registers: Vec<Register<'a>>,
		resolve_fn: F,
	) -> Result<(Box<[Op<'a>]>, Self), ParseError>
	where
		I: Iterator<Item = Token<'a>>,
	{
		let mut s = Self {
			registers,
			functions: Some(Default::default()),
			loop_depth: 0,
			resolve_fn,
		};
		let ops = s
			.parse_inner(Default::default(), &mut tokens.peekable(), false)?
			.into();
		assert!(
			u16::try_from(s.registers.len()).is_ok(),
			"too many registers used"
		);
		let ops = s.reduce(ops);
		// TODO horribly inefficient
		for name in s
			.functions
			.as_ref()
			.unwrap()
			.keys()
			.copied()
			.collect::<Vec<_>>()
		{
			let ops = mem::take(&mut s.functions.as_mut().unwrap().get_mut(name).unwrap().ops);
			let ops = s.reduce(ops);
			s.functions.as_mut().unwrap().get_mut(name).unwrap().ops = ops;
		}
		s.validate(&*ops).map(|()| (ops, s))
	}

	/// Convert tokens that describe function. This *excludes* the `fn` keyword.
	///
	/// This function does *not* apply reduce or perform validation.
	pub fn parse_function<I>(
		tokens: &mut Peekable<I>,
		resolve_fn: F,
	) -> Result<(&'a str, Function<'a>), ParseError>
	where
		I: Iterator<Item = Token<'a>>,
	{
		let name = match tokens.next() {
			Some(Token::Word(n)) => n,
			_ => return Err(ParseError::ExpectedFunctionName),
		};

		// Collect arguments
		let mut args = Vec::new();
		let mut pipe_in = Vec::new();
		let mut pipe_out = Vec::new();
		loop {
			let tk = tokens.next().expect("no token (bug in token parser?)");
			match tk {
				Token::Word(arg) => args.push(arg),
				Token::PipeIn { from, to: "" } => pipe_in.push(from),
				Token::PipeOut { from: "", to } => pipe_out.push(to),
				Token::Separator => break,
				Token::PipeIn { .. } => return Err(ParseError::UnexpectedPipeFrom),
				Token::PipeOut { .. } => return Err(ParseError::UnexpectedPipeTo),
				_ => return Err(ParseError::UnexpectedToken),
			}
		}

		// Don't allocate for pipe_out as those default to nil in all cases.
		let registers = args
			.iter()
			.chain(&*pipe_in)
			.map(|&variable| Register {
				variable: variable.into(),
				constant: false,
				types: Types::ALL,
			})
			.collect();
		// Create new tree for function (with separate variables etc).
		let mut func = Parser {
			registers,
			functions: Default::default(),
			loop_depth: 0,
			resolve_fn,
		};
		// Parse function body
		let ops = match func.parse_statement(tokens)? {
			Expression::Statement(ops) => ops,
			Expression::Integer(_) | Expression::String(_) | Expression::Variable(_) => [].into(),
		};
		let func = Function {
			arguments: args.into(),
			pipe_in: pipe_in.into(),
			pipe_out: pipe_out.into(),
			ops,
			registers: func.registers.into(),
		};
		Ok((name, func))
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
			if_true: match self.parse_statement(tokens)? {
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
					for_each: match self.parse_statement(tokens)? {
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
			while_true: match self.parse_statement(tokens)? {
				Expression::Statement(c) => c,
				_ => [].into(), // TODO
			},
		};
		self.loop_depth -= 1;
		Ok(op)
	}

	/// Parse a call, e.g. `echo @x >y`
	fn parse_call<I>(&mut self, function: &'a str, tokens: &mut I) -> Result<Op<'a>, ParseError>
	where
		I: Iterator<Item = Token<'a>>,
	{
		let mut args = Vec::new();
		let mut pipe_out = Vec::new();
		let mut pipe_in = Vec::new();
		while let Some(tk) = tokens.next() {
			match tk {
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
				Token::PipeOut { from, to } => pipe_out.push((from, self.alloc_register(to, true))),
				Token::PipeIn { from, to } => pipe_in.push((self.alloc_register(from, false), to)),
				Token::Separator => break,
				Token::Function => todo!("convert 'fn' to string arg"),
			}
		}
		Ok(Op::Call {
			function,
			arguments: args.into(),
			pipe_out: pipe_out.into(),
			pipe_in: pipe_in.into(),
		})
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
			Token::Word(f) => Ok(Expression::Statement([self.parse_call(f, tokens)?].into())),
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

	/// Parse a "statement" in a function, i.e. `fn foo; <stmt>`, `if true; <stmt>`, ..
	fn parse_statement<I>(&mut self, tokens: &mut Peekable<I>) -> Result<Expression<'a>, ParseError>
	where
		I: Iterator<Item = Token<'a>>,
	{
		match tokens.peek() {
			// parse_expr doesn't allow assignments, so handle it manually
			Some(&Token::Variable(s)) => {
				tokens.next().unwrap();
				match tokens.next().expect("expected token") {
					Token::Separator => Ok(Expression::Variable(
						self.alloc_register(s, self.inside_loop()),
					)),
					Token::Word("=") => Ok(Expression::Statement(
						[Op::Assign {
							variable: self.alloc_register(s, self.inside_loop()),
							expression: self.parse_expr(tokens)?,
						}]
						.into(),
					)),
					t => todo!("parse {:?}", t),
				}
			}
			_ => self.parse_expr(tokens),
		}
	}

	fn parse_inner(
		&mut self,
		mut ops: Vec<Op<'a>>,
		tokens: &mut Peekable<impl Iterator<Item = Token<'a>>>,
		in_scope: bool,
	) -> Result<Vec<Op<'a>>, ParseError> {
		while let Some(tk) = tokens.next() {
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
				Token::Word(f) => ops.push(self.parse_call(f, tokens)?),
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
					let f = self
						.functions
						.as_mut()
						.ok_or(ParseError::CantNestFunctions)?;
					let (name, func) = Self::parse_function(tokens, self.resolve_fn.clone())?;
					f.try_insert(name, func)
						.map_err(|_| ParseError::FunctionAlreadyDefined)?;
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
		if let Some((i, _)) = (!overwrite || !self.inside_loop())
			.then(|| {
				self.registers
					.iter()
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
				variable: var.into(),
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

#[derive(Debug)]
pub enum ParseError {
	CloseBlockWithoutOpen,
	UnclosedBlock,
	ExpectedVariable,
	ExpectedIn,
	ExpectedFunctionName,
	UnexpectedPipeFrom,
	UnexpectedPipeTo,
	UnexpectedToken,
	CantNestFunctions,
	FunctionAlreadyDefined,
	ArgumentMismatch,
	PipeInMismatch,
	PipeOutMismatch,
}

impl fmt::Display for ParseError {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		match self {
			Self::CloseBlockWithoutOpen => "')' without '('",
			Self::UnclosedBlock => "'(' without ')'",
			Self::ExpectedVariable => "expected variable",
			Self::ExpectedIn => "expected 'in'",
			Self::UnexpectedPipeFrom => "unexpected '>'",
			Self::UnexpectedPipeTo => "unexpected '<'",
			_ => todo!(),
		}
		.fmt(f)
	}
}

impl std::error::Error for ParseError {}
