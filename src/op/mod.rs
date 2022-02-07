mod function;
mod op;
mod parse;

pub use function::Function;
pub use op::Op;
pub use parse::ParseError;

use crate::token::Token;
use bitflags::bitflags;
use core::iter::Peekable;
use std::collections::BTreeMap;

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

/// An AST
pub struct OpTree<'a> {
	/// The "opcode" tree.
	pub ops: Box<[Op<'a>]>,
	/// A list of registers to their corresponding variables.
	///
	/// There may be multiple registers per variable.
	pub registers: Box<[Register<'a>]>,
	/// All functions found in the script.
	pub functions: BTreeMap<&'a str, Function<'a>>,
}

impl<'a> OpTree<'a> {
	/// Convert an iterator of tokens to an [`OpTree`].
	#[inline(always)]
	pub fn new(mut tokens: impl Iterator<Item = Token<'a>>) -> Result<Self, ParseError> {
		parse::Parser::parse_script(&mut tokens.peekable())
			.map(|p| Self {
				ops: p.ops,
				registers: p.registers.into(),
				functions: p.functions.unwrap(),
			})
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
			&*parse("print Hello world!").ops,
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
			&*parse("print Hello; print world!").ops,
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
			&*parse("if some_cond; print it is true").ops,
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
			&*t.ops,
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
			&*t.ops,
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
			&*parse("while true; print y").ops,
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
			&*t.ops,
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
			&*t.ops,
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
				pipe_in: [].into(),
				pipe_out: [].into(),
				ops: [Op::Call {
					function: "bar",
					arguments: [].into(),
					pipe_in: [].into(),
					pipe_out: [].into(),
				}]
				.into(),
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
				pipe_in: [].into(),
				pipe_out: [].into(),
				ops: [Op::Call {
					function: "bar",
					arguments: [].into(),
					pipe_in: [].into(),
					pipe_out: [].into(),
				}]
				.into(),
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
				]
				.into(),
			}
		);
	}

	#[test]
	fn function_wrong_arg() {
		let t = parse("fn foo x; bar @y");
		assert_eq!(
			t.functions["foo"],
			Function {
				arguments: ["x"].into(),
				pipe_in: [].into(),
				pipe_out: [].into(),
				ops: [Op::Call {
					function: "bar",
					arguments: [Expression::Variable(RegisterIndex(1)),].into(),
					pipe_in: [].into(),
					pipe_out: [].into(),
				}]
				.into(),
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
				]
				.into(),
			}
		);
	}

	#[test]
	fn function_pipe_out() {
		let t = parse("fn foo x >y; bar @x >y");
		assert_eq!(
			t.functions["foo"],
			Function {
				arguments: ["x"].into(),
				pipe_in: [].into(),
				pipe_out: ["y"].into(),
				ops: [Op::Call {
					function: "bar",
					arguments: [Expression::Variable(RegisterIndex(0)),].into(),
					pipe_in: [].into(),
					pipe_out: [("", RegisterIndex(1))].into(),
				}]
				.into(),
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
				]
				.into(),
			}
		);
		// arguments > pipe out > pipe in, hence these should be equivalent
		assert_eq!(
			t.functions["foo"],
			parse("fn foo >y x; bar @x >y").functions["foo"]
		);
	}

	#[test]
	fn function_pipe_out_unused() {
		let t = parse("fn foo x >y; bar @x");
		assert_eq!(
			t.functions["foo"],
			Function {
				arguments: ["x"].into(),
				pipe_in: [].into(),
				pipe_out: ["y"].into(),
				ops: [Op::Call {
					function: "bar",
					arguments: [Expression::Variable(RegisterIndex(0)),].into(),
					pipe_in: [].into(),
					pipe_out: [].into(),
				}]
				.into(),
				registers: [Register {
					variable: "x",
					constant: false,
					types: Types::ALL,
				},]
				.into(),
			}
		);
	}

	#[test]
	fn function_pipe_in() {
		let t = parse("fn foo x <y; bar @x <y");
		assert_eq!(
			t.functions["foo"],
			Function {
				arguments: ["x"].into(),
				pipe_in: ["y"].into(),
				pipe_out: [].into(),
				ops: [Op::Call {
					function: "bar",
					arguments: [Expression::Variable(RegisterIndex(0)),].into(),
					pipe_in: [(RegisterIndex(1), "")].into(),
					pipe_out: [].into(),
				}]
				.into(),
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
				]
				.into(),
			}
		);
		// arguments > pipe out > pipe in, hence these should be equivalent
		assert_eq!(
			t.functions["foo"],
			parse("fn foo <y x; bar @x <y").functions["foo"]
		);
	}

	#[test]
	fn function_pipe_in_out() {
		let t = parse("fn foo x <y >z; bar @x <y >z");
		assert_eq!(
			t.functions["foo"],
			Function {
				arguments: ["x"].into(),
				pipe_in: ["y"].into(),
				pipe_out: ["z"].into(),
				ops: [Op::Call {
					function: "bar",
					arguments: [Expression::Variable(RegisterIndex(0)),].into(),
					pipe_in: [(RegisterIndex(1), "")].into(),
					pipe_out: [("", RegisterIndex(2))].into(),
				}]
				.into(),
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
					Register {
						variable: "z",
						constant: false,
						types: Types::ALL,
					},
				]
				.into(),
			}
		);
		// arguments > pipe out > pipe in, hence these should be equivalent
		assert_eq!(
			t.functions["foo"],
			parse("fn foo >z <y x; bar @x <y >z").functions["foo"]
		);
	}
}
