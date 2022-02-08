use super::*;
use crate::runtime::{QFunction, FFI_EXEC, FFI_PRINT};
use crate::token::TokenParser;

/// Custom resolve_fn so adding or removing functions doesn't break anything.
fn resolve_fn(f: &str) -> Option<QFunction> {
	match f {
		"exec" => Some(FFI_EXEC),
		"print" => Some(FFI_PRINT),
		_ => None,
	}
}

fn parse(s: &str) -> OpTree<'_> {
	OpTree::new(TokenParser::new(s).map(Result::unwrap), resolve_fn).unwrap()
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
		[Op::CallBuiltin {
			function: FFI_PRINT,
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
			Op::CallBuiltin {
				function: FFI_PRINT,
				arguments: [Expression::String("Hello".into()),].into(),
				pipe_out: [].into(),
				pipe_in: [].into(),
			},
			Op::CallBuiltin {
				function: FFI_PRINT,
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
				[Op::Exec {
					arguments: [Expression::String("some_cond".into())].into(),
					pipe_out: [].into(),
					pipe_in: [].into(),
				},]
				.into()
			),
			if_true: [Op::CallBuiltin {
				function: FFI_PRINT,
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
			Op::CallBuiltin {
				function: FFI_PRINT,
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
					[Op::Exec {
						arguments: [
							Expression::String("test".into()),
							Expression::String("-n".into()),
							Expression::Variable(v_a),
						]
						.into(),
						pipe_in: [].into(),
						pipe_out: [].into(),
					},]
					.into()
				),
				if_true: [Op::CallBuiltin {
					function: FFI_PRINT,
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
				[Op::Exec {
					arguments: [Expression::String("true".into())].into(),
					pipe_in: [].into(),
					pipe_out: [].into()
				}]
				.into()
			),
			while_true: [Op::CallBuiltin {
				function: FFI_PRINT,
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
				[Op::Exec {
					arguments: [Expression::String("true".into())].into(),
					pipe_in: [].into(),
					pipe_out: [].into()
				}]
				.into()
			),
			if_true: [
				Op::CallBuiltin {
					function: FFI_PRINT,
					arguments: [Expression::String("x".into())].into(),
					pipe_in: [].into(),
					pipe_out: [].into(),
				},
				Op::CallBuiltin {
					function: FFI_PRINT,
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
			Op::CallBuiltin {
				function: FFI_PRINT,
				arguments: [Expression::String("abc".into())].into(),
				pipe_in: [].into(),
				pipe_out: [("", v_)].into(),
			},
			Op::CallBuiltin {
				function: FFI_PRINT,
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
			ops: [Op::Exec {
				arguments: [Expression::String("bar".into())].into(),
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
			ops: [Op::Exec {
				arguments: [Expression::String("bar".into())].into(),
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
			ops: [Op::Exec {
				arguments: [
					Expression::String("bar".into()),
					Expression::Variable(RegisterIndex(1)),
				]
				.into(),
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
			ops: [Op::Exec {
				arguments: [
					Expression::String("bar".into()),
					Expression::Variable(RegisterIndex(0)),
				]
				.into(),
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
			ops: [Op::Exec {
				arguments: [
					Expression::String("bar".into()),
					Expression::Variable(RegisterIndex(0)),
				]
				.into(),
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
			ops: [Op::Exec {
				arguments: [
					Expression::String("bar".into()),
					Expression::Variable(RegisterIndex(0)),
				]
				.into(),
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
			ops: [Op::Exec {
				arguments: [
					Expression::String("bar".into()),
					Expression::Variable(RegisterIndex(0)),
				]
				.into(),
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
