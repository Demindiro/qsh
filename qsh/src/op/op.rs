use super::{Expression, ForRange, RegisterIndex};
use crate::runtime::QFunction;

#[derive(PartialEq, Debug)]
pub enum Op<'a> {
	/// A generic call. This refers osepy to user-defined functions if [`Parser::reduce`] has been
	/// applied.
	Call {
		function: &'a str,
		arguments: Box<[Expression<'a>]>,
		pipe_out: Box<[(&'a str, RegisterIndex)]>,
		pipe_in: Box<[(RegisterIndex, &'a str)]>,
	},
	/// Execute a program.
	Exec {
		arguments: Box<[Expression<'a>]>,
		pipe_out: Box<[(&'a str, RegisterIndex)]>,
		pipe_in: Box<[(RegisterIndex, &'a str)]>,
	},
	/// Call a built-in function.
	CallBuiltin {
		function: QFunction,
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
