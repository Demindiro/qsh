use super::{Expression, RegisterIndex, ForRange};

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
