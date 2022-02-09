use super::{Op, Register};

/// A `qsh` function defined with `fn`.
#[derive(Clone, Debug, PartialEq)]
pub struct Function<'a> {
	pub arguments: Box<[&'a str]>,
	pub pipe_in: Box<[&'a str]>,
	pub pipe_out: Box<[&'a str]>,
	pub ops: Box<[Op<'a>]>,
	/// A list of registers to their corresponding variables.
	///
	/// The first few correspond with the arguments.
	///
	/// There may be multiple registers per variable.
	pub registers: Box<[Register<'a>]>,
}
