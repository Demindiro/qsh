mod function;
mod op;
mod parse;
#[cfg(test)]
mod test;

pub use function::Function;
pub use op::Op;
pub use parse::ParseError;

use crate::runtime::QFunction;
use crate::token::Token;
use bitflags::bitflags;
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
	pub fn new<I, F>(tokens: I, resolve_fn: F) -> Result<Self, ParseError>
	where
		I: Iterator<Item = Token<'a>>,
		F: Fn(&str) -> Option<QFunction>,
	{
		parse::Parser::parse_script(&mut tokens.peekable(), &resolve_fn).map(|(ops, p)| Self {
			ops,
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
