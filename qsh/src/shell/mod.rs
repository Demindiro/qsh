//! Utilities for creating interactive shells.

use crate::jit;
use crate::op::{Op, OpTreeParser, Register};
use crate::runtime::{QFunction, Value};
use crate::token::{Token, TokenParser};
use core::mem::{self, MaybeUninit};
use std::error::Error;

/// An fixed-size stack with proper alignment.
#[cfg_attr(target_arch = "x86_64", repr(align(16)))]
struct Stack([MaybeUninit<u8>; 1 << 16]);

impl Default for Stack {
	fn default() -> Self {
		Self(MaybeUninit::uninit_array())
	}
}

/// An interactive shell.
///
/// Code is continuously fed with [`Shell::evaluate`]. It is parsed & executed as soon
/// as a valid expression is formed. Results & errors can be retrieved with [`Shell::poll`].
///
/// New variables are stored permanently on the stack & can be used by any commands after the
/// declaration of those variables.
pub struct Shell {
	/// Stack used for storing variables & executing commands.
	stack: Stack,
	/// The last status code returned by a call. Defaults to 0.
	status: isize,
	/// The currently defined variables / virtual registers.
	registers: Vec<Register<'static>>,
}

impl Shell {
	/// Feed a string of code, parsing & executing it if it is complete.
	pub fn evaluate<F>(&mut self, code: &str, resolve_fn: F) -> Result<isize, Box<dyn Error>>
	where
		F: Fn(&str) -> Option<QFunction> + Copy,
	{
		let old_registers_len = self.registers.len();

		// Generate tokens
		let mut tokens = Vec::new();
		TokenParser::new(code).try_for_each(|t| t.map(|t| tokens.push(t)))?;

		// Generate op tree with already defined variables
		let ops = OpTreeParser::new(resolve_fn)
			.with_registers(mem::take(&mut self.registers))
			.parse(tokens.into_iter())?;

		// Generate function
		self.registers = ops
			.registers
			.iter()
			.cloned()
			.map(|t| t.into_owned())
			.collect();
		let func = jit::compile(ops, resolve_fn);

		// Move virtual registers on stack up.
		let reg_size = mem::size_of::<Value>();
		let stack_size = self.stack.0.len();
		let old_range = stack_size - old_registers_len * reg_size..stack_size;
		let new_range = stack_size - self.registers.len() * reg_size..stack_size;
		self.stack.0.copy_within(old_range, new_range.start);
		// Clear old range.
		let clear = stack_size - (self.registers.len() - old_registers_len) * reg_size;
		self.stack.0[clear..].fill(MaybeUninit::new(0));

		// SAFETY: The stack is large enough... Hopefully.
		// The stack is properly aligned.
		// Virtual registers are properly initialized.
		unsafe {
			let stack = self.stack.0.as_ptr().add(new_range.start);
			self.status = func.call_with_stack(stack.cast(), self.status);
		}

		Ok(self.status)
	}
}

impl Default for Shell {
	fn default() -> Self {
		Self {
			stack: Default::default(),
			status: Default::default(),
			registers: Default::default(),
		}
	}
}
