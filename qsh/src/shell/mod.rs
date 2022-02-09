//! Utilities for creating interactive shells.

use core::mem::MaybeUninit;
use crate::token::{Token, TokenParser};
use crate::op::{Op, OpTree};
use crate::runtime::QFunction;
use crate::jit;

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
#[derive(Default)]
pub struct Shell {
	/// Stack used for storing variables & executing commands.
	stack: Stack,
	/// The last status code returned by a call. Defaults to 0.
	status: isize,
}

impl Shell {
	/// How much space to reserve for variables (virtual registers) on the stack initially.
	/// This count is in [`Value`]s.
	const INITIAL_VREG_CAPACITY: usize = 32;
	/// By how much to allocate more space for variables if the capacity runs out.
	const VREG_CAPACITY_GROW: usize = 8;

	/// Feed a string of code, parsing & executing it if it is complete.
	pub fn evaluate<F>(&mut self, code: &str, resolve_fn: F) -> Result<isize, ()>
	where
		F: Fn(&str) -> Option<QFunction> + Copy,
	{
		dbg!(code);

		let mut tokens = Vec::new();
		TokenParser::new(code).try_fold((), |(), t| t.map(|t| tokens.push(t)))
			.map_err(|_| ())?;

		let mut ops = OpTree::new(tokens.into_iter(), resolve_fn)
			.map_err(|_| ())?;

		let mut func = jit::compile(ops, resolve_fn);

		dbg!(&func);

		self.status = func.call(&[], self.status);
		Ok(self.status)
	}
}
