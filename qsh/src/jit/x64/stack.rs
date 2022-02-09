//! Utilities for manipulating the stack.

use super::X64Compiler;
use crate::runtime::{QFunction, TValue};
use core::mem;
use dynasmrt::{dynasm, DynasmApi};

impl<'a, F> X64Compiler<'a, F>
where
	F: Fn(&str) -> Option<QFunction>,
{
	/// Allocate and zero out a fixed-size section of the stack.
	pub(super) fn stack_alloc_zeroed(&mut self, size: i32) {
		dynasm!(self.jit
			; mov ecx, size
			; xor eax, eax
			; sub rsp, rcx
			; mov rdi, rsp
			; rep stosb
		);
	}

	pub(super) fn push_stack(&mut self, v: i64) -> i32 {
		match v {
			v if let Ok(v) = v.try_into() => dynasm!(self.jit ; push BYTE v),
			v if let Ok(v) = v.try_into() => dynasm!(self.jit ; push DWORD v),
			v => dynasm!(self.jit ; mov rsi, QWORD v; push rsi),
		}
		8
	}

	pub(super) fn push_stack_value(&mut self, v: TValue) -> i32 {
		// FIXME transmuting Value::Nil is technically UB because part of it is unitialized.
		let [a, b] = unsafe { mem::transmute::<_, [i64; 2]>(v) };
		self.push_stack(b) + self.push_stack(a)
	}
}
