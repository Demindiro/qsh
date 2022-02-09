//! Utilities for compiling functions & function calls.

use super::{Function, X64Compiler};
use crate::op::{Expression, RegisterIndex};
use crate::runtime::{QFunction, TValue, Value};
use core::arch::asm;
use core::mem;
use dynasmrt::{dynasm, AssemblyOffset, DynasmApi, DynasmLabelApi};

impl<'a, F> X64Compiler<'a, F>
where
	F: Fn(&str) -> Option<QFunction>,
{
	/// Compile all functions.
	pub(super) fn compile_functions(&mut self) {
		let og_reg = mem::take(&mut self.registers);
		for (name, (f, lbl)) in mem::take(&mut self.functions).into_iter() {
			assert_eq!(self.stack_offset, 0, "stack is not properly restored");
			self.symbol(name);
			// Arguments to this function are not checked during compile time, so check
			// during runtime.
			// arguments: argv + inv + other virt regs + outv (rsp + 8)
			// Note that argv, outv and inv have a fixed size.
			// Registers space is allocated by the caller.
			dynasm!(self.jit
				; =>lbl
				// Registers are already initialized by the caller, so don't use standard prologue
				// Account for return address
				;; self.stack_offset += 8
			);

			self.registers = f.registers;
			self.compile(f.ops);

			// Copy virtual registers to out pipes and return
			dynasm!(self.jit
				;; self.comment(|| "copy to out pipes")
				; lea rsi, [rsp + i32::try_from(self.registers.len() * 16).unwrap() + self.stack_offset]
			);
			for &out in f.pipe_out.iter() {
				// Find the last used register that corresponds to the out variable.
				// If not found, just ignore it. The caller should have set it to nil anyways.
				if let Some(r) = self
					.registers
					.iter()
					.enumerate()
					.rev()
					.find(|r| r.1.variable == out)
				{
					self.comment(|| "copy ".to_string() + out);
					let offt = self.variable_offset(RegisterIndex(r.0 as u16));
					dynasm!(self.jit
						; mov rdi, [rsi]
						;; self.comment(|| "skip if 0")
						; test rdi, rdi
						; jz BYTE >skip
						; mov rcx, [rsp + offt    ]
						; mov rdx, [rsp + offt + 8]
						; mov [rdi    ], rcx
						; mov [rdi + 8], rdx
						;; self.symbol("skip")
						; skip:
					);
				} else {
					self.comment(|| "ignore ".to_string() + out);
				}
				dynasm!(self.jit
					; add rsi, 8
				);
			}
			// Registers are already initialized by the caller, so don't use standard epilogue
			dynasm!(self.jit
				; ret
				;; self.stack_offset -= 8
			);
		}
		self.registers = og_reg;
	}

	/// Compile a call to a local user-defined function.
	pub(super) fn compile_local_call(
		&mut self,
		function: &str,
		arguments: Box<[Expression<'_>]>,
		pipe_in: Box<[(RegisterIndex, &str)]>,
		pipe_out: Box<[(&str, RegisterIndex)]>,
	) {
		self.comment(|| format!("call '{}'", function));
		let (func, _) = &self.functions[function];
		// Verify if arguments, pipe_in and pipe_out are correct as we may
		// not potentially cause UB in safe code.
		assert_eq!(
			func.arguments.len(),
			arguments.len(),
			"argument mismatch (bug in op parser)"
		);
		assert_eq!(
			func.pipe_in.len(),
			pipe_in.len(),
			"pipe_in mismatch (bug in op parser)"
		);
		assert_eq!(
			func.pipe_out.len(),
			pipe_out.len(),
			"pipe_out mismatch (bug in op parser)"
		);
		let registers_len = func.registers.len();

		// Calling convention: argv + inv + other virt regs + outv (rsp + 8)

		let original_stack_offset = self.stack_offset;

		// Align stack beforehand
		// Note that we want to align on a mod 16 boundary so that the callee
		// compensates properly.
		let offt = (pipe_out.len() + pipe_in.len() * 2 + arguments.len() * 2) * 8;
		if (i32::try_from(offt).unwrap() + self.stack_offset) % 16 != 0 {
			dynasm!(self.jit
				; push rbx
			);
			self.stack_offset += 8;
		};

		// Push pipe out
		self.comment(|| "pipe out");
		let (func, lbl) = &self.functions[function];
		let lbl = *lbl;
		'out: for (from, to) in pipe_out.into_vec().into_iter().rev() {
			for &out in func.pipe_out.iter() {
				if from == out {
					let offt = self.variable_offset(to);
					dynasm!(self.jit
						; lea rax, [rsp + offt]
						; push rax
						;; self.stack_offset += 8
					);
					continue 'out;
				}
			}
			dynasm!(self.jit
				; push 0
				;; self.stack_offset += 8
			);
		}

		// Allocate other virtual registers
		let l = ((registers_len - arguments.len() - pipe_in.len()) * 16)
			.try_into()
			.unwrap();
		dynasm!(self.jit
			;; self.comment(|| "set non-arg registers to nil")
			; mov ecx, l
			; xor eax, eax
			; sub rsp, rcx
			;; self.stack_offset += l
			; mov rdi, rsp
			; rep stosb
		);

		// Push pipe in
		self.comment(|| "pipe in");
		'inv: for (from, to) in pipe_in.into_vec().into_iter().rev() {
			for &inv in func.pipe_in.iter() {
				if to == inv {
					let offt = self.variable_offset(from);
					// push decrements rsp before storing
					let offt = offt.checked_add(8).unwrap();
					dynasm!(self.jit
						; push QWORD [rsp + offt]
						; push QWORD [rsp + offt]
						;; self.stack_offset += 16
					);
					continue 'inv;
				}
			}
			dynasm!(self.jit
				; push 0
				; push 0
				;; self.stack_offset += 16
			);
		}

		// Push args
		self.comment(|| "args");
		for a in arguments.into_vec().into_iter().rev() {
			let v = match a {
				Expression::String(s) => Value::String((&*s).into()),
				Expression::Variable(v) => {
					let offt = self.variable_offset(v);
					// push decrements rsp before storing
					let offt = offt.checked_add(8).unwrap();
					dynasm!(self.jit
						; push QWORD [rsp + offt]
						; push QWORD [rsp + offt]
						;; self.stack_offset += 16
					);
					continue;
				}
				_ => todo!("argument {:?}", a),
			};
			self.stack_offset += self.push_stack_value((&v).into());
			self.data.push(v);
		}

		// Call
		dynasm!(self.jit
			;; self.comment(|| "call")
			; call =>lbl
		);

		// Restore stack
		dynasm!(self.jit
			; add rsp, self.stack_offset - original_stack_offset
		);
		self.stack_offset = original_stack_offset;
	}

	/// Compile a call to a function.
	pub(super) fn compile_builtin_call(
		&mut self,
		function: QFunction,
		arguments: Box<[Expression<'_>]>,
		pipe_in: Box<[(RegisterIndex, &str)]>,
		pipe_out: Box<[(&str, RegisterIndex)]>,
	) {
		self.comment(|| format!("call {:?}", &function));

		// TODO should we clear pipe_out values before a call?

		// The original stack offset, used to restore the stack.
		let original_stack_offset = self.stack_offset;

		// Create out list
		self.comment(|| "out pipes");
		let len = pipe_out.len().try_into().unwrap();
		for (from, to) in pipe_out.into_vec() {
			self.comment(|| format!("{} > @{}", from, self.reg_to_var(to)));
			let str_offt = self.strings.len();
			self.strings.push(from.len().try_into().unwrap());
			self.strings.extend(from.bytes());
			let offt = self.variable_offset(to);
			dynasm!(self.jit
				// value pointer
				; lea rax, [rsp + offt]
				; push rax
				// name
				; lea rax, [>strings + str_offt.try_into().unwrap()]
				; push rax
			);
			self.stack_offset += 16;
		}
		dynasm!(self.jit
			; mov edx, BYTE len
			; mov rcx, rsp
		);

		// Create in list
		self.comment(|| "in pipes");
		let len = pipe_in.len().try_into().unwrap();
		for (from, to) in pipe_in.into_vec() {
			self.comment(|| format!("{} < @{}", to, self.reg_to_var(from)));
			let str_offt = self.strings.len();
			self.strings.push(to.len().try_into().unwrap());
			self.strings.extend(to.bytes());
			let offt = self.variable_offset(from).checked_add(8).unwrap();
			dynasm!(self.jit
				// value
				; push QWORD [rsp + offt]
				// value discriminant
				; push QWORD [rsp + offt]
				// name
				; lea rax, [>strings + str_offt.try_into().unwrap()]
				; push rax
			);
			self.stack_offset += 24;
		}
		dynasm!(self.jit
			; mov r8, len
			; mov r9, rsp
		);

		// Note start of data if all arguments are static.
		let i = self.data.len();

		// Figure out whether we need to use the stack.
		let use_stack = arguments.iter().any(|a| match a {
			Expression::Variable(_) => true,
			_ => false,
		});
		let len = arguments.len();

		// Create argument list
		if use_stack {
			self.comment(|| "dynamic args");

			// Note that stack pushing is top-down
			for a in arguments.into_vec().into_iter().rev() {
				let v = match a {
					Expression::String(s) => Value::String((&*s).into()),
					Expression::Variable(v) => {
						let offt = self.variable_offset(v);
						// push decrements rsp before storing
						let offt = offt.checked_add(8).unwrap();
						dynasm!(self.jit
							; push QWORD [rsp + offt]
							; push QWORD [rsp + offt]
						);
						self.stack_offset += 16;
						continue;
					}
					_ => todo!("argument {:?}", a),
				};
				self.stack_offset += self.push_stack_value((&v).into());
				self.data.push(v);
			}
			if let Ok(n) = len.try_into() {
				dynasm!(self.jit ; mov edi, DWORD n);
			} else {
				dynasm!(self.jit ; mov rdi, len.try_into().unwrap())
			}
			dynasm!(self.jit
				; mov rsi, rsp
			);
		} else {
			self.comment(|| "constant args");

			// Push arguments
			for a in arguments.into_vec() {
				let v = match a {
					Expression::String(s) => Value::String((&*s).into()),
					Expression::Variable(_) => unreachable!(),
					_ => todo!("argument {:?}", a),
				};
				self.data.push(v);
			}
			dynasm!(self.jit
				; mov rdi, len.try_into().unwrap()
				; lea rsi, [>data + (i * 16).try_into().unwrap()]
			);
		}

		// Align stack to 16 bytes, then call
		// Note that we didn't align the stack at the start of the function,
		// so offset by 8
		self.comment(|| "call");
		if self.stack_offset % 16 != 0 {
			dynasm!(self.jit ; push rbx);
			self.stack_offset += 8;
		}

		dynasm!(self.jit
			; mov rax, QWORD function.0 as _
			; call rax
		);

		// Restore stack
		let offset = self.stack_offset - original_stack_offset;
		if let Ok(n) = offset.try_into() {
			dynasm!(self.jit ; add rsp, BYTE n);
		} else {
			dynasm!(self.jit ; add rsp, offset);
		}
		self.stack_offset = original_stack_offset;

		// @? is now useable
		self.retval_defined = true;
	}
}

impl Function {
	pub fn call(&self, args: &[TValue], status: isize) -> isize {
		unsafe {
			let f = mem::transmute(self.exec.ptr(AssemblyOffset(0)));
			Self::call_inner(args.len(), args.as_ptr(), f, self.stack_bytes, status)
		}
	}

	#[naked]
	extern "C" fn call_inner(
		argc: usize,
		argv: *const TValue,
		f: extern "C" fn(),
		stack_bytes: usize,
		status: isize,
	) -> isize {
		// rdi: argc
		// rsi: argv
		// rdx: f
		// rcx: stack_bytes
		// r8: status
		unsafe {
			asm!(
				"
				# Preserve original stack pointer
				push rbp
				mov rbp, rsp
				# Allocate space for virtual registers & initialize to nil
				sub rsp, rcx
				xor eax, eax
				mov rdi, rsp
				rep stosb
				mov rax, r8
				# Set previous status & call
				call rdx
				# Restore stack & return
				mov rsp, rbp
				pop rbp
				ret
			",
				options(noreturn)
			)
		}
	}
}
