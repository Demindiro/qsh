#[cfg(feature = "iced")]
mod debug;
mod function;
mod stack;

use std::borrow::Cow;
use super::Function;
use crate::op::{self, Expression, ForRange, Op, OpTree, RegisterIndex};
use crate::runtime::*;
use core::cell::Cell;
use core::mem;
use dynasmrt::x64;
use dynasmrt::{dynasm, DynasmApi, DynasmLabelApi, Register};
use std::collections::BTreeMap;
#[cfg(feature = "iced")]
use std::rc::Rc;

pub(super) fn compile<F>(ops: OpTree<'_>, resolve_fn: F) -> Function
where
	F: Fn(&str) -> Option<QFunction>,
{
	let mut jit = X64Compiler::new(resolve_fn, ops.registers.into(), ops.functions);

	// main function
	jit.stack_offset += 8;
	jit.compile(ops.ops);
	jit.stack_offset -= 8;
	jit.insert_epilogue();

	// user defined functions
	jit.compile_functions();

	// small routines + data
	jit.finish()
}

struct X64Compiler<'a, F>
where
	F: Fn(&str) -> Option<QFunction>,
{
	jit: dynasmrt::x64::Assembler,
	data: Vec<Value>,
	resolve_fn: F,
	strings: Vec<u8>,
	#[cfg(feature = "iced")]
	symbols: BTreeMap<usize, Vec<Box<str>>>,
	#[cfg(feature = "iced")]
	comments: Cell<BTreeMap<usize, String>>,
	stack_offset: i32,
	registers: Box<[op::Register<'a>]>,
	functions: BTreeMap<&'a str, (op::Function<'a>, dynasmrt::DynamicLabel)>,
}

impl<'a, F> X64Compiler<'a, F>
where
	F: Fn(&str) -> Option<QFunction>,
{
	fn new(
		resolve_fn: F,
		registers: Box<[op::Register<'a>]>,
		functions: BTreeMap<&'a str, op::Function<'a>>,
	) -> Self {
		let mut jit = dynasmrt::x64::Assembler::new().unwrap();
		Self {
			data: Default::default(),
			resolve_fn,
			strings: Default::default(),
			#[cfg(feature = "iced")]
			symbols: Default::default(),
			#[cfg(feature = "iced")]
			comments: Default::default(),
			stack_offset: 0,
			registers,
			functions: functions
				.into_iter()
				.map(|(k, v)| (k, (v, jit.new_dynamic_label())))
				.collect(),
			jit,
		}
	}

	/// Insert the common function epilogue.
	fn insert_epilogue(&mut self) {
		assert_eq!(self.stack_offset, 0, "stack is not properly restored");
		dynasm!(self.jit
			; ret
		);
	}

	fn finish(mut self) -> Function {
		// Add data
		let data_offset = self.jit.offset();
		dynasm!(self.jit
			; .align 8
			; data:
		);
		#[cfg(feature = "iced")]
		for i in 0..self.data.len() * 16 {
			self.symbols
				.insert(data_offset.0 + i, Vec::from([format!("data+{}", i).into()]));
		}
		for d in self.data {
			let [a, b] = unsafe { mem::transmute::<_, [u64; 2]>(d) };
			self.jit.push_u64(a);
			self.jit.push_u64(b);
		}

		// Add strings
		let strings_offset = self.jit.offset();
		dynasm!(self.jit
			; strings:
		);
		#[cfg(feature = "iced")]
		for i in 0..self.strings.len() {
			self.symbols.insert(
				strings_offset.0 + i,
				Vec::from([format!("strings+{}", i).into()]),
			);
		}
		self.jit.extend(self.strings);
		Function {
			exec: self.jit.finalize().unwrap(),
			data_offset,
			#[cfg(feature = "iced")]
			symbols: Rc::new(self.symbols),
			#[cfg(feature = "iced")]
			comments: self.comments.take(),
			stack_bytes: self.registers.len() * 16,
		}
	}

	fn compile(&mut self, ops: Box<[Op<'a>]>) {
		for op in ops.into_vec() {
			match op {
				Op::Call {
					function,
					arguments,
					pipe_in,
					pipe_out,
				} => self.compile_local_call(function, arguments, pipe_in, pipe_out),
				Op::CallBuiltin {
					function,
					arguments,
					pipe_in,
					pipe_out,
				} => self.compile_builtin_call(function, arguments, pipe_in, pipe_out),
				Op::Exec {
					arguments,
					pipe_in,
					pipe_out,
				} => self.compile_builtin_call(
					(self.resolve_fn)("exec").expect("'exec' not defined"),
					arguments,
					pipe_in,
					pipe_out,
				),
				Op::If {
					condition,
					if_true,
					if_false,
				} => {
					let if_true_lbl = self.jit.new_dynamic_label();
					let if_false_lbl = self.jit.new_dynamic_label();
					let if_end = self.jit.new_dynamic_label();

					match condition {
						// TODO use an enum for special variables
						Expression::Variable(s) if self.reg_to_var(s) == "?" => {
							// rax is set even if no calls has been made as per our QSH ABI.
							dynasm!(self.jit
								;; self.comment(|| "if @?")
								; test rax, rax
								; jne =>if_false_lbl
							);
						}
						Expression::Variable(s) => {
							self.comment(|| format!("if @{}", self.reg_to_var(s)));
							dynasm!(self.jit
								;; let offt = self.variable_offset(s)
								; mov rax, [rsp + offt + 0]
								// Test if *not* nil
								;; self.comment(|| "test nil")
								; cmp rax, Value::NIL_DISCRIMINANT.try_into().unwrap()
								; je =>if_false_lbl
								;; self.comment(|| "load value")
								; mov rdx, [rsp + offt + 8]
								// Test if integer is 0
								;; self.comment(|| "test int")
								; cmp rax, Value::INTEGER_DISCRIMINANT.try_into().unwrap()
								; jne >if_not_int
								; test rdx, rdx
								; je =>if_true_lbl
								; jmp =>if_false_lbl
								; if_not_int:
								// Test if array or string is *not* empty
								// Arrays and strings both have len at the same position
								;; self.comment(|| "test string")
								; cmp rax, Value::STRING_DISCRIMINANT.try_into().unwrap()
								; je >if_string
								;; self.comment(|| "test array")
								; cmp rax, Value::ARRAY_DISCRIMINANT.try_into().unwrap()
								; jne >if_not_array
								; if_string:
								; mov rdx, [rdx + 8]
								; test rdx, rdx
								; jne =>if_true_lbl
								; jmp =>if_false_lbl
								; if_not_array:
								// There's also pipes, but idk how to handle them.
								// Use ud2 as guard
								; ud2
							);
						}
						Expression::Statement(c) => {
							dynasm!(self.jit
								;; self.comment(|| "if <statement>")
							);
							self.compile(c);
							dynasm!(self.jit
								;; self.comment(|| "skip if not 0")
								; test rax, rax
								; jne =>if_false_lbl
							);
						}
						c => todo!("condition {:?}", c),
					}
					dynasm!(self.jit
						;; self.symbol("if_end")
						; =>if_true_lbl
					);
					self.compile(if_true);

					if if_false.len() > 0 {
						dynasm!(self.jit
							; jmp >if_end
							; =>if_false_lbl
						);
						self.compile(if_false);
						dynasm!(self.jit
							;; self.symbol("if_end")
							; =>if_end
						);
					} else {
						dynasm!(self.jit
							;; self.symbol("if_false")
							; =>if_false_lbl
						);
					}
				}
				Op::For {
					variable,
					range,
					for_each,
				} => {
					self.comment(|| "for");
					let range = match range {
						ForRange::Variable(v) => v,
					};

					// Use dynamic labels as loops may be nested (and hence local labels will
					// interfere with each other)
					let for_end = self.jit.new_dynamic_label();
					let for_array = self.jit.new_dynamic_label();
					let for_array_check = self.jit.new_dynamic_label();

					dynasm!(self.jit
						;; self.comment(|| "test if array")
						;; let range_offt = self.variable_offset(range)
						; mov rax, [rsp + range_offt]
						; cmp rax, BYTE Value::ARRAY_DISCRIMINANT.try_into().unwrap()
						;; self.comment(|| "skip if not array")
						; jne =>for_end

						;; self.comment(|| "save previous iteration or caller")
						; push rbx
						; push r12
						;; self.stack_offset += 16
						;; let range_offt = self.variable_offset(range)
						;; let var_offt = self.variable_offset(variable)

						;; self.comment(|| "load array pointer")
						; mov rbx, [rsp + range_offt + 8]
						;; self.comment(|| "calculate end address")
						; mov r12, [rbx + 8]
						; add r12, r12 // size * 2 (1 byte shorter than shl r12, 4)
						; lea r12, [rbx + 16 + r12 * 8] // base + 16 + size * 16
						;; self.comment(|| "check if array is empty")
						; jmp =>for_array_check

						;; self.symbol("for_array")
						; =>for_array
						;; self.comment(|| format!("load element into @{}", self.reg_to_var(variable)))
						; mov rax, [rbx + 0]
						; mov rdx, [rbx + 8]
						; mov [rsp + var_offt + 0], rax
						; mov [rsp + var_offt + 8], rdx
					);

					self.compile(for_each);

					dynasm!(self.jit

						;; self.symbol("for_array_check")
						; =>for_array_check
						; add rbx, 16
						; cmp rbx, r12
						; jne =>for_array

						;; self.comment(|| "restore previous iteration or caller")
						; pop r12
						; pop rbx
						;; self.stack_offset -= 16
						;; self.symbol("for_end")
						; =>for_end
					);
				}
				Op::While {
					condition,
					while_true,
				} => {
					let while_true_lbl = self.jit.new_dynamic_label();
					let while_test = self.jit.new_dynamic_label();

					// Put condition at end of body so we have 1 branch per iteration
					// instead of 2.
					dynasm!(self.jit
						;; self.comment(|| "while")
						; jmp =>while_test
						;; self.symbol("while_true")
						; =>while_true_lbl
					);

					self.compile(while_true);

					dynasm!(self.jit
						;; self.symbol("while_test")
						; =>while_test
					);

					// TODO don't just copy paste the code for If you lazy bastard.
					match condition {
						// TODO use an enum for special variables
						Expression::Variable(s) if self.reg_to_var(s) == "?" => {
							dynasm!(self.jit
								;; self.comment(|| "if @?")
								; test rax, rax
								; je >while_true
							);
						}
						Expression::Variable(s) => {
							self.comment(|| format!("if @{}", self.reg_to_var(s)));
							let offt = self.variable_offset(s);
							dynasm!(self.jit
								; mov rax, [rsp + offt + 0]
								// Test if *not* nil
								;; self.comment(|| "test nil")
								; cmp rax, Value::NIL_DISCRIMINANT.try_into().unwrap()
								; je >while_end
								;; self.comment(|| "load value")
								; mov rdx, [rsp + offt + 8]
								// Test if integer is 0
								;; self.comment(|| "test int")
								; cmp rax, Value::INTEGER_DISCRIMINANT.try_into().unwrap()
								; jne >if_not_int
								; test rdx, rdx
								; je =>while_true_lbl
								; jmp >while_end
								; if_not_int:
								// Test if array or string is *not* empty
								// Arrays and strings both have len at the same position
								;; self.comment(|| "test string")
								; cmp rax, Value::STRING_DISCRIMINANT.try_into().unwrap()
								; je >if_string
								;; self.comment(|| "test array")
								; cmp rax, Value::ARRAY_DISCRIMINANT.try_into().unwrap()
								; jne >if_not_array
								; if_string:
								; mov rdx, [rdx + 8]
								; test rdx, rdx
								; jne =>while_true_lbl
								; jmp >while_end
								; if_not_array:
								// There's also pipes, but idk how to handle them.
								// Use ud2 as guard
								; ud2
								;; self.symbol("while_end")
								; while_end:
							);
						}
						Expression::Statement(c) => {
							dynasm!(self.jit
								;; self.comment(|| "while <statement>")
								;; self.compile(c)
								;; self.comment(|| "skip if not 0")
								; test rax, rax
								; je =>while_true_lbl
							);
						}
						c => todo!("condition {:?}", c),
					}
				}
				Op::Assign {
					variable,
					expression,
				} => {
					self.comment(|| format!("@{} = {:?}", self.reg_to_var(variable), expression));
					self.set_variable(variable, expression)
				}
			}
		}
	}

	fn set_variable(&mut self, var: RegisterIndex, expression: Expression) {
		let val = match expression {
			Expression::String(v) => Value::String((&*v).into()),
			Expression::Integer(v) => Value::Integer(v.into()),
			_ => todo!(),
		};
		let i = self.variable_offset(var);
		// FIXME transmuting Value::Nil is technically UB because part of it is unitialized.
		let [a, b] = unsafe { mem::transmute::<_, [i64; 2]>(val) };
		self.mov_const(x64::Rq::RSP, i, a);
		self.mov_const(x64::Rq::RSP, i.checked_add(8).unwrap(), b);
	}

	/// Get the current offset of a variable in bytes. This includes the stack offset.
	fn variable_offset(&self, var: RegisterIndex) -> i32 {
		self.stack_offset + i32::from(var.0) * 16
	}

	/// Move a constant to a memory location with the most optimal instruction(s).
	///
	/// It may use `rdi` as a scratch register if necessary.
	fn mov_const(&mut self, reg: x64::Rq, offt: i32, val: i64) {
		let reg = reg.code();
		if let Ok(offt) = offt.try_into() {
			if let Ok(val) = i32::try_from(val) {
				dynasm!(self.jit ; mov QWORD [BYTE Rq(reg) + offt], DWORD val);
			} else {
				dynasm!(self.jit
					; mov rdi, QWORD val
					; mov [BYTE Rq(reg) + offt], rdi
				);
			}
		} else {
			if let Ok(val) = i32::try_from(val) {
				dynasm!(self.jit ; mov QWORD [DWORD Rq(reg) + offt], DWORD val);
			} else {
				dynasm!(self.jit
					; mov rdi, QWORD val
					; mov [DWORD Rq(reg) + offt], rdi
				);
			}
		}
	}

	// Non-mutable to avoid borrow errors in trivial cases.
	fn comment<R>(&self, comment: impl FnOnce() -> R)
	where
		R: AsRef<str> + Into<String>,
	{
		let _c = comment;
		#[cfg(feature = "iced")]
		{
			let mut v = self.comments.take();
			let c = _c();
			v.entry(self.jit.offset().0)
				.and_modify(|s| {
					*s += ", ";
					*s += c.as_ref();
				})
				.or_insert_with(|| c.into());
			self.comments.set(v);
		}
	}

	fn symbol(&mut self, symbol: impl Into<String>) {
		let _s = symbol;
		#[cfg(feature = "iced")]
		self.symbols
			.entry(self.jit.offset().0)
			.or_default()
			.push(_s.into().into());
	}

	/// Map a register to a variable
	fn reg_to_var(&self, reg: RegisterIndex) -> &str {
		&self.registers[usize::from(reg.0)].variable
	}
}
