use crate::op::{self, Expression, ForRange, Op, OpTree, RegisterIndex};
use crate::runtime::*;
use core::cell::Cell;
use core::fmt;
use core::mem;
#[cfg(target_arch = "x86_64")]
use dynasmrt::x64;
use dynasmrt::{dynasm, AssemblyOffset, DynasmApi, DynasmLabelApi, ExecutableBuffer, Register};
use std::collections::{btree_map::Entry, BTreeMap};
use std::rc::Rc;

/// A JIT-compiled function that can be called.
pub struct Function {
	exec: ExecutableBuffer,
	data_offset: AssemblyOffset,
	#[cfg(feature = "iced")]
	symbols: Rc<BTreeMap<usize, Vec<Box<str>>>>,
	#[cfg(feature = "iced")]
	comments: BTreeMap<usize, String>,
}

impl Function {
	pub fn call(&self, _args: &[TValue]) {
		unsafe {
			let f: extern "C" fn() = mem::transmute(self.exec.ptr(AssemblyOffset(0)));
			f()
		}
	}
}

impl fmt::Debug for Function {
	#[cfg(feature = "iced")]
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		use iced_x86::{
			Decoder, Formatter, FormatterTextKind, Instruction, IntelFormatter, SymResString,
			SymResTextInfo, SymResTextPart, SymbolResolver, SymbolResult,
		};
		let mut dec = Decoder::new(64, &self.exec[..self.data_offset.0], 0);

		struct Symbols(Rc<BTreeMap<usize, Vec<Box<str>>>>);

		impl SymbolResolver for Symbols {
			fn symbol(
				&mut self,
				_: &Instruction,
				_: u32,
				_: Option<u32>,
				address: u64,
				_: u32,
			) -> Option<SymbolResult<'_>> {
				self.0.get(&address.try_into().unwrap()).map(|s| {
					// "How many data structures do you want?" "Yes"
					// implement From<&str> pls
					let text = SymResTextInfo::Text(SymResTextPart {
						text: SymResString::Str(&*s[0]),
						color: FormatterTextKind::Label,
					});
					SymbolResult {
						address,
						flags: 0,
						text,
						symbol_size: None,
					}
				})
			}
		}

		let mut fmt =
			IntelFormatter::with_options(Some(Box::new(Symbols(self.symbols.clone()))), None);
		fmt.options_mut().set_digit_separator("_");
		fmt.options_mut().set_hex_prefix("0x");
		fmt.options_mut().set_hex_suffix("");
		fmt.options_mut().set_uppercase_hex(false);
		fmt.options_mut().set_rip_relative_addresses(true);

		writeln!(f, "")?;
		let mut s = String::new();
		while dec.can_decode() {
			s.clear();
			let instr = dec.decode();
			fmt.format(&instr, &mut s);
			if let Some(s) = self.symbols.get(&instr.ip().try_into().unwrap()) {
				for s in s.iter() {
					writeln!(f, "{}:", s)?;
				}
			}
			write!(f, "{:4x}  ", instr.ip())?;
			for b in &self.exec[instr.ip() as usize..][..instr.len()] {
				write!(f, "{:02x}", b)?;
			}
			(instr.len()..15).try_for_each(|_| f.write_str("  "))?;
			if let Some(c) = self.comments.get(&instr.ip().try_into().unwrap()) {
				writeln!(f, "  {:<32}  ; {}", s, c)?;
			} else {
				writeln!(f, "  {}", s)?;
			}
		}
		Ok(())
	}

	#[cfg(not(feature = "iced"))]
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		f.debug_struct(stringify!(Function)).finish_non_exhaustive()
	}
}

/// Compile an opcode tree to native machine-code.
pub fn compile<F>(ops: OpTree<'_>, resolve_fn: F) -> Function
where
	F: Fn(&str) -> Option<QFunction>,
{
	#[cfg(target_arch = "x86_64")]
	return compile_x64(ops, resolve_fn);
	#[cfg(not(any(target_arch = "x86_64")))]
	compile_error!("unsupported architecture");
}

#[cfg(target_arch = "x86_64")]
fn compile_x64<F>(ops: OpTree<'_>, resolve_fn: F) -> Function
where
	F: Fn(&str) -> Option<QFunction>,
{
	let mut jit = X64Compiler::new(resolve_fn, ops.registers.into(), ops.functions);

	// main function
	jit.insert_prologue(0);
	jit.compile(ops.ops);
	jit.insert_epilogue();

	// user defined functions
	jit.compile_functions();

	// small routines + data
	jit.finish()
}

#[cfg(target_arch = "x86_64")]
struct X64Compiler<'a, F>
where
	F: Fn(&str) -> Option<QFunction>,
{
	jit: dynasmrt::x64::Assembler,
	data: Vec<Value>,
	resolve_fn: F,
	strings: Vec<u8>,
	retval_defined: bool,
	#[cfg(feature = "iced")]
	symbols: BTreeMap<usize, Vec<Box<str>>>,
	#[cfg(feature = "iced")]
	comments: Cell<BTreeMap<usize, String>>,
	stack_offset: i32,
	registers: Box<[op::Register<'a>]>,
	functions: BTreeMap<&'a str, (op::Function<'a>, dynasmrt::DynamicLabel)>,
}

#[cfg(target_arch = "x86_64")]
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
		let mut s = Self {
			data: Default::default(),
			resolve_fn,
			strings: Default::default(),
			retval_defined: Default::default(),
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
		};
		s
	}

	/// Insert the common function prologue.
	fn insert_prologue(&mut self, argument_count: usize) {
		let l = ((self.registers.len() - argument_count) * 16)
			.try_into()
			.unwrap();
		dynasm!(self.jit
			;; self.comment(|| "set non-arg registers to nil")
			; mov ecx, l
			; xor eax, eax
			; sub rsp, rcx
			; mov rdi, rsp
			; rep stosb
		);
	}

	/// Insert the common function epilogue.
	fn insert_epilogue(&mut self) {
		assert_eq!(self.stack_offset, 0, "stack is not properly restored");
		dynasm!(self.jit
			;; self.comment(|| "return")
			// stack OOB check was already done in insert_prologue, so just cast
			; add rsp, (self.registers.len() * 16) as i32
			; ret
			;; self.symbol("bad_argument_count")
			; bad_argument_count:
			// Ditto
			; add rsp, (self.registers.len() * 16) as i32
			// Shortest sequence to move -2 to rax
			; push BYTE -2
			; pop rax
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
		}
	}

	/// Compile all functions.
	fn compile_functions(&mut self) {
		for (name, (f, lbl)) in mem::take(&mut self.functions).into_iter() {
			assert_eq!(self.stack_offset, 0, "stack is not properly restored");
			self.symbol(name);
			// Arguments to this function are not checked during compile time, so check
			// during runtime.
			// arg registers in order: rdi, rsi, rdx, rcx, r8, r9
			// arguments: argc, argv, outc, outb, inc, inv
			dynasm!(self.jit
				; =>lbl
				;; self.comment(|| "check argument count")
				; cmp rdi, f.arguments.len().try_into().unwrap()
				; jne >bad_argument_count
				; test rdx, rdx // outc == 0 always for now.
				; jne >bad_argument_count
				; test r8, r8 // inc == 0 always for now.
				; jne >bad_argument_count
				;; self.comment(|| "preserve arg count")
				; mov r11, rdi
				;; self.comment(|| "adjust arg count ahead of time (avoid stall)")
				; shl r11, 4
			);
			self.registers = f.registers;
			self.insert_prologue(f.arguments.len());
			dynasm!(self.jit
				;; self.comment(|| "copy arguments to virtual registers")
				; sub rsp, r11
				; mov rcx, r11
				; mov rdi, rsp
				; rep movsb
			);
			self.compile(f.ops);
			self.insert_epilogue();
		}
	}

	fn compile(&mut self, ops: Box<[Op<'a>]>) {
		for op in ops.into_vec() {
			match op {
				Op::Call {
					function,
					arguments,
					pipe_out,
					pipe_in,
				} => {
					self.comment(|| format!("call '{}'", &function));

					enum Fn {
						BuiltIn(QFunction),
						User(dynasmrt::DynamicLabel),
						Exec(QFunction),
					}

					// Resolve built-in function, user defined function or default to 'exec'
					let f = (self.resolve_fn)(&*function)
						.map(Fn::BuiltIn)
						.or_else(|| self.functions.get(&function).map(|l| Fn::User(l.1)))
						.or_else(|| (self.resolve_fn)("exec").map(Fn::Exec))
						.expect("'exec' not defined");

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

					// Note start of data if all arguments are static. Also push program name
					// if using 'exec'
					let i = self.data.len();
					let fn_str_val = if let Fn::Exec(_) = f {
						let f = Value::String((&*function).into());
						let fp = unsafe { core::mem::transmute_copy::<_, [i64; 2]>(&f) };
						self.data.push(f);
						Some(fp)
					} else {
						None
					};
					#[cfg(feature = "iced")]
					match f {
						Fn::User(_) => (),
						Fn::BuiltIn(f) => self
							.symbols
							.entry(f as usize)
							.or_default()
							.push(function.into()),
						Fn::Exec(f) => self
							.symbols
							.entry(f as usize)
							.or_default()
							.push("exec".into()),
					}

					// Figure out whether we need to use the stack.
					let use_stack = arguments.iter().any(|a| match a {
						Expression::Variable(_) => true,
						_ => false,
					});
					let len = arguments.len() + fn_str_val.is_some().then(|| 1).unwrap_or(0);

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
						if let Some([a, b]) = fn_str_val {
							dynasm!(self.jit
								; mov rax, QWORD b
								; push rax
								; mov rax, QWORD a
								; push rax
							);
							self.stack_offset += 16;
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
					if self.stack_offset % 16 != 8 {
						dynasm!(self.jit ; push rbx);
						self.stack_offset += 8;
					}

					match f {
						Fn::User(f) => dynasm!(self.jit ; call => f),
						Fn::BuiltIn(f) | Fn::Exec(f) => {
							dynasm!(self.jit
								; mov rax, QWORD f as _
								; call rax
							);
						}
					}

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
							assert!(self.retval_defined);
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
							assert!(self.retval_defined);
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
				op => todo!("parse {:?}", op),
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

	fn push_stack(&mut self, v: i64) -> i32 {
		match v {
			v if let Ok(v) = v.try_into() => dynasm!(self.jit ; push BYTE v),
			v if let Ok(v) = v.try_into() => dynasm!(self.jit ; push DWORD v),
			v => dynasm!(self.jit ; mov rsi, QWORD v; push rsi),
		}
		8
	}

	fn push_stack_value(&mut self, v: TValue) -> i32 {
		// FIXME transmuting Value::Nil is technically UB because part of it is unitialized.
		let [a, b] = unsafe { mem::transmute::<_, [i64; 2]>(v) };
		self.push_stack(b) + self.push_stack(a)
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
	fn reg_to_var(&self, reg: RegisterIndex) -> &'a str {
		self.registers[usize::from(reg.0)].variable
	}
}

#[cfg(test)]
mod test {
	use super::{Function, *};
	use crate::op::*;
	use crate::token::*;
	use crate::wrap_ffi;
	use core::cell::RefCell;

	thread_local! {
		static OUT: RefCell<String> = RefCell::default();
		static COUNTER: RefCell<usize> = RefCell::default();
	}

	fn print(args: &[TValue], out: &mut [OutValue<'_>], inv: &[InValue<'_>]) -> isize {
		let it = args
			.iter()
			.map(|v| v.to_string().chars().collect::<Vec<_>>())
			.intersperse_with(|| Vec::from([' ']))
			.flatten();
		for o in out {
			match o.name() {
				"" | "1" => {
					let s = (&it.chain(['\n']).collect::<String>()).into();
					o.set_value(Value::String(s));
					return 0;
				}
				_ => (),
			}
		}
		OUT.with(|out| {
			let mut out = out.borrow_mut();
			out.extend(it);
			out.push('\n');
		});
		0
	}

	fn exec(args: &[TValue], out: &mut [OutValue<'_>], inv: &[InValue<'_>]) -> isize {
		use std::io::{Read, Write};
		use std::process::{Command, Stdio};

		let mut stdin = Stdio::null();
		let mut val = None;
		for i in inv {
			if i.name() == "0" {
				stdin = Stdio::piped();
				val = Some(i.value());
				break;
			}
		}
		let mut cmd = Command::new(args[0].to_string())
			.args(args[1..].iter().map(|a| a.to_string()))
			.stdout(Stdio::piped())
			.stdin(stdin)
			.spawn()
			.unwrap();
		val.map(|val| {
			cmd.stdin
				.take()
				.unwrap()
				.write_all(val.to_string().as_bytes())
				.unwrap()
		});
		let code = cmd.wait().unwrap().code().unwrap_or(-1).try_into().unwrap();
		let stdout = cmd.stdout.unwrap();
		let stdout = stdout.bytes().map(Result::unwrap).collect::<Vec<_>>();
		let stdout = String::from_utf8_lossy(&stdout);
		OUT.with(|o| {
			for o in out {
				match o.name() {
					"" | "1" => {
						o.set_value(Value::String((&*stdout).into()));
						return;
					}
					_ => (),
				}
			}
			o.borrow_mut().extend(stdout.chars())
		});
		code
	}

	fn count_to_10(_: &[TValue], _: &mut [OutValue<'_>], _: &[InValue<'_>]) -> isize {
		COUNTER.with(|c| {
			let mut c = c.borrow_mut();
			*c += 1;
			(*c > 10).then(|| 1).unwrap_or(0)
		})
	}

	wrap_ffi!(ffi_print = print);
	wrap_ffi!(ffi_exec = exec);
	wrap_ffi!(ffi_count_to_10 = count_to_10);

	fn clear_out() {
		OUT.with(|out| out.borrow_mut().clear());
		COUNTER.with(|c| *c.borrow_mut() = 0);
	}

	fn resolve_fn(f: &str) -> Option<QFunction> {
		match f {
			"print" => Some(ffi_print),
			"exec" => Some(ffi_exec),
			"split" => Some(ffi_split),
			"count_to_10" => Some(ffi_count_to_10),
			_ => None,
		}
	}

	fn compile(s: &str) -> Function {
		let ops = OpTree::new(TokenParser::new(s).map(Result::unwrap)).unwrap();
		super::compile(ops, resolve_fn)
	}

	fn run(s: &str) {
		clear_out();
		compile(s).call(&[])
	}

	#[test]
	fn hello() {
		run("print Hello world!");
		OUT.with(|out| assert_eq!("Hello world!\n", &*out.borrow()));
	}

	#[test]
	fn echo() {
		run("echo Hello world!");
		OUT.with(|out| assert_eq!("Hello world!\n", &*out.borrow()));
	}

	#[test]
	fn hello_echo() {
		run("echo Hello; print world!");
		OUT.with(|out| assert_eq!("Hello\nworld!\n", &*out.borrow()));
	}

	#[test]
	fn cond_if() {
		run("if true; print yes");
		OUT.with(|out| assert_eq!("yes\n", &*out.borrow()));
		run("if false; print yes");
		OUT.with(|out| assert_eq!("", &*out.borrow()));
	}

	#[test]
	fn call_if() {
		run("if test -n \"aa\"; print yes");
		OUT.with(|out| assert_eq!("yes\n", &*out.borrow()));
		run("if test -n \"\"; print yes");
		OUT.with(|out| assert_eq!("", &*out.borrow()));
	}

	#[test]
	fn assign_variable() {
		run("@a = $42;");
		OUT.with(|out| assert_eq!("", &*out.borrow()));
	}

	#[test]
	fn assign_variable_2() {
		run("@a = $42; @b = forty_two");
		OUT.with(|out| assert_eq!("", &*out.borrow()));
	}

	#[test]
	fn print_variable() {
		run("@a = xyz; print @a");
		OUT.with(|out| assert_eq!("xyz\n", &*out.borrow()));
	}

	#[test]
	fn print_variable_2() {
		run("@a = 5; @b = \"five\"; print @a is pronounced as @b");
		OUT.with(|out| assert_eq!("5 is pronounced as five\n", &*out.borrow()));
	}

	#[test]
	fn print_pipe_print() {
		run("print abc > ; print @");
		OUT.with(|out| assert_eq!("abc\n\n", &*out.borrow()));
	}

	#[test]
	fn ret_value() {
		run("echo chickens are neat 1>; print output: @");
		OUT.with(|out| assert_eq!("output: chickens are neat\n\n", &*out.borrow()));
	}

	#[test]
	fn cat() {
		run("echo chickens are neat 1>; cat 0<");
		OUT.with(|out| assert_eq!("chickens are neat\n", &*out.borrow()));
	}

	#[test]
	fn for_loop() {
		run("printf abcde >; split \"\" < >; for a in @; print @a");
		OUT.with(|out| assert_eq!("a\nb\nc\nd\ne\n", &*out.borrow()));
	}

	#[test]
	fn for_if_loop() {
		run("printf abcde\\n >; split < >; for a in @; if test -n @a; print @a");
		OUT.with(|out| assert_eq!("abcde\n", &*out.borrow()));
	}

	#[test]
	fn for_for_loop() {
		run("@ = $0; for a in @; for b in @; print");
		OUT.with(|out| assert_eq!("", &*out.borrow()));
	}

	#[test]
	fn for_for_split_print() {
		run("printf a.b/c.d >; split / < >; for a in @; (split . <a >a; for b in @a; print @b)");
		OUT.with(|out| assert_eq!("a\nb\nc\nd\n", &*out.borrow()));
	}

	#[test]
	fn while_loop() {
		run("while count_to_10; print y");
		OUT.with(|out| assert_eq!("y\ny\ny\ny\ny\ny\ny\ny\ny\ny\n", &*out.borrow()));
	}

	#[test]
	fn block() {
		run("@y = kek; if true; (print x; print @y; false); if @?; print z");
		OUT.with(|out| assert_eq!("x\nkek\n", &*out.borrow()));
	}

	#[test]
	fn function() {
		run("fn foo; print yay; foo");
		OUT.with(|out| assert_eq!("yay\n", &*out.borrow()));
	}

	#[test]
	fn function_arg() {
		run("fn foo a; print @a; foo abracadabra");
		OUT.with(|out| assert_eq!("abracadabra\n", &*out.borrow()));
	}

	#[test]
	fn function_wrong_arg() {
		run("fn foo a; print @; foo abracadabra");
		OUT.with(|out| assert_eq!("(nil)\n", &*out.borrow()));
	}
}
