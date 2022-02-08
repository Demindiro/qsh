use super::Function;
use crate::op::{self, Expression, ForRange, Op, OpTree, RegisterIndex};
use crate::runtime::*;
use core::cell::Cell;
use core::fmt;
use core::mem;
use dynasmrt::x64;
use dynasmrt::{dynasm, AssemblyOffset, DynasmApi, DynasmLabelApi, ExecutableBuffer, Register};
use std::collections::{btree_map::Entry, BTreeMap};
use std::rc::Rc;

#[cfg(feature = "iced")]
impl fmt::Debug for Function {
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
}

#[cfg(target_arch = "x86_64")]
pub(super) fn compile<F>(ops: OpTree<'_>, resolve_fn: F) -> Function
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
			}
		}
	}

	/// Compile a call to a local user-defined function.
	fn compile_local_call(
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
		// Note that we want to align on a mod 16 + 8 boundary so that the callee
		// compensates properly.
		let offt = (pipe_out.len() + pipe_in.len() * 2 + arguments.len() * 2) * 8;
		let offt = if (i32::try_from(offt).unwrap() + self.stack_offset) % 16 == 8 {
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
	fn compile_builtin_call(
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
		if self.stack_offset % 16 != 8 {
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
