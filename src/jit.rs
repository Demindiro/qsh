use crate::op::{Argument, Op};
use crate::runtime::*;
use core::fmt;
use core::mem;
use dynasmrt::{dynasm, AssemblyOffset, DynasmApi, DynasmLabelApi, ExecutableBuffer};
use std::collections::{btree_map::Entry, BTreeMap};
use std::rc::Rc;

/// A JIT-compiled function that can be called.
pub struct Function {
	exec: ExecutableBuffer,
	data_offset: AssemblyOffset,
	#[cfg(feature = "iced")]
	symbols: Rc<BTreeMap<usize, Box<str>>>,
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

#[cfg(feature = "iced")]
impl fmt::Debug for Function {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		use iced_x86::{
			Decoder, Formatter, FormatterTextKind, Instruction, IntelFormatter, SymResString,
			SymResTextInfo, SymResTextPart, SymbolResolver, SymbolResult,
		};
		let mut dec = Decoder::new(64, &self.exec[..self.data_offset.0], 0);

		struct Symbols(Rc<BTreeMap<usize, Box<str>>>);

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
						text: SymResString::Str(&*s),
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
		let mut s = String::new();
		while dec.can_decode() {
			s.clear();
			let instr = dec.decode();
			fmt.format(&instr, &mut s);
			if let Some(s) = self.symbols.get(&instr.ip().try_into().unwrap()) {
				writeln!(f, "{}:", s)?;
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

/// Compile an opcode tree to native machine-code.
pub fn compile<F>(ops: Box<[Op]>, resolve_fn: F) -> Function
where
	F: Fn(&str) -> Option<QFunction>,
{
	#[cfg(target_arch = "x86_64")]
	return compile_x64(ops, resolve_fn);
	#[cfg(not(any(target_arch = "x86_64")))]
	compile_error!("unsupported architecture");
}

#[cfg(target_arch = "x86_64")]
fn compile_x64<F>(ops: Box<[Op]>, resolve_fn: F) -> Function
where
	F: Fn(&str) -> Option<QFunction>,
{
	let mut jit = X64Compiler::new(resolve_fn);
	jit.compile(ops);
	jit.finish()
}

#[cfg(target_arch = "x86_64")]
struct X64Compiler<F>
where
	F: Fn(&str) -> Option<QFunction>,
{
	jit: dynasmrt::x64::Assembler,
	data: Vec<Value>,
	resolve_fn: F,
	variables: BTreeMap<Box<str>, usize>,
	strings: Vec<u8>,
	#[cfg(feature = "iced")]
	symbols: BTreeMap<usize, Box<str>>,
	#[cfg(feature = "iced")]
	comments: BTreeMap<usize, String>,
}

#[cfg(target_arch = "x86_64")]
impl<F> X64Compiler<F>
where
	F: Fn(&str) -> Option<QFunction>,
{
	fn new(resolve_fn: F) -> Self {
		Self {
			jit: dynasmrt::x64::Assembler::new().unwrap(),
			data: Default::default(),
			resolve_fn,
			variables: Default::default(),
			strings: Default::default(),
			#[cfg(feature = "iced")]
			symbols: Default::default(),
			#[cfg(feature = "iced")]
			comments: Default::default(),
		}
	}

	fn finish(mut self) -> Function {
		self.comment("return");
		match self.variables.len() * 16 {
			8 => dynasm!(self.jit ; pop rdi),
			l if let Ok(l) = l.try_into() => dynasm!(self.jit ; add rsp, BYTE l),
			l => dynasm!(self.jit ; add rsp, l.try_into().unwrap()),
		}
		dynasm!(self.jit ; ret);

		// Add data
		let data_offset = self.jit.offset();
		dynasm!(self.jit
			; .align 8
			; data:
		);
		#[cfg(feature = "iced")]
		for i in 0..self.data.len() * 16 {
			self.symbols
				.insert(data_offset.0 + i, format!("data+{}", i).into());
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
			self.symbols
				.insert(strings_offset.0 + i, format!("strings+{}", i).into());
		}
		self.jit.extend(self.strings);
		Function {
			exec: self.jit.finalize().unwrap(),
			data_offset,
			#[cfg(feature = "iced")]
			symbols: Rc::new(self.symbols),
			#[cfg(feature = "iced")]
			comments: self.comments,
		}
	}

	fn compile(&mut self, ops: Box<[Op]>) {
		for op in ops.into_vec() {
			match op {
				Op::Call {
					function,
					arguments,
					pipe_out,
					pipe_in,
				} => {
					self.comment("call ".to_string() + &function);
					// Resolve function or default to 'exec'
					let (f, push_fn_name) = (self.resolve_fn)(&*function)
						.map(|f| (f, false))
						.or_else(|| (self.resolve_fn)("exec").map(|f| (f, true)))
						.expect("'exec' not defined");

					// Reserve space for out values (if they don't exist yet)
					for (from, to) in pipe_out.iter() {
						dbg!(&from, &to);
						self.set_variable((&**to).into(), None);
					}

					// How much the stack has grown in bytes.
					// Used for calculating offsets to variables.
					let mut stack_bytes = 0;

					// Create out list
					self.comment("out pipes");
					let len = pipe_out.len().try_into().unwrap();
					for (from, to) in pipe_out.into_vec() {
						self.comment(format!("{} > @{}", from, to));
						let str_offt = self.strings.len();
						self.strings.push(from.len().try_into().unwrap());
						self.strings.extend(from.bytes());
						let offt = self.variables.len() - self.variables[&*to] - 1;
						let offt = (offt * 16 + stack_bytes).try_into().unwrap();
						dynasm!(self.jit
							// value pointer
							; lea rax, [rsp + offt]
							; push rax
							// name
							; lea rax, [>strings + str_offt.try_into().unwrap()]
							; push rax
						);
						stack_bytes += 16;
					}
					dynasm!(self.jit
						; mov edx, BYTE len
						; mov rcx, rsp
					);

					// Create in list
					self.comment("in pipes");
					let len = pipe_in.len().try_into().unwrap();
					for (from, to) in pipe_in.into_vec() {
						self.comment(format!("{} < @{}", to, from));
						let str_offt = self.strings.len();
						self.strings.push(to.len().try_into().unwrap());
						self.strings.extend(to.bytes());
						let offt = self.variables.len() - self.variables[&*from] - 1;
						let offt = (offt * 16 + stack_bytes + 8).try_into().unwrap();
						dynasm!(self.jit
							// value
							; push QWORD [rsp + offt]
							// value discriminant
							; push QWORD [rsp + offt]
							// name
							; lea rax, [>strings + str_offt.try_into().unwrap()]
							; push rax
						);
						stack_bytes += 24;
					}
					dynasm!(self.jit
						; mov r8, len
						; mov r9, rsp
					);

					// Note start of data if all arguments are static. Also push program name
					// if using 'exec'
					let i = self.data.len();
					if push_fn_name {
						self.data.push(Value::String((&*function).into()));
					}
					#[cfg(feature = "iced")]
					self.symbols.insert(
						f as usize,
						push_fn_name.then(|| "exec".into()).unwrap_or(function),
					);

					// Figure out whether we need to use the stack.
					let use_stack = arguments.iter().any(|a| match a {
						Argument::Variable(_) => true,
						_ => false,
					});
					let len = arguments.len() + push_fn_name.then(|| 1).unwrap_or(0);

					// Create argument list
					if use_stack {
						self.comment("dynamic args");

						// Note that stack pushing is top-down
						for a in arguments.into_vec().into_iter().rev() {
							let v = match a {
								Argument::String(s) => Value::String((&*s).into()),
								Argument::Variable(v) => {
									let offt = self.variables.len() - self.variables[&v] - 1;
									dbg!(offt, stack_bytes);
									let offt = (offt * 16 + stack_bytes + 8).try_into().unwrap();
									dynasm!(self.jit
										; push QWORD [rsp + offt]
										; push QWORD [rsp + offt]
									);
									stack_bytes += 16;
									continue;
								}
								_ => todo!("argument {:?}", a),
							};
							stack_bytes += self.push_stack_value((&v).into());
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
						self.comment("constant args");

						// Push arguments
						for a in arguments.into_vec() {
							let v = match a {
								Argument::String(s) => Value::String((&*s).into()),
								Argument::Variable(_) => unreachable!(),
								_ => todo!("argument {:?}", a),
							};
							self.data.push(v);
						}
						if let Ok(n) = len.try_into() {
							dynasm!(self.jit ; mov edi, DWORD n);
						} else {
							dynasm!(self.jit ; mov rdi, len.try_into().unwrap())
						}

						dynasm!(self.jit
							; lea rsi, [>data + (i * 16).try_into().unwrap()]
						);
					}

					// Align stack to 16 bytes, then call
					// Note that we didn't align the stack at the start of the function,
					// so offset by 8
					self.comment("call");
					(stack_bytes % 16 != 8).then(|| dynasm!(self.jit ; push rbx));
					dynasm!(self.jit
						; mov rax, QWORD f as _
						; call rax
					);
					(stack_bytes % 16 != 8).then(|| dynasm!(self.jit ; pop rbx));

					// Restore stack
					if let Ok(n) = stack_bytes.try_into() {
						dynasm!(self.jit ; add rsp, BYTE n);
					} else {
						dynasm!(self.jit ; add rsp, stack_bytes.try_into().unwrap())
					}
				}
				Op::If {
					condition,
					if_true,
					if_false,
				} => {
					self.compile(condition);
					dynasm!(self.jit
						; test rax, rax
						// FIXME 1-byte jumps may not always be possible.
						// Some sort of rollback mechanism if it fails would be useful.
						// UncommittedModifier may be usable for this purpose.
						; jne BYTE >if_false
					);
					self.compile(if_true);
					if if_false.len() > 0 {
						dynasm!(self.jit
							; jmp >if_true
							; if_false:
						);
						self.compile(if_false);
						dynasm!(self.jit
							; if_true:
						);
					} else {
						#[cfg(feature = "iced")]
						self.symbols.insert(self.jit.offset().0, "if_false".into());
						dynasm!(self.jit
							; if_false:
						);
					}
				}
				Op::Assign {
					variable,
					statement,
				} => {
					self.comment(format!("@{} = {:?}", variable, statement));
					self.set_variable(variable, Some(statement))
				}
				op => todo!("parse {:?}", op),
			}
		}
	}

	fn set_variable(&mut self, variable: Box<str>, statement: Option<Argument>) {
		let i = self.variables.len();
		let mut vars = mem::take(&mut self.variables); // Avoid silly borrow errors
		match vars.entry(variable) {
			Entry::Vacant(e) => {
				let v = match statement {
					Some(Argument::String(s)) => Value::String((&*s).into()),
					None => Value::Nil,
					_ => todo!("assign {:?}", statement),
				};
				self.push_stack_value((&v).into());
				self.data.push(v);
				e.insert(i);
			}
			Entry::Occupied(_) => todo!("occupied"),
		}
		self.variables = vars;
	}

	fn push_stack(&mut self, v: i64) -> usize {
		match v {
			v if let Ok(v) = v.try_into() => dynasm!(self.jit ; push BYTE v),
			v if let Ok(v) = v.try_into() => dynasm!(self.jit ; push DWORD v),
			v => dynasm!(self.jit ; mov rsi, QWORD v; push rsi),
		}
		8
	}

	fn push_stack_value(&mut self, v: TValue) -> usize {
		let [a, b] = unsafe { mem::transmute::<_, [i64; 2]>(v) };
		self.push_stack(b) + self.push_stack(a)
	}

	fn comment(&mut self, comment: impl AsRef<str> + Into<String>) {
		let _c = comment.as_ref();
		#[cfg(feature = "iced")]
		self.comments
			.entry(self.jit.offset().0)
			.and_modify(|s| {
				*s += ", ";
				*s += _c;
			})
			.or_insert_with(|| comment.into());
	}
}

#[cfg(test)]
mod test {
	use super::*;
	use crate::op::*;
	use crate::token::*;
	use crate::wrap_ffi;
	use core::cell::RefCell;

	thread_local! {
		static OUT: RefCell<String> = RefCell::default();
	}

	fn print(args: &[TValue], out: &mut [OutValue<'_>], inv: &[InValue<'_>]) -> isize {
		OUT.with(|out| {
			let mut out = out.borrow_mut();
			for (i, a) in args.iter().enumerate() {
				dbg!(unsafe { mem::transmute_copy::<_, [u64; 2]>(a) });
				(i > 0).then(|| out.push(' '));
				out.extend(a.to_string().chars());
			}
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
				if o.name() == "1" {
					o.set_value(Value::String((&*stdout).into()));
					return;
				}
			}
			o.borrow_mut().extend(stdout.chars())
		});
		code
	}

	wrap_ffi!(ffi_print = print);
	wrap_ffi!(ffi_exec = exec);

	fn clear_out() {
		OUT.with(|out| out.borrow_mut().clear())
	}

	fn resolve_fn(f: &str) -> Option<QFunction> {
		match f {
			"print" => Some(ffi_print),
			"exec" => Some(ffi_exec),
			_ => None,
		}
	}

	fn run(s: &str) {
		clear_out();
		let ops = parse(TokenParser::new(s).map(Result::unwrap)).unwrap();
		let f = compile(ops, resolve_fn);
		dbg!(&f);
		f.call(&[]);
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
	fn variable() {
		run("@a = 5; @b = \"five\"; print @a is pronounced as @b");
		OUT.with(|out| assert_eq!("5 is pronounced as five\n", &*out.borrow()));
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
}
