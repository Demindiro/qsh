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
}

impl Function {
	pub fn call(&self, _args: &[TValue]) {
		unsafe {
			let f: fn() = mem::transmute(self.exec.ptr(AssemblyOffset(0)));
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
			writeln!(f, "  {}", s)?;
		}
		Ok(())
	}
}

/// Compile an opcode tree to native machine-code.
pub fn compile<F>(ops: Box<[Op]>, resolve_fn: F) -> Function
where
	F: Fn(&str) -> Option<fn(usize, *const TValue) -> isize>,
{
	#[cfg(target_arch = "x86_64")]
	return compile_x64(ops, resolve_fn);
	#[cfg(not(any(target_arch = "x86_64")))]
	compile_error!("unsupported architecture");
}

#[cfg(target_arch = "x86_64")]
fn compile_x64<F>(ops: Box<[Op]>, resolve_fn: F) -> Function
where
	F: Fn(&str) -> Option<fn(usize, *const TValue) -> isize>,
{
	let mut jit = X64Compiler::new(resolve_fn);
	jit.compile(ops);
	jit.finish()
}

#[cfg(target_arch = "x86_64")]
struct X64Compiler<F>
where
	F: Fn(&str) -> Option<fn(usize, *const TValue) -> isize>,
{
	jit: dynasmrt::x64::Assembler,
	data: Vec<Value>,
	resolve_fn: F,
	variables: BTreeMap<Box<str>, usize>,
	#[cfg(feature = "iced")]
	symbols: BTreeMap<usize, Box<str>>,
}

#[cfg(target_arch = "x86_64")]
impl<F> X64Compiler<F>
where
	F: Fn(&str) -> Option<fn(usize, *const TValue) -> isize>,
{
	fn new(resolve_fn: F) -> Self {
		let mut jit = dynasmrt::x64::Assembler::new().unwrap();
		dynasm!(jit ; push rdi);
		Self {
			jit,
			data: Default::default(),
			resolve_fn,
			variables: Default::default(),
			#[cfg(feature = "iced")]
			symbols: Default::default(),
		}
	}

	fn finish(mut self) -> Function {
		match self.variables.len() * 16 + 8 {
			8 => dynasm!(self.jit ; pop rdi),
			l if let Ok(l) = l.try_into() => dynasm!(self.jit ; add rsp, BYTE l),
			l => dynasm!(self.jit ; add rsp, l.try_into().unwrap()),
		}
		dynasm!(self.jit ; ret);
		let data_offset = self.jit.offset();
		dynasm!(self.jit
			; .align 8
			; data:
		);
		#[cfg(feature = "iced")]
		for i in 0..self.data.len() {
			self.symbols
				.insert(data_offset.0, format!("data+{}", i * 16).into());
		}
		for d in self.data {
			let [a, b] = unsafe { mem::transmute::<_, [u64; 2]>(d) };
			self.jit.push_u64(a);
			self.jit.push_u64(b);
		}
		Function {
			exec: self.jit.finalize().unwrap(),
			data_offset,
			#[cfg(feature = "iced")]
			symbols: Rc::new(self.symbols),
		}
	}

	fn compile(&mut self, ops: Box<[Op]>) {
		let push_stack = |jit: &mut dynasmrt::x64::Assembler, v: i64| {
			match v {
			v if let Ok(v) = v.try_into() => dynasm!(jit ; push BYTE v),
			v if let Ok(v) = v.try_into() => dynasm!(jit ; push DWORD v),
			v => dynasm!(jit ; mov rsi, QWORD v; push rsi),
		}
		};
		for op in ops.into_vec() {
			match op {
				Op::Call {
					function,
					arguments,
				} => {
					let (f, push_fn_name) = (self.resolve_fn)(&*function)
						.map(|f| (f, false))
						.or_else(|| (self.resolve_fn)("exec").map(|f| (f, true)))
						.expect("'exec' not defined");
					let i = self.data.len();
					if push_fn_name {
						self.data.push(Value::String((&*function).into()));
					}
					#[cfg(feature = "iced")]
					self.symbols.insert(
						f as usize,
						push_fn_name.then(|| "exec".into()).unwrap_or(function),
					);

					let use_stack = arguments.iter().any(|a| match a {
						Argument::Variable(_) => true,
						_ => false,
					});
					let len = arguments.len() + push_fn_name.then(|| 1).unwrap_or(0);

					if use_stack {
						// Note that stack pushing is top-down
						for (i, a) in arguments.iter().rev().enumerate() {
							let v = match a {
								Argument::String(s) => Value::String((&**s).into()),
								Argument::Variable(v) => {
									let offt = self.variables.len() - self.variables[v] - 1;
									dbg!(offt, i);
									let offt = ((offt + i) * 16 + 8).try_into().unwrap();
									dynasm!(self.jit
										; push QWORD [rsp + offt]
										; push QWORD [rsp + offt]
									);
									continue;
								}
								_ => todo!("argument {:?}", a),
							};
							let [a, b] = unsafe { mem::transmute_copy::<_, [i64; 2]>(&v) };
							push_stack(&mut self.jit, b);
							push_stack(&mut self.jit, a);
							self.data.push(v);
						}
						if let Ok(n) = len.try_into() {
							dynasm!(self.jit ; mov edi, DWORD n);
						} else {
							dynasm!(self.jit ; mov rdi, len.try_into().unwrap())
						}
						dynasm!(self.jit
							; mov rsi, rsp
							; mov rax, QWORD f as _
							; call rax
						);
						let len = len * 16;
						if let Ok(n) = len.try_into() {
							dynasm!(self.jit ; add rsp, BYTE n);
						} else {
							dynasm!(self.jit ; add rsp, len.try_into().unwrap())
						}
					} else {
						for a in arguments.iter() {
							let v = match a {
								Argument::String(s) => Value::String((&**s).into()),
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
							; mov rax, QWORD f as _
							; call rax
						);
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
					let i = self.variables.len();
					match self.variables.entry(variable) {
						Entry::Vacant(e) => {
							let v = match statement {
								Argument::String(s) => Value::String((&*s).into()),
								_ => todo!("assign {:?}", statement),
							};
							let [a, b] = unsafe { mem::transmute::<_, [i64; 2]>(v) };
							push_stack(&mut self.jit, b);
							push_stack(&mut self.jit, a);
							e.insert(i);
						}
						Entry::Occupied(_) => todo!("occupied"),
					}
				}
				op => todo!("parse {:?}", op),
			}
		}
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

	fn print(args: &[TValue]) -> isize {
		OUT.with(|out| {
			let mut out = out.borrow_mut();
			dbg!(args);
			for (i, a) in args.iter().enumerate() {
				dbg!(unsafe { mem::transmute_copy::<_, [u64; 2]>(a) });
				(i > 0).then(|| out.push(' '));
				out.extend(a.to_string().chars());
			}
			out.push('\n');
		});
		0
	}

	fn exec(args: &[TValue]) -> isize {
		use std::process::Command;
		let out = Command::new(args[0].to_string())
			.args(args[1..].iter().map(|a| a.to_string()))
			.output()
			.unwrap();
		OUT.with(|o| {
			o.borrow_mut()
				.extend(String::from_utf8_lossy(&out.stdout).chars())
		});
		out.status.code().unwrap_or(-1).try_into().unwrap()
	}

	wrap_ffi!(ffi_print = print);
	wrap_ffi!(ffi_exec = exec);

	fn clear_out() {
		OUT.with(|out| out.borrow_mut().clear())
	}

	fn resolve_fn(f: &str) -> Option<fn(usize, *const TValue) -> isize> {
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
}
