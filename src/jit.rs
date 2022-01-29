use crate::op::{Argument, Op};
use crate::runtime::*;
use core::fmt;
use core::mem;
use dynasmrt::{dynasm, AssemblyOffset, DynasmApi, DynasmLabelApi, ExecutableBuffer};

/// A JIT-compiled function that can be called.
pub struct Function {
	exec: ExecutableBuffer,
	data_offset: AssemblyOffset,
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
		struct Symbols {
			data: u64,
		}
		impl SymbolResolver for Symbols {
			fn symbol(
				&mut self,
				_: &Instruction,
				_: u32,
				_: Option<u32>,
				address: u64,
				_: u32,
			) -> Option<SymbolResult<'_>> {
				/* TODO fix this
				address.checked_sub(self.data).map(|offt| {
					// "How many data structures do you want?" "Yes"
					// implement From<&str> pls
					let text = SymResTextInfo::Text(SymResTextPart {
						text: SymResString::String(format!("@data[{}]", offt.to_string())),
						color: FormatterTextKind::Label,
					});
					SymbolResult {
						address,
						flags: 0,
						text,
						symbol_size: None,
					}
				})
				*/
				None
			}
		}
		let mut fmt = IntelFormatter::with_options(
			Some(Box::new(Symbols {
				data: self.data_offset.0.try_into().unwrap(),
			})),
			None,
		);
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
}

#[cfg(target_arch = "x86_64")]
impl<F> X64Compiler<F>
where
	F: Fn(&str) -> Option<fn(usize, *const TValue) -> isize>,
{
	fn new(resolve_fn: F) -> Self {
		let mut jit = dynasmrt::x64::Assembler::new().unwrap();
		dynasm!(jit ; push rax);
		Self {
			jit,
			data: Vec::new(),
			resolve_fn,
		}
	}

	fn finish(mut self) -> Function {
		dynasm!(self.jit
			; pop rax
			; ret
		);
		let data_offset = self.jit.offset();
		dynasm!(self.jit
			; .align 8
			; data:
		);
		for d in self.data {
			let [a, b] = unsafe { mem::transmute::<_, [u64; 2]>(d) };
			self.jit.push_u64(a);
			self.jit.push_u64(b);
		}
		Function {
			exec: self.jit.finalize().unwrap(),
			data_offset,
		}
	}

	fn compile(&mut self, ops: Box<[Op]>) {
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
					for a in arguments.iter() {
						let v = match a {
							Argument::String(s) => Value::String((&**s).into()),
							_ => todo!("argument {:?}", a),
						};
						self.data.push(v);
					}
					let len = arguments.len() + push_fn_name.then(|| 1).unwrap_or(0);
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
						dynasm!(self.jit
							; if_false:
						);
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
			for (i, a) in args.iter().enumerate() {
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
}
