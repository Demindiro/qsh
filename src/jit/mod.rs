#[cfg(target_arch = "x86_64")]
mod x64;

use crate::op::{self, Expression, ForRange, Op, OpTree, RegisterIndex};
use crate::runtime::*;
use core::cell::Cell;
use core::fmt;
use core::mem;
use dynasmrt::{AssemblyOffset, ExecutableBuffer};
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

#[cfg(not(feature = "iced"))]
impl fmt::Debug for Function {
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
	return x64::compile(ops, resolve_fn);
	#[cfg(not(any(target_arch = "x86_64")))]
	compile_error!("unsupported architecture");
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

	#[test]
	fn function_pipe_out() {
		run("fn foo a >x; print @a >x; foo abracadabra >; print its @?");
		OUT.with(|out| assert_eq!("its abracadabra\n", &*out.borrow()));
	}
}
