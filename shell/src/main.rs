use core::str;
use qsh::runtime;
use qsh::shell::Shell;
use std::env;
use std::error::Error;
use std::fs;
use std::io;

fn main() -> Result<(), Box<dyn Error>> {
	let mut args = env::args().skip(1);
	if let Some(a) = args.next() {
		run(&a).map(|_| ())
	} else {
		interactive()
	}
}

fn run(file: &str) -> Result<isize, Box<dyn Error>> {
	let s = fs::read(file)?;
	let s = str::from_utf8(&s)?;
	let s = qsh::compile(s, runtime::resolve_fn)?;
	Ok(s.call(&[], 0))
}

fn interactive() -> Result<(), Box<dyn Error>> {
	let mut sh = Shell::default();
	let mut ret = 0;
	loop {
		eprint!("{:>4} > ", ret);
		let mut s = Default::default();
		io::stdin().read_line(&mut s)?;
		ret = sh.evaluate(&s, runtime::resolve_fn).unwrap_or(-9999);
		s.clear();
	}
}
