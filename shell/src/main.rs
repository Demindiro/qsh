use std::error::Error;
use std::io;
use qsh::shell::Shell;
use qsh::runtime;

fn main() -> Result<(), Box<dyn Error>> {
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
