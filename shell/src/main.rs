use std::error::Error;
use std::io;
use qsh::shell::Shell;
use qsh::runtime;

fn main() -> Result<(), Box<dyn Error>> {
	let mut sh = Shell::default();
	loop {
		eprint!("> ");
		let mut s = Default::default();
		io::stdin().read_line(&mut s)?;
		dbg!(sh.evaluate(&s, runtime::resolve_fn));
		s.clear();
	}
}
