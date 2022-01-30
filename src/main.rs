#![feature(const_discriminant)]
#![feature(if_let_guard)]

mod jit;
mod op;
mod runtime;
mod token;

fn main() -> Result<(), Box<dyn std::error::Error>> {
	let f = std::env::args().skip(1).next().ok_or("usage: qsh <file>")?;
	let f = std::fs::read(f)?;
	let f = std::str::from_utf8(&f)?;
	let f = op::parse(token::TokenParser::new(f).map(Result::unwrap)).unwrap();
	let f = jit::compile(f, |f| match f {
		"print" => Some(runtime::ffi_print),
		"exec" => Some(runtime::ffi_exec),
		_ => None,
	});
	f.call(&[]);
	Ok(())
}
