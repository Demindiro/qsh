#![feature(const_discriminant)]
#![feature(const_refs_to_cell)]
#![feature(core_intrinsics)]
#![feature(if_let_guard)]
#![feature(iter_intersperse)]
#![feature(trusted_len)]

mod jit;
mod op;
mod runtime;
mod token;

fn main() -> Result<(), Box<dyn std::error::Error>> {
	let f = std::env::args().skip(1).next().ok_or("usage: qsh <file>")?;
	let f = std::fs::read(f)?;
	let f = std::str::from_utf8(&f)?;
	let f = token::TokenParser::new(f)
		.map(Result::unwrap)
		.collect::<Vec<_>>();
	dbg!(&f);
	let f = op::parse(f.into_iter()).unwrap();
	dbg!(&f);
	let f = jit::compile(f, |f| match f {
		"print" => Some(runtime::ffi_print),
		"exec" => Some(runtime::ffi_exec),
		"split" => Some(runtime::ffi_split),
		_ => None,
	});
	dbg!(&f);
	f.call(&[]);
	Ok(())
}
