#![feature(const_discriminant)]
#![feature(const_refs_to_cell)]
#![feature(core_intrinsics)]
#![feature(if_let_guard)]
#![feature(iter_intersperse)]
#![feature(map_try_insert)]
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
	//dbg!(&f);
	let f = op::OpTree::new(f.into_iter(), resolve_fn).unwrap();
	//dbg!(&f);
	let f = jit::compile(f, resolve_fn);
	//dbg!(&f);
	f.call(&[]);
	Ok(())
}

fn resolve_fn(f: &str) -> Option<runtime::QFunction> {
	match f {
		"print" => Some(runtime::FFI_PRINT),
		"exec" => Some(runtime::FFI_EXEC),
		"split" => Some(runtime::FFI_SPLIT),
		_ => None,
	}
}
