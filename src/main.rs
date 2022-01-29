#![feature(const_discriminant)]
#![feature(if_let_guard)]

mod jit;
mod op;
mod runtime;
mod token;

fn main() {
	let ops = op::parse(token::TokenParser::new("print Hello world!").map(Result::unwrap)).unwrap();
	let f = jit::compile(ops, |f| match f {
		"print" => Some(runtime::ffi_print),
		_ => None,
	});
	dbg!(&f);
	f.call(&[]);
}
