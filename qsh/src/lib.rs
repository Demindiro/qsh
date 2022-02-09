#![allow(unused_unsafe)]
#![feature(const_discriminant)]
#![feature(const_refs_to_cell)]
#![feature(core_intrinsics)]
#![feature(if_let_guard)]
#![feature(iter_intersperse)]
#![feature(naked_functions)]
#![feature(map_try_insert)]
#![feature(maybe_uninit_uninit_array)]
#![feature(trusted_len)]

pub mod jit;
pub mod op;
pub mod runtime;
pub mod shell;
pub mod token;

/// Compile a script.
pub fn compile<F>(s: &str, resolve_fn: F) -> Result<jit::Function, Box<dyn std::error::Error>>
where
	F: Fn(&str) -> Option<runtime::QFunction>,
{
	let mut tk = Vec::new();
	token::TokenParser::new(s).try_for_each(|t| t.map(|t| tk.push(t)))?;
	let ops = op::OpTreeParser::new(&resolve_fn).parse(tk.into_iter())?;
	Ok(jit::compile(ops, resolve_fn))
}
