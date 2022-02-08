#![feature(const_discriminant)]
#![feature(const_refs_to_cell)]
#![feature(core_intrinsics)]
#![feature(if_let_guard)]
#![feature(iter_intersperse)]
#![feature(map_try_insert)]
#![feature(trusted_len)]

pub mod jit;
pub mod op;
pub mod runtime;
pub mod token;
