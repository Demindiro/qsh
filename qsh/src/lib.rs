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
pub mod token;
pub mod shell;
