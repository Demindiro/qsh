mod arc_str;

pub use arc_str::{ArcStr, TArcStr};

use core::fmt;
use core::slice;

#[derive(Debug)]
pub enum Value {
	String(ArcStr),
	Integer(isize),
}

impl fmt::Display for Value {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		match self {
			Self::String(s) => s.fmt(f),
			Self::Integer(s) => s.fmt(f),
		}
	}
}

#[derive(Debug)]
pub enum TValue<'a> {
	String(TArcStr<'a>),
	Integer(isize),
}

impl<'a> From<&'a Value> for TValue<'a> {
	fn from(v: &'a Value) -> Self {
		match v {
			Value::String(s) => Self::String(s.into()),
			Value::Integer(s) => Self::Integer(*s),
		}
	}
}

impl<'a> fmt::Display for TValue<'a> {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		match self {
			Self::String(s) => s.fmt(f),
			Self::Integer(s) => s.fmt(f),
		}
	}
}

macro_rules! wrap_ffi {
	(pub $new_fn:ident = $fn:ident) => {
		pub fn $new_fn(argc: usize, argv: *const TValue) {
			$fn(unsafe { slice::from_raw_parts(argv, argc) })
		}
	};
}

pub fn print(args: &[TValue]) {
	for (i, a) in args.iter().enumerate() {
		print!("{}", a);
		(i != args.len() - 1).then(|| print!(" "));
	}
	println!();
}

wrap_ffi!(pub ffi_print = print);
