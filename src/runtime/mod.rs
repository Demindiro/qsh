mod arc_str;

pub use arc_str::{ArcStr, TArcStr};

use core::fmt;
use core::mem;

pub type ValueDiscriminant = usize;

#[derive(Debug)]
pub enum Value {
	String(ArcStr),
	Integer(isize),
}

impl Value {
	#[inline(always)]
	pub const fn string_discriminant() -> ValueDiscriminant {
		const V: Value = Value::Integer(0);
		V.discriminant()
	}

	#[inline(always)]
	pub const fn integer_discriminant() -> ValueDiscriminant {
		const V: Value = Value::Integer(0);
		V.discriminant()
	}

	const fn discriminant(&self) -> ValueDiscriminant {
		unsafe { mem::transmute::<_, ValueDiscriminant>(mem::discriminant(self)) }
	}
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

const fn _check(v: &Value, t: &TValue) -> u8 {
	unsafe {
		(mem::transmute::<_, ValueDiscriminant>(mem::discriminant(v))
			== mem::transmute::<_, ValueDiscriminant>(mem::discriminant(t))) as u8
	}
}

const _CHECK_INT: u8 = _check(&Value::Integer(0), &TValue::Integer(0)) - 1;

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

#[macro_export]
macro_rules! wrap_ffi {
	($new_fn:ident = $fn:ident) => {
		fn $new_fn(argc: usize, argv: *const TValue) -> isize {
			$fn(unsafe { core::slice::from_raw_parts(argv, argc) })
		}
	};
	(pub $new_fn:ident = $fn:ident) => {
		pub fn $new_fn(argc: usize, argv: *const TValue) -> isize {
			$fn(unsafe { core::slice::from_raw_parts(argv, argc) })
		}
	};
}

pub fn print(args: &[TValue]) -> isize {
	for (i, a) in args.iter().enumerate() {
		print!("{}", a);
		(i != args.len() - 1).then(|| print!(" "));
	}
	println!();
	0
}

wrap_ffi!(pub ffi_print = print);
