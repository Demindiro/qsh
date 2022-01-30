mod arc_str;

pub use arc_str::{ArcStr, TArcStr};

use core::fmt;
use core::mem;
use core::ptr::NonNull;
use core::str;
use core::slice;

pub type ValueDiscriminant = usize;
pub type QFunction = for<'a> extern "C" fn(usize, *const TValue, usize, *mut OutValue<'a>) -> isize;

#[derive(Debug)]
pub enum Value {
	Nil,
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
			Self::Nil => f.write_str("(nil)"),
			Self::String(s) => s.fmt(f),
			Self::Integer(s) => s.fmt(f),
		}
	}
}

#[derive(Debug)]
pub enum TValue<'a> {
	Nil,
	String(TArcStr<'a>),
	Integer(isize),
}

const fn _check(v: &Value, t: &TValue) -> u8 {
	unsafe {
		(mem::transmute::<_, ValueDiscriminant>(mem::discriminant(v))
			== mem::transmute::<_, ValueDiscriminant>(mem::discriminant(t))) as u8
	}
}

const _CHECK_NIL: u8 = _check(&Value::Nil, &TValue::Nil) - 1;
const _CHECK_INT: u8 = _check(&Value::Integer(0), &TValue::Integer(0)) - 1;

impl<'a> From<&'a Value> for TValue<'a> {
	fn from(v: &'a Value) -> Self {
		match v {
			Value::Nil => Self::Nil,
			Value::String(s) => Self::String(s.into()),
			Value::Integer(s) => Self::Integer(*s),
		}
	}
}

impl<'a> fmt::Display for TValue<'a> {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		match self {
			Self::Nil => f.write_str("(nil)"),
			Self::String(s) => s.fmt(f),
			Self::Integer(s) => s.fmt(f),
		}
	}
}

#[repr(C)]
pub struct OutValue<'a> {
	name: NonNull<u8>,
	value: &'a mut Value,
}

impl OutValue<'_> {
	#[inline(always)]
	pub fn name(&self) -> &str {
		unsafe {
			let s = *self.name.as_ref();
			let s = slice::from_raw_parts(self.name.as_ptr().add(1), s.into());
			str::from_utf8_unchecked(s)
		}
	}

	#[inline(always)]
	pub fn set_value(&mut self, value: Value) {
		*self.value = value
	}
}

impl fmt::Debug for OutValue<'_> {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		f.debug_struct(stringify!(OutValue))
			.field("name", &self.name())
			.field("value", self.value)
			.finish()
	}
}

#[macro_export]
macro_rules! wrap_ffi {
	($new_fn:ident = $fn:ident) => {
		wrap_ffi!(@INTERNAL [] $new_fn = $fn);
	};
	(pub $new_fn:ident = $fn:ident) => {
		wrap_ffi!(@INTERNAL [pub] $new_fn = $fn);
	};
	(@INTERNAL [$($vis:ident)*] $new_fn:ident = $fn:ident) => {
		$($vis)* extern "C" fn $new_fn(argc: usize, argv: *const TValue, outc: usize, outv: *mut OutValue<'_>) -> isize {
			unsafe {
				use core::slice;
				debug_assert!(!argv.is_null());
				debug_assert!(!outv.is_null());
				$fn(slice::from_raw_parts(argv, argc), slice::from_raw_parts_mut(outv, outc))
			}
		}
	};
}

pub fn print(args: &[TValue], _: &mut [OutValue<'_>]) -> isize {
	for (i, a) in args.iter().enumerate() {
		print!("{}", a);
		(i != args.len() - 1).then(|| print!(" "));
	}
	println!();
	0
}

wrap_ffi!(pub ffi_print = print);
