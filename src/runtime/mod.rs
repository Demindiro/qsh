mod arc_str;

pub use arc_str::{ArcStr, TArcStr};

use core::fmt;
use core::mem;
use core::ptr::NonNull;
use core::slice;
use core::str;

pub type ValueDiscriminant = usize;
pub type QFunction = for<'a> extern "C" fn(
	usize,
	*const TValue,
	usize,
	*mut OutValue<'a>,
	usize,
	*const InValue<'a>,
) -> isize;

#[derive(Clone, Debug)]
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

#[derive(Clone, Copy, Debug)]
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

#[repr(C)]
pub struct InValue<'a> {
	name: NonNull<u8>,
	value: TValue<'a>,
}

impl<'a> InValue<'a> {
	#[inline(always)]
	pub fn name(&self) -> &str {
		unsafe {
			let s = *self.name.as_ref();
			let s = slice::from_raw_parts(self.name.as_ptr().add(1), s.into());
			str::from_utf8_unchecked(s)
		}
	}

	#[inline(always)]
	pub fn value(&self) -> TValue<'a> {
		self.value
	}
}

impl fmt::Debug for InValue<'_> {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		f.debug_struct(stringify!(InValue))
			.field("name", &self.name())
			.field("value", &self.value)
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
		$($vis)* extern "C" fn $new_fn(argc: usize, argv: *const TValue, outc: usize, outv: *mut OutValue<'_>, inc: usize, inv: *const InValue<'_>) -> isize {
			unsafe {
				use core::slice::{from_raw_parts, from_raw_parts_mut};
				debug_assert!(!argv.is_null());
				debug_assert!(!outv.is_null());
				debug_assert!(!inv.is_null());
				$fn(from_raw_parts(argv, argc), from_raw_parts_mut(outv, outc), from_raw_parts(inv, inc))
			}
		}
	};
}

pub fn print(args: &[TValue], _: &mut [OutValue<'_>], _: &[InValue<'_>]) -> isize {
	for (i, a) in args.iter().enumerate() {
		print!("{}", a);
		(i != args.len() - 1).then(|| print!(" "));
	}
	println!();
	0
}

pub fn exec(args: &[TValue], out: &mut [OutValue<'_>], inv: &[InValue<'_>]) -> isize {
	use std::io::{Read, Write};
	use std::process::{Command, Stdio};

	// Figure out I/O redirection
	let mut stdin = Stdio::inherit();
	let mut stdout = Stdio::inherit();
	let mut stderr = Stdio::inherit();
	let mut val = None;
	for i in inv {
		if i.name() == "0" {
			stdin = Stdio::piped();
			val = Some(i.value());
			break;
		}
	}
	for o in out {
		match o.name() {
			"1" => stdout = Stdio::piped(),
			"2" => stderr = Stdio::piped(),
			_ => (),
		}
	}

	let mut cmd = Command::new(args[0].to_string())
		.args(args[1..].iter().map(|a| a.to_string()))
		.stdin(stdin)
		.stdout(stdout)
		.stderr(stderr)
		.spawn()
		.unwrap();
	let code = cmd.wait().unwrap().code().unwrap_or(-1);
	code.try_into().unwrap()
}

wrap_ffi!(pub ffi_print = print);
wrap_ffi!(pub ffi_exec  = exec );
