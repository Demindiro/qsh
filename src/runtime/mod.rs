mod arc_array;
mod arc_str;
mod array;
mod pipe;

pub use arc_str::{ArcStr, TArcStr};
pub use array::{Array, TArray};
pub use pipe::{Pipe, TPipe};

use core::fmt;
use core::mem::{self, ManuallyDrop};
use core::ptr::NonNull;
use core::slice;
use core::str;

pub type ValueDiscriminant = usize;

#[derive(Clone, Copy)]
pub struct QFunction(
	pub(crate)  for<'a> extern "C" fn(
		usize,
		*const TValue,
		usize,
		*mut OutValue<'a>,
		usize,
		*const InValue<'a>,
	) -> isize,
);

impl PartialEq for QFunction {
	fn eq(&self, rhs: &Self) -> bool {
		self.0 as usize == rhs.0 as usize
	}
}

impl Eq for QFunction {}

impl fmt::Debug for QFunction {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		write!(f, "{:p}", self.0 as *const ())
	}
}

#[derive(Clone, Debug)]
pub enum Value {
	Nil,
	String(ArcStr),
	Integer(isize),
	Pipe(Pipe),
	Array(Array),
}

impl Value {
	pub const NIL_DISCRIMINANT: ValueDiscriminant = Value::Nil.discriminant();
	pub const STRING_DISCRIMINANT: ValueDiscriminant = Value::String(ArcStr::EMPTY).discriminant();
	pub const INTEGER_DISCRIMINANT: ValueDiscriminant = Value::Integer(0).discriminant();
	pub const ARRAY_DISCRIMINANT: ValueDiscriminant = Value::Array(Array::EMPTY).discriminant();

	const fn discriminant(self) -> ValueDiscriminant {
		let d = unsafe { mem::transmute::<_, ValueDiscriminant>(mem::discriminant(&self)) };
		mem::forget(self);
		d
	}
}

impl fmt::Display for Value {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		match self {
			Self::Nil => f.write_str("(nil)"),
			Self::String(s) => s.fmt(f),
			Self::Integer(s) => s.fmt(f),
			Self::Pipe(_) => f.write_str("<pipe>"),
			Self::Array(s) => s.fmt(f),
		}
	}
}

#[derive(Clone, Copy, Debug)]
pub enum TValue<'a> {
	Nil,
	String(TArcStr<'a>),
	Integer(isize),
	Pipe(TPipe<'a>),
	Array(TArray<'a>),
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
			Value::Pipe(s) => Self::Pipe(s.into()),
			Value::Array(s) => Self::Array(s.into()),
		}
	}
}

impl<'a> fmt::Display for TValue<'a> {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		match self {
			Self::Nil => f.write_str("(nil)"),
			Self::String(s) => s.fmt(f),
			Self::Integer(s) => s.fmt(f),
			Self::Pipe(_) => f.write_str("<pipe>"),
			Self::Array(s) => s.fmt(f),
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

	/// Return the value.
	///
	/// This returns a reference to avoid some issues with lifetimes.
	#[inline(always)]
	pub fn value(&self) -> &TValue<'a> {
		&self.value
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
	($vis:vis $qfn:ident = $fn:ident) => {
		$vis const $qfn: QFunction = QFunction({
			extern "C" fn g(argc: usize, argv: *const TValue, outc: usize, outv: *mut OutValue<'_>, inc: usize, inv: *const InValue<'_>) -> isize {
				unsafe {
					use core::slice::{from_raw_parts, from_raw_parts_mut};
					debug_assert!(!argv.is_null());
					debug_assert!(!outv.is_null());
					debug_assert!(!inv.is_null());
					let f = || $fn(from_raw_parts(argv, argc), from_raw_parts_mut(outv, outc), from_raw_parts(inv, inc));
					if cfg!(feature = "catch_unwind") {
						// EX_SOFTWARE is 70. Use -70 to indicate internal software in built-in
						// function for now.
						std::panic::catch_unwind(f).unwrap_or(-70)
					} else {
						f()
					}
				}
			}
			g
		});
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
		match i.name() {
			"" | "0" => {
				stdin = Stdio::piped();
				val = Some(i.value());
				break;
			}
			_ => (),
		}
	}
	let mut outv = None;
	let mut errv = None;
	for o in out {
		match o.name() {
			"" | "1" => (stdout, outv) = (Stdio::piped(), Some(o)),
			"2" => (stderr, errv) = (Stdio::piped(), Some(o)),
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

	if let Some(mut i) = cmd.stdin.take() {
		i.write_all(val.unwrap().to_string().as_bytes()).unwrap();
	}

	match (cmd.stdout.take(), cmd.stderr.take()) {
		(Some(o), Some(e)) => todo!("two streams"),
		(Some(mut o), None) => {
			let mut b = Default::default();
			o.read_to_end(&mut b).unwrap();
			outv.unwrap().set_value(Value::String((&b).into()));
		}
		(None, Some(mut e)) => {
			let mut b = Default::default();
			e.read_to_end(&mut b).unwrap();
			errv.unwrap().set_value(Value::String((&b).into()));
		}
		(None, None) => (),
	}
	cmd.wait().unwrap().code().unwrap_or(-1).try_into().unwrap()
}

pub fn split(args: &[TValue], out: &mut [OutValue], inv: &[InValue<'_>]) -> isize {
	let mut v = &b""[..];

	let sep = match args {
		[] => b"\n",
		[s] => match s {
			TValue::String(s) => s.as_ref(),
			_ => todo!("non-string separators"),
		},
		_ => todo!("multiple separators"),
	};

	for i in inv {
		match i.name() {
			"" | "0" => {
				v = match i.value() {
					TValue::String(s) => &s,
					v => todo!("split {:?}", v),
				}
			}
			_ => return -1, // TODO print an error message
		}
	}

	let mut out_index = None;
	for (i, o) in out.iter().enumerate() {
		match o.name() {
			"" | "1" => out_index = Some(i),
			_ => return -1, // TODO print an error message
		}
	}

	let mut vec = Vec::new();

	// This keeps the generic loop a little faster (and also is in itself faster)
	// TODO consider splitting on UTF-8 chars instead of bytes
	if sep == b"" {
		vec.extend(v.chunks(1).map(|s| Value::String(s.into())));
	} else {
		// TODO this is far from optimal
		let max = v.len().saturating_sub(sep.len());
		let mut i @ mut start = 0;
		while i <= max {
			if &v[i..][..sep.len()] == sep {
				vec.push(Value::String(v[start..i].into()));
				i += sep.len();
				start = i;
			} else {
				i += 1;
			}
		}
		vec.push(Value::String(v[start..].into()));
	}

	let array = Array::from(vec);

	if let Some(o) = out_index.map(|i| &mut out[i]) {
		o.set_value(Value::Array(array));
	} else {
		println!("{}", array);
	}

	0
}

wrap_ffi!(pub FFI_PRINT = print);
wrap_ffi!(pub FFI_EXEC  = exec );
wrap_ffi!(pub FFI_SPLIT = split);

#[cfg(test)]
mod test {
	use super::*;

	#[test]
	fn split() {
		let s = ArcStr::from("this is a\nstring with\nlinebreaks");
		let mut out = [OutValue {
			name: NonNull::from(&0),
			value: &mut Value::Nil,
		}];
		let inv = [InValue {
			name: NonNull::from(&0),
			value: TValue::String((&s).into()),
		}];
		assert_eq!(super::split(&[], &mut out, &inv), 0);
		match &out[0].value {
			Value::Array(a) => {
				assert_eq!(a.len(), 3);
				for (x, y) in a.iter().zip(&["this is a", "string with", "linebreaks"]) {
					match x {
						Value::String(x) => assert_eq!(&**x, y.as_bytes()),
						x => panic!("expected string, got {:?}", x),
					}
				}
			}
			v => panic!("expected array, got {:?}", v),
		}
	}
}
