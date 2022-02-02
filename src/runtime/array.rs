use super::{
	arc_array::{ArcArray, TArcArray},
	Value,
};
use core::alloc::Layout;
use core::fmt;
use core::marker::PhantomData;
use core::ops::Deref;
use core::ptr::NonNull;
use core::sync::atomic::{AtomicUsize, Ordering};
use std::alloc::{alloc, dealloc};
use std::io::{self, Read};
use std::process::{ChildStderr, ChildStdin, ChildStdout};
use std::sync::{Mutex, MutexGuard};

/// A fixed-sized array of [`Value`]s.
#[derive(Clone)]
#[repr(transparent)]
pub struct Array(ArcArray<Value>);

impl From<&[Value]> for Array {
	#[inline]
	fn from(s: &[Value]) -> Self {
		Self(s.iter().cloned().into())
	}
}

impl<R> From<&R> for Array
where
	R: AsRef<[Value]>,
{
	#[inline(always)]
	fn from(s: &R) -> Self {
		s.as_ref().into()
	}
}

impl From<Vec<Value>> for Array {
	#[inline]
	fn from(s: Vec<Value>) -> Self {
		let len = s.len();
		Self(s.into_iter().take(len).into())
	}
}

impl AsRef<[Value]> for Array {
	#[inline(always)]
	fn as_ref(&self) -> &[Value] {
		self.0.as_ref()
	}
}

impl Deref for Array {
	type Target = [Value];

	#[inline(always)]
	fn deref(&self) -> &Self::Target {
		self.0.deref()
	}
}

impl fmt::Debug for Array {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		self.0.fmt(f)
	}
}

impl fmt::Display for Array {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		fmt_display(self.as_ref(), f)
	}
}

/// A temporary reference to an [`Array`].
///
/// This type avoids an extra indirection while still maintaining lifetime invariants.
#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct TArray<'a>(TArcArray<'a, Value>);

impl TArray<'_> {
	/// Increase the reference count and take ownership of the array.
	#[inline]
	pub fn upgrade(self) -> Array {
		Array((&*self.0).clone())
	}
}

impl<'a> From<&'a Array> for TArray<'a> {
	#[inline(always)]
	fn from(s: &'a Array) -> Self {
		Self((&s.0).into())
	}
}

impl<'a> AsRef<[Value]> for TArray<'a> {
	#[inline(always)]
	fn as_ref(&self) -> &[Value] {
		self.0.as_ref()
	}
}

impl<'a> Deref for TArray<'a> {
	type Target = [Value];

	#[inline(always)]
	fn deref(&self) -> &Self::Target {
		self.as_ref()
	}
}

impl<'a> fmt::Debug for TArray<'a> {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		self.0.fmt(f)
	}
}

impl<'a> fmt::Display for TArray<'a> {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		fmt_display(self.as_ref(), f)
	}
}

fn fmt_display(a: &[Value], f: &mut fmt::Formatter) -> fmt::Result {
	use fmt::Display;
	f.write_str("[ ")?;
	for (i, e) in a.into_iter().enumerate() {
		f.write_str("\"")?;
		e.to_string().escape_default().fmt(f)?;
		f.write_str("\" ")?;
	}
	f.write_str("]")
}
