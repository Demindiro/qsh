use super::{
	arc_array::{ArcArray, TArcArray},
	Value,
};
use core::fmt;
use core::alloc::Layout;
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
	#[inline(always)]
	fn from(s: &[Value]) -> Self {
		Self(s.into())
	}
}

impl<R> From<&R> for Array
where
	R: AsRef<[Value]>,
{
	#[inline(always)]
	fn from(s: &R) -> Self {
		Self(s.as_ref().into())
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
