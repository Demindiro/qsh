use super::arc_array::{ArcArray, TArcArray};
use core::alloc::Layout;
use core::fmt;
use core::marker::PhantomData;
use core::ops::Deref;
use core::ptr::{self, NonNull};
use core::sync::atomic::{AtomicUsize, Ordering};
use std::alloc::{alloc, dealloc};

/// A reference-counted string usable with FFI.
///
/// Note that this string may not be valid UTF-8.
#[derive(Clone)]
#[repr(transparent)]
pub struct ArcStr(ArcArray<u8>);

impl From<&[u8]> for ArcStr {
	#[inline(always)]
	fn from(s: &[u8]) -> Self {
		Self(s.iter().copied().into())
	}
}

impl<R> From<&R> for ArcStr
where
	R: AsRef<[u8]>,
{
	#[inline(always)]
	fn from(s: &R) -> Self {
		s.as_ref().into()
	}
}

impl From<&str> for ArcStr {
	#[inline(always)]
	fn from(s: &str) -> Self {
		s.as_bytes().into()
	}
}

impl AsRef<[u8]> for ArcStr {
	#[inline(always)]
	fn as_ref(&self) -> &[u8] {
		self.0.as_ref()
	}
}

impl Deref for ArcStr {
	type Target = [u8];

	#[inline(always)]
	fn deref(&self) -> &Self::Target {
		self.0.deref()
	}
}

impl fmt::Debug for ArcStr {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		fmt_debug(self, f)
	}
}

impl fmt::Display for ArcStr {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		fmt_display(self, f)
	}
}

/// A temporary reference to an [`ArcStr`].
///
/// This type avoids an extra indirection while still maintaining lifetime invariants.
#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct TArcStr<'a>(TArcArray<'a, u8>);

impl<'a> TArcStr<'a> {
	/// Increase the reference count and take ownership of the string.
	#[inline]
	pub fn upgrade(self) -> ArcStr {
		ArcStr((&*self.0).clone())
	}
}

impl<'a> From<&'a ArcStr> for TArcStr<'a> {
	#[inline(always)]
	fn from(s: &'a ArcStr) -> Self {
		Self((&s.0).into())
	}
}

impl<'a> AsRef<[u8]> for TArcStr<'a> {
	#[inline(always)]
	fn as_ref(&self) -> &[u8] {
		self.0.as_ref()
	}
}

impl<'a> Deref for TArcStr<'a> {
	type Target = [u8];

	#[inline(always)]
	fn deref(&self) -> &Self::Target {
		self.0.deref()
	}
}

impl fmt::Debug for TArcStr<'_> {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		fmt_debug(self, f)
	}
}

impl fmt::Display for TArcStr<'_> {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		fmt_display(self, f)
	}
}

fn fmt_debug(s: &[u8], f: &mut fmt::Formatter) -> fmt::Result {
	use fmt::Debug;
	String::from_utf8_lossy(s.as_ref())
		.escape_debug()
		.collect::<String>()
		.fmt(f)
}

fn fmt_display(s: &[u8], f: &mut fmt::Formatter) -> fmt::Result {
	use fmt::Display;
	String::from_utf8_lossy(s.as_ref()).fmt(f)
}
