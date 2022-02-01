use core::alloc::Layout;
use core::fmt;
use core::marker::PhantomData;
use core::ops::Deref;
use core::ptr::{self, NonNull};
use core::sync::atomic::{AtomicUsize, Ordering};
use std::alloc::{alloc, dealloc};

#[repr(C)]
struct ArcStrInner {
	refcount: AtomicUsize,
	size: usize,
	buffer: [u8; 0],
}

/// A reference-counted string usable with FFI.
///
/// Note that this string may not be valid UTF-8.
#[repr(transparent)]
pub struct ArcStr {
	inner: NonNull<ArcStrInner>,
}

impl ArcStr {
	#[inline]
	fn layout(len: usize) -> Layout {
		Layout::new::<ArcStrInner>()
			.extend(Layout::array::<u8>(len).unwrap())
			.unwrap()
			.0
	}

	/// # Safety
	///
	/// This object may not be reused after this call.
	// Never inline to prevent bloat when inlining drop()
	#[inline(never)]
	unsafe fn dealloc(&mut self) {
		dealloc(
			self.inner.as_ptr().cast(),
			Self::layout(self.inner.as_ref().size),
		)
	}
}

impl Clone for ArcStr {
	#[inline]
	fn clone(&self) -> Self {
		// SAFETY: self.inner is a valid pointer
		unsafe {
			self.inner.as_ref().refcount.fetch_add(1, Ordering::Relaxed);
			Self { inner: self.inner }
		}
	}
}

impl Drop for ArcStr {
	#[inline]
	fn drop(&mut self) {
		// SAFETY: self.inner is a valid pointer
		unsafe {
			if self.inner.as_ref().refcount.fetch_sub(1, Ordering::Relaxed) == 0 {
				self.dealloc();
			}
		}
	}
}

impl From<&[u8]> for ArcStr {
	fn from(s: &[u8]) -> Self {
		unsafe {
			let inner = alloc(Self::layout(s.len())).cast::<ArcStrInner>();
			inner.write(ArcStrInner {
				size: s.len(),
				refcount: AtomicUsize::new(0),
				buffer: [],
			});
			ptr::copy_nonoverlapping(s.as_ptr(), inner.add(1).cast::<u8>(), s.len());
			Self {
				inner: NonNull::new_unchecked(inner),
			}
		}
	}
}

impl<R> From<&R> for ArcStr
where
	R: AsRef<[u8]>,
{
	fn from(s: &R) -> Self {
		s.as_ref().into()
	}
}

impl From<&str> for ArcStr {
	#[inline]
	fn from(s: &str) -> Self {
		s.as_bytes().into()
	}
}

impl AsRef<[u8]> for ArcStr {
	#[inline]
	fn as_ref(&self) -> &[u8] {
		// SAFETY: self.inner is a valid pointer and size matches the real length of the buffer.
		unsafe {
			let inner = self.inner.as_ref();
			core::slice::from_raw_parts(inner.buffer.as_ptr(), inner.size)
		}
	}
}

impl Deref for ArcStr {
	type Target = [u8];

	#[inline]
	fn deref(&self) -> &Self::Target {
		self.as_ref()
	}
}

impl fmt::Debug for ArcStr {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		String::from_utf8_lossy(self.as_ref())
			.escape_debug()
			.collect::<String>()
			.fmt(f)
	}
}

impl fmt::Display for ArcStr {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		String::from_utf8_lossy(self.as_ref()).fmt(f)
	}
}

/// A temporary reference to an [`ArcStr`].
///
/// This type avoids an extra indirection while still maintaining lifetime invariants.
#[derive(Clone, Copy)]
pub struct TArcStr<'a> {
	inner: NonNull<ArcStrInner>,
	_marker: PhantomData<&'a ArcStr>,
}

impl<'a> From<&'a ArcStr> for TArcStr<'a> {
	#[inline]
	fn from(s: &'a ArcStr) -> Self {
		TArcStr {
			inner: s.inner,
			_marker: PhantomData,
		}
	}
}

impl<'a> AsRef<ArcStr> for TArcStr<'a> {
	#[inline]
	fn as_ref(&self) -> &ArcStr {
		// SAFETY: ArcStr is transparent
		unsafe { &*(&self.inner as *const NonNull<ArcStrInner> as *const ArcStr) }
	}
}

impl<'a> Deref for TArcStr<'a> {
	type Target = ArcStr;

	#[inline]
	fn deref(&self) -> &Self::Target {
		self.as_ref()
	}
}

impl<'a> fmt::Debug for TArcStr<'a> {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		self.as_ref().fmt(f)
	}
}

impl<'a> fmt::Display for TArcStr<'a> {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		self.as_ref().fmt(f)
	}
}
