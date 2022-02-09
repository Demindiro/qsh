use core::alloc::Layout;
use core::iter::TrustedLen;
use core::marker::PhantomData;
use core::ops::Deref;
use core::ptr::{self, NonNull};
use core::sync::atomic::{AtomicUsize, Ordering};
use std::alloc::{alloc, dealloc};

#[repr(C)]
struct ArcArrayInner<T> {
	refcount: AtomicUsize,
	size: usize,
	buffer: [T; 0],
}

/// A reference-counted array usable with FFI.
///
/// Note that this string may not be valid UTF-8.
#[repr(transparent)]
pub(crate) struct ArcArray<T> {
	inner: NonNull<ArcArrayInner<T>>,
	_marker: PhantomData<ArcArrayInner<T>>,
}

impl<T> ArcArray<T> {
	// For internal use only, as this may cause UB if used improperly.
	// inner may *never* be dereferenced.
	pub(super) const EMPTY: Self = Self {
		// This is valid, yet referencing a const is bad because the const becomes dangling?
		inner: NonNull::dangling(),
		_marker: PhantomData,
	};

	#[inline]
	fn layout(len: usize) -> Layout {
		Layout::new::<ArcArrayInner<T>>()
			.extend(Layout::array::<T>(len).unwrap())
			.unwrap()
			.0
	}

	/// A variant of layout that will call [`core::intrinsics::abort`] if the layout cannot be
	/// constructed.
	#[inline]
	fn fast_layout(len: usize) -> Layout {
		if let Ok(layout) = Layout::array::<T>(len) {
			if let Ok(layout) = Layout::new::<ArcArrayInner<T>>().extend(layout) {
				return layout.0;
			}
		}
		// The size being incorrect is very unlikely but still possible. abort() is a
		// relatively cheap way to guard against UB with minimal bloat.
		core::intrinsics::abort();
	}

	/// # Safety
	///
	/// This object may not be reused after this call.
	// Never inline to prevent bloat when inlining drop()
	#[inline(never)]
	unsafe fn dealloc(&mut self) {
		for i in 0..self.len() {
			// SAFETY:
			// The object at index i is valid.
			// This is the first time this object is dropped.
			unsafe {
				ptr::drop_in_place(self.inner.as_mut().buffer.as_mut_ptr().add(i));
			}
		}
		dealloc(
			self.inner.as_ptr().cast(),
			Self::fast_layout(self.inner.as_ref().size),
		)
	}
}

impl<T> Clone for ArcArray<T> {
	#[inline]
	fn clone(&self) -> Self {
		// SAFETY: self.inner is a valid pointer
		unsafe {
			self.inner.as_ref().refcount.fetch_add(1, Ordering::Relaxed);
			Self {
				inner: self.inner,
				_marker: PhantomData,
			}
		}
	}
}

impl<T> Drop for ArcArray<T> {
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

impl<T, I> From<I> for ArcArray<T>
where
	I: Iterator<Item = T> + TrustedLen,
{
	#[inline(always)]
	fn from(iter: I) -> Self {
		unsafe {
			let inner = alloc(Self::layout(iter.size_hint().0)).cast::<ArcArrayInner<T>>();
			inner.write(ArcArrayInner {
				size: iter.size_hint().0,
				refcount: AtomicUsize::new(0),
				buffer: [],
			});
			for (i, e) in iter.enumerate() {
				ptr::write(inner.add(1).cast::<T>().add(i), e);
			}
			Self {
				inner: NonNull::new_unchecked(inner),
				_marker: PhantomData,
			}
		}
	}
}

impl<T> AsRef<[T]> for ArcArray<T> {
	#[inline]
	fn as_ref(&self) -> &[T] {
		// SAFETY: self.inner is a valid pointer and size matches the real length of the buffer.
		unsafe {
			let inner = self.inner.as_ref();
			core::slice::from_raw_parts(inner.buffer.as_ptr(), inner.size)
		}
	}
}

impl<T> Deref for ArcArray<T> {
	type Target = [T];

	#[inline]
	fn deref(&self) -> &Self::Target {
		self.as_ref()
	}
}

/// A temporary reference to an [`ArcArray`].
///
/// This type avoids an extra indirection while still maintaining lifetime invariants.
#[derive(Clone)]
pub(crate) struct TArcArray<'a, T> {
	inner: NonNull<ArcArrayInner<T>>,
	_marker: PhantomData<&'a ArcArray<T>>,
}

impl<'a, T> Copy for TArcArray<'a, T> where T: Clone {}

impl<'a, T> From<&'a ArcArray<T>> for TArcArray<'a, T> {
	#[inline]
	fn from(s: &'a ArcArray<T>) -> Self {
		TArcArray {
			inner: s.inner,
			_marker: PhantomData,
		}
	}
}

impl<'a, T> AsRef<ArcArray<T>> for TArcArray<'a, T> {
	#[inline]
	fn as_ref(&self) -> &ArcArray<T> {
		// SAFETY: ArcArray is transparent
		unsafe { &*(&self.inner as *const NonNull<ArcArrayInner<T>> as *const ArcArray<T>) }
	}
}

impl<'a, T> Deref for TArcArray<'a, T> {
	type Target = ArcArray<T>;

	#[inline]
	fn deref(&self) -> &Self::Target {
		self.as_ref()
	}
}
