use core::marker::PhantomData;
use core::ops::Deref;
use core::ptr::NonNull;
use core::sync::atomic::{AtomicUsize, Ordering};
use std::io::{self, Read};
use std::process::{ChildStderr, ChildStdout};
use std::sync::{Mutex, MutexGuard};

enum Input {
	Out(ChildStdout),
	Err(ChildStderr),
}

#[repr(C)]
struct InnerPipe {
	refcount: AtomicUsize,
	input: Mutex<Input>,
}

#[derive(Debug)]
#[repr(transparent)]
pub struct Pipe {
	inner: NonNull<InnerPipe>,
}

impl Pipe {
	/// Lock a pipe for reading.
	pub fn lock_read(&self) -> PipeReadGuard {
		// SAFETY: self.inner is a valid pointer.
		unsafe {
			PipeReadGuard {
				input: self.inner.as_ref().input.lock().unwrap(),
			}
		}
	}

	/// # Safety
	///
	/// This function may only be called once. There may also not be
	/// any other references to the [`InnerPipe`].
	// Never inline to keep inlined drop small & efficient.
	#[inline(never)]
	unsafe fn dealloc(&mut self) {
		Box::from_raw(self.inner.as_ptr());
	}
}

impl Clone for Pipe {
	#[inline(always)]
	fn clone(&self) -> Self {
		unsafe {
			self.inner.as_ref().refcount.fetch_add(1, Ordering::Relaxed);
			Self { inner: self.inner }
		}
	}
}

impl Drop for Pipe {
	#[inline(always)]
	fn drop(&mut self) {
		unsafe {
			if self.inner.as_ref().refcount.fetch_sub(1, Ordering::Relaxed) == 0 {
				self.dealloc();
			}
		}
	}
}

impl From<ChildStdout> for Pipe {
	fn from(c: ChildStdout) -> Self {
		let p = InnerPipe {
			refcount: AtomicUsize::new(0),
			input: Mutex::new(Input::Out(c)),
		};
		Self {
			inner: NonNull::new(Box::into_raw(Box::new(p))).unwrap(),
		}
	}
}

impl From<ChildStderr> for Pipe {
	fn from(c: ChildStderr) -> Self {
		let p = InnerPipe {
			refcount: AtomicUsize::new(0),
			input: Mutex::new(Input::Err(c)),
		};
		Self {
			inner: NonNull::new(Box::into_raw(Box::new(p))).unwrap(),
		}
	}
}

pub struct PipeReadGuard<'a> {
	input: MutexGuard<'a, Input>,
}

impl Read for PipeReadGuard<'_> {
	fn read(&mut self, out: &mut [u8]) -> io::Result<usize> {
		match &mut *self.input {
			Input::Out(o) => o.read(out),
			Input::Err(o) => o.read(out),
		}
	}
}

/// A temporary reference to a [`Pipe`].
///
/// This type avoids an extra indirection while still maintaining lifetime invariants.
#[derive(Clone, Copy, Debug)]
#[repr(transparent)]
pub struct TPipe<'a> {
	inner: NonNull<InnerPipe>,
	_marker: PhantomData<&'a Pipe>,
}

impl<'a> From<&'a Pipe> for TPipe<'a> {
	#[inline]
	fn from(s: &'a Pipe) -> Self {
		TPipe {
			inner: s.inner,
			_marker: PhantomData,
		}
	}
}

impl<'a> AsRef<Pipe> for TPipe<'a> {
	#[inline]
	fn as_ref(&self) -> &Pipe {
		// SAFETY: Pipe is transparent
		unsafe { &*(&self.inner as *const NonNull<InnerPipe> as *const Pipe) }
	}
}

impl<'a> Deref for TPipe<'a> {
	type Target = Pipe;

	#[inline]
	fn deref(&self) -> &Self::Target {
		self.as_ref()
	}
}
