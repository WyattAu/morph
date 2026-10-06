use std::alloc::{self, Layout};
use std::sync::atomic::{AtomicUsize, Ordering};

/// A bump allocator interface used by the runtime for raw memory blocks.
///
/// Implementations hand out raw pointers, so callers are responsible for
/// pairing every successful [`Allocator::alloc`] with a [`Allocator::dealloc`]
/// carrying the same `size` and `align`.
pub trait Allocator {
    /// Reserves `size` bytes aligned to `align`.
    ///
    /// Returns a null pointer when `size` is `0` or the request cannot be
    /// satisfied; the caller must treat null as failure and must not
    /// [`Allocator::dealloc`] it.
    fn alloc(&self, size: usize, align: usize) -> *mut u8;

    /// Returns a block previously obtained from [`Allocator::alloc`].
    ///
    /// `size` and `align` must match the values used to allocate `ptr`.
    fn dealloc(&self, ptr: *mut u8, size: usize, align: usize);
}

/// A fixed-capacity bump allocator supporting lock-free concurrent allocation.
///
/// The arena owns one heap buffer and hands out ever-increasing offsets. It
/// never reclaims individual blocks; [`ArenaAllocator::reset`] rewinds the bump
/// pointer to make the whole buffer available again.
pub struct ArenaAllocator {
    buffer: Vec<u8>,
    offset: AtomicUsize,
}

impl ArenaAllocator {
    /// Creates an arena backed by a zeroed buffer of `capacity` bytes.
    pub fn new(capacity: usize) -> Self {
        ArenaAllocator {
            buffer: vec![0u8; capacity],
            offset: AtomicUsize::new(0),
        }
    }

    /// Returns the number of bytes currently handed out.
    pub fn used(&self) -> usize {
        self.offset.load(Ordering::Relaxed)
    }

    /// Returns the total size of the backing buffer in bytes.
    pub fn capacity(&self) -> usize {
        self.buffer.len()
    }

    /// Returns how many bytes are still available without a [`ArenaAllocator::reset`].
    pub fn remaining(&self) -> usize {
        self.buffer.len().saturating_sub(self.used())
    }

    /// Rewinds the bump pointer so the entire buffer becomes available again.
    ///
    /// Any pointer previously returned by [`Allocator::alloc`] is invalidated;
    /// callers must not use or deallocate those blocks afterwards.
    pub fn reset(&self) {
        self.offset.store(0, Ordering::Relaxed);
    }
}

impl Allocator for ArenaAllocator {
    /// Bump-allocates `size` bytes aligned to `align`.
    ///
    /// Returns a null pointer if `size` is `0` or the request would exceed the
    /// arena capacity. Blocks are never individually reclaimed.
    fn alloc(&self, size: usize, align: usize) -> *mut u8 {
        if size == 0 {
            return std::ptr::null_mut();
        }
        let align = align.max(1);
        loop {
            let current = self.offset.load(Ordering::Relaxed);
            let aligned = (current + align - 1) & !(align - 1);
            let new_offset = aligned + size;
            if new_offset > self.buffer.len() {
                return std::ptr::null_mut();
            }
            if self
                .offset
                .compare_exchange_weak(current, new_offset, Ordering::AcqRel, Ordering::Relaxed)
                .is_ok()
            {
                // SAFETY: aligned + size <= buffer.len(), and the buffer is
                // heap-allocated so its base pointer is stable.
                return unsafe { self.buffer.as_ptr().add(aligned) as *mut u8 };
            }
        }
    }

    /// No-op: the arena reclaims memory only through [`ArenaAllocator::reset`].
    fn dealloc(&self, _ptr: *mut u8, _size: usize, _align: usize) {}
}

/// An [`Allocator`] backed by the global `std` allocator.
pub struct GlobalAllocator;

impl Allocator for GlobalAllocator {
    /// Allocates `size` bytes aligned to `align` in the global heap.
    ///
    /// Returns a null pointer when `size` is `0` or when `size` and `align`
    /// cannot form a valid [`Layout`].
    fn alloc(&self, size: usize, align: usize) -> *mut u8 {
        if size == 0 {
            return std::ptr::null_mut();
        }
        let align = align.max(1);
        match Layout::from_size_align(size, align) {
            Ok(layout) => unsafe { alloc::alloc(layout) },
            Err(_) => std::ptr::null_mut(),
        }
    }

    /// Frees a block back to the global heap.
    ///
    /// Null pointers and zero-sized requests are ignored, as are requests whose
    /// `size`/`align` do not form a valid [`Layout`].
    #[allow(clippy::not_unsafe_ptr_arg_deref)]
    fn dealloc(&self, ptr: *mut u8, size: usize, align: usize) {
        if ptr.is_null() || size == 0 {
            return;
        }
        let align = align.max(1);
        if let Ok(layout) = Layout::from_size_align(size, align) {
            // SAFETY: ptr was allocated by GlobalAllocator::alloc with the same size/align.
            unsafe { alloc::dealloc(ptr, layout) }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_arena_basic_alloc() {
        let arena = ArenaAllocator::new(1024);
        let p1 = arena.alloc(16, 8);
        assert!(!p1.is_null());
        assert_eq!(arena.used(), 16);
        let p2 = arena.alloc(32, 8);
        assert!(!p2.is_null());
        assert_eq!(arena.used(), 48);
    }

    #[test]
    fn test_arena_alignment() {
        let arena = ArenaAllocator::new(1024);
        let p1 = arena.alloc(1, 1);
        assert!(!p1.is_null());
        let p2 = arena.alloc(1, 16);
        assert!(!p2.is_null());
        assert_eq!((p2 as usize) % 16, 0);
    }

    #[test]
    fn test_arena_overflow() {
        let arena = ArenaAllocator::new(32);
        let p1 = arena.alloc(16, 1);
        assert!(!p1.is_null());
        let p2 = arena.alloc(32, 1);
        assert!(p2.is_null());
    }

    #[test]
    fn test_arena_reset() {
        let arena = ArenaAllocator::new(1024);
        arena.alloc(100, 1);
        assert_eq!(arena.used(), 100);
        arena.reset();
        assert_eq!(arena.used(), 0);
        let p = arena.alloc(100, 1);
        assert!(!p.is_null());
    }

    #[test]
    fn test_arena_zero_size() {
        let arena = ArenaAllocator::new(1024);
        assert!(arena.alloc(0, 1).is_null());
    }

    #[test]
    fn test_global_allocator() {
        let ga = GlobalAllocator;
        let p = ga.alloc(64, 8);
        assert!(!p.is_null());
        ga.dealloc(p, 64, 8);
    }
}
