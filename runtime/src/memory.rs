use std::alloc::{self, Layout};
use std::sync::atomic::{AtomicUsize, Ordering};

pub trait Allocator {
    fn alloc(&self, size: usize, align: usize) -> *mut u8;
    fn dealloc(&self, ptr: *mut u8, size: usize, align: usize);
}

pub struct ArenaAllocator {
    buffer: Vec<u8>,
    offset: AtomicUsize,
}

impl ArenaAllocator {
    pub fn new(capacity: usize) -> Self {
        ArenaAllocator {
            buffer: vec![0u8; capacity],
            offset: AtomicUsize::new(0),
        }
    }

    pub fn used(&self) -> usize {
        self.offset.load(Ordering::Relaxed)
    }

    pub fn capacity(&self) -> usize {
        self.buffer.len()
    }

    pub fn remaining(&self) -> usize {
        self.buffer.len().saturating_sub(self.used())
    }

    pub fn reset(&self) {
        self.offset.store(0, Ordering::Relaxed);
    }
}

impl Allocator for ArenaAllocator {
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

    fn dealloc(&self, _ptr: *mut u8, _size: usize, _align: usize) {}
}

pub struct GlobalAllocator;

impl Allocator for GlobalAllocator {
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

    fn dealloc(&self, ptr: *mut u8, size: usize, align: usize) {
        if ptr.is_null() || size == 0 {
            return;
        }
        let align = align.max(1);
        if let Ok(layout) = Layout::from_size_align(size, align) {
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
