use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, Mutex};

const INITIAL_CAPACITY: usize = 32;

/// A work-stealing deque with a single owner and many stealers.
///
/// The owner pushes and pops at the bottom end while other threads steal from
/// the top end, so contention stays low. The buffer grows on demand and never
/// shrinks.
pub struct ChaseLevDeque<T> {
    buffer: Arc<Mutex<Vec<Option<T>>>>,
    bottom: AtomicUsize,
    top: AtomicUsize,
}

impl<T> ChaseLevDeque<T> {
    /// Creates an empty deque with the default initial capacity.
    pub fn new() -> Self {
        let mut buf = Vec::with_capacity(INITIAL_CAPACITY);
        for _ in 0..INITIAL_CAPACITY {
            buf.push(None);
        }
        ChaseLevDeque {
            buffer: Arc::new(Mutex::new(buf)),
            bottom: AtomicUsize::new(0),
            top: AtomicUsize::new(0),
        }
    }

    /// Creates an empty deque sized to hold `capacity` elements.
    ///
    /// Capacities below 8 are raised to 8.
    pub fn with_capacity(capacity: usize) -> Self {
        let cap = capacity.max(8);
        let mut buf = Vec::with_capacity(cap);
        for _ in 0..cap {
            buf.push(None);
        }
        ChaseLevDeque {
            buffer: Arc::new(Mutex::new(buf)),
            bottom: AtomicUsize::new(0),
            top: AtomicUsize::new(0),
        }
    }

    fn grow(&self) {
        let mut buffer = self.buffer.lock().unwrap();
        let old_len = buffer.len();
        let new_len = old_len * 2;
        buffer.resize_with(new_len, || None);
    }

    /// Adds `value` to the owner (bottom) end of the deque.
    ///
    /// The buffer is doubled first if the deque is full.
    pub fn push(&self, value: T) {
        let b = self.bottom.load(Ordering::Relaxed);
        let t = self.top.load(Ordering::Relaxed);
        {
            let buffer = self.buffer.lock().unwrap();
            if b - t >= buffer.len() {
                drop(buffer);
                self.grow();
            }
        }
        let mut buffer = self.buffer.lock().unwrap();
        let idx = b % buffer.len();
        buffer[idx] = Some(value);
        self.bottom.store(b + 1, Ordering::Relaxed);
    }

    /// Removes the most recently pushed value from the owner (bottom) end.
    ///
    /// Returns `None` when the deque is empty.
    pub fn pop(&self) -> Option<T> {
        let b = self.bottom.load(Ordering::Relaxed);
        let t = self.top.load(Ordering::Relaxed);
        if b <= t {
            return None;
        }
        let mut buffer = self.buffer.lock().unwrap();
        let idx = (b - 1) % buffer.len();
        let value = buffer[idx].take();
        self.bottom.store(b - 1, Ordering::Relaxed);
        value
    }

    /// Removes the oldest value from the stealable (top) end of the deque.
    ///
    /// Returns `None` when no value is available to steal.
    pub fn steal(&self) -> Option<T> {
        let t = self.top.load(Ordering::Relaxed);
        let b = self.bottom.load(Ordering::Relaxed);
        if t >= b {
            return None;
        }
        let mut buffer = self.buffer.lock().unwrap();
        let idx = t % buffer.len();
        let value = buffer[idx].take();
        if value.is_some() {
            self.top.store(t + 1, Ordering::Relaxed);
        }
        value
    }

    /// Returns the number of elements currently buffered.
    ///
    /// The result is a snapshot and may be stale immediately, since other
    /// threads may push or steal concurrently.
    pub fn len(&self) -> usize {
        let b = self.bottom.load(Ordering::Relaxed);
        let t = self.top.load(Ordering::Relaxed);
        b.saturating_sub(t)
    }

    /// Returns `true` if no elements are buffered.
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

impl<T> Clone for ChaseLevDeque<T> {
    fn clone(&self) -> Self {
        ChaseLevDeque {
            buffer: Arc::clone(&self.buffer),
            bottom: AtomicUsize::new(self.bottom.load(Ordering::Relaxed)),
            top: AtomicUsize::new(self.top.load(Ordering::Relaxed)),
        }
    }
}

impl<T> Default for ChaseLevDeque<T> {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_push_pop_lifo() {
        let deque: ChaseLevDeque<i32> = ChaseLevDeque::new();
        deque.push(1);
        deque.push(2);
        deque.push(3);
        assert_eq!(deque.pop(), Some(3));
        assert_eq!(deque.pop(), Some(2));
        assert_eq!(deque.pop(), Some(1));
        assert_eq!(deque.pop(), None);
    }

    #[test]
    fn test_steal_fifo() {
        let deque: ChaseLevDeque<i32> = ChaseLevDeque::new();
        deque.push(10);
        deque.push(20);
        deque.push(30);
        assert_eq!(deque.steal(), Some(10));
        assert_eq!(deque.steal(), Some(20));
        assert_eq!(deque.pop(), Some(30));
        assert_eq!(deque.pop(), None);
    }

    #[test]
    fn test_steal_and_pop_interleaved() {
        let deque: ChaseLevDeque<i32> = ChaseLevDeque::new();
        deque.push(1);
        deque.push(2);
        deque.push(3);
        assert_eq!(deque.steal(), Some(1));
        assert_eq!(deque.pop(), Some(3));
        assert_eq!(deque.pop(), Some(2));
        assert_eq!(deque.steal(), None);
        assert_eq!(deque.pop(), None);
    }

    #[test]
    fn test_empty() {
        let deque: ChaseLevDeque<i32> = ChaseLevDeque::new();
        assert!(deque.is_empty());
        assert_eq!(deque.len(), 0);
        assert_eq!(deque.pop(), None);
        assert_eq!(deque.steal(), None);
    }

    #[test]
    fn test_grow() {
        let deque: ChaseLevDeque<i32> = ChaseLevDeque::with_capacity(4);
        for i in 0..100 {
            deque.push(i);
        }
        assert_eq!(deque.len(), 100);
        for i in (0..100).rev() {
            assert_eq!(deque.pop(), Some(i));
        }
    }
}
