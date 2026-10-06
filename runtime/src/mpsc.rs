use std::collections::VecDeque;
use std::sync::{Arc, Mutex};

/// A multi-producer, single-consumer queue backed by a shared FIFO buffer.
///
/// Cloning the queue yields another handle to the *same* buffer, which is how a
/// queue is handed to producers. Ordering is guaranteed FIFO within the buffer,
/// but interleaving between concurrent producers is unspecified.
pub struct MpscQueue<T> {
    inner: Arc<Mutex<VecDeque<T>>>,
}

impl<T> MpscQueue<T> {
    /// Creates an empty queue.
    pub fn new() -> Self {
        MpscQueue {
            inner: Arc::new(Mutex::new(VecDeque::new())),
        }
    }

    /// Appends `value` to the back of the queue.
    pub fn push(&self, value: T) {
        self.inner.lock().unwrap().push_back(value);
    }

    /// Removes and returns the front element, or `None` if the queue is empty.
    pub fn pop(&self) -> Option<T> {
        self.inner.lock().unwrap().pop_front()
    }

    /// Returns the number of buffered elements.
    pub fn len(&self) -> usize {
        self.inner.lock().unwrap().len()
    }

    /// Returns `true` if no elements are buffered.
    pub fn is_empty(&self) -> bool {
        self.inner.lock().unwrap().is_empty()
    }

    /// Returns a lock guard over the queue if it is non-empty, otherwise `None`.
    ///
    /// The returned guard keeps the queue locked until it is dropped, so no
    /// other thread can push or pop for the guard's lifetime.
    pub fn peek(&self) -> Option<std::sync::MutexGuard<'_, VecDeque<T>>> {
        let guard = self.inner.lock().unwrap();
        if guard.is_empty() {
            None
        } else {
            Some(guard)
        }
    }

    /// Discards all buffered elements.
    pub fn clear(&self) {
        self.inner.lock().unwrap().clear();
    }
}

impl<T> Clone for MpscQueue<T> {
    /// Clones the handle; both handles refer to the same underlying buffer.
    fn clone(&self) -> Self {
        MpscQueue {
            inner: Arc::clone(&self.inner),
        }
    }
}

impl<T> Default for MpscQueue<T> {
    /// Creates an empty queue, exactly as [`MpscQueue::new`] does.
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::thread;

    #[test]
    fn test_mpsc_push_pop() {
        let q: MpscQueue<i32> = MpscQueue::new();
        assert!(q.is_empty());
        q.push(1);
        q.push(2);
        q.push(3);
        assert_eq!(q.len(), 3);
        assert_eq!(q.pop(), Some(1));
        assert_eq!(q.pop(), Some(2));
        assert_eq!(q.pop(), Some(3));
        assert_eq!(q.pop(), None);
        assert!(q.is_empty());
    }

    #[test]
    fn test_mpsc_fifo_order() {
        let q: MpscQueue<&str> = MpscQueue::new();
        q.push("first");
        q.push("second");
        q.push("third");
        assert_eq!(q.pop(), Some("first"));
        assert_eq!(q.pop(), Some("second"));
        assert_eq!(q.pop(), Some("third"));
    }

    #[test]
    fn test_mpsc_multi_producer() {
        let q: MpscQueue<usize> = MpscQueue::new();
        let n: usize = 100;

        let mut handles = Vec::new();
        for i in 0..4 {
            let qc = q.clone();
            handles.push(thread::spawn(move || {
                for j in 0..n {
                    qc.push(i * n + j);
                }
            }));
        }

        for h in handles {
            h.join().unwrap();
        }

        assert_eq!(q.len(), 4 * n);

        let mut values: Vec<usize> = Vec::new();
        while let Some(v) = q.pop() {
            values.push(v);
        }
        assert_eq!(values.len(), 4 * n);
    }

    #[test]
    fn test_mpsc_clone_shares_state() {
        let q1: MpscQueue<i32> = MpscQueue::new();
        let q2 = q1.clone();
        q1.push(42);
        assert_eq!(q2.pop(), Some(42));
    }
}
