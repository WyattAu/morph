use std::collections::VecDeque;
use std::sync::{Arc, Mutex};

pub struct MpscQueue<T> {
    inner: Arc<Mutex<VecDeque<T>>>,
}

impl<T> MpscQueue<T> {
    pub fn new() -> Self {
        MpscQueue {
            inner: Arc::new(Mutex::new(VecDeque::new())),
        }
    }

    pub fn push(&self, value: T) {
        self.inner.lock().unwrap().push_back(value);
    }

    pub fn pop(&self) -> Option<T> {
        self.inner.lock().unwrap().pop_front()
    }

    pub fn len(&self) -> usize {
        self.inner.lock().unwrap().len()
    }

    pub fn is_empty(&self) -> bool {
        self.inner.lock().unwrap().is_empty()
    }

    pub fn peek(&self) -> Option<std::sync::MutexGuard<'_, VecDeque<T>>> {
        let guard = self.inner.lock().unwrap();
        if guard.is_empty() {
            None
        } else {
            Some(guard)
        }
    }

    pub fn clear(&self) {
        self.inner.lock().unwrap().clear();
    }
}

impl<T> Clone for MpscQueue<T> {
    fn clone(&self) -> Self {
        MpscQueue {
            inner: Arc::clone(&self.inner),
        }
    }
}

impl<T> Default for MpscQueue<T> {
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
