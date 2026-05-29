use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use std::sync::{Mutex, RwLock as StdRwLock};

pub struct WaitGroup {
    count: AtomicUsize,
    notified: AtomicBool,
}

impl WaitGroup {
    pub fn new(count: usize) -> Self {
        let notified = count == 0;
        WaitGroup {
            count: AtomicUsize::new(count),
            notified: AtomicBool::new(notified),
        }
    }

    pub fn done(&self) {
        let prev = self.count.fetch_sub(1, Ordering::AcqRel);
        if prev == 1 {
            self.notified.store(true, Ordering::Release);
        }
    }

    pub fn add(&self, delta: usize) {
        self.count.fetch_add(delta, Ordering::AcqRel);
        self.notified.store(false, Ordering::Release);
    }

    pub fn wait(&self) {
        while !self.notified.load(Ordering::Acquire) {
            std::thread::yield_now();
        }
    }

    pub fn count(&self) -> usize {
        self.count.load(Ordering::Relaxed)
    }

    pub fn is_done(&self) -> bool {
        self.notified.load(Ordering::Acquire)
    }
}

pub struct Once {
    done: AtomicBool,
    lock: Mutex<()>,
}

impl Once {
    pub fn new() -> Self {
        Once {
            done: AtomicBool::new(false),
            lock: Mutex::new(()),
        }
    }

    pub fn call_once<F: FnOnce()>(&self, f: F) {
        if self.done.load(Ordering::Acquire) {
            return;
        }
        let _guard = self.lock.lock().unwrap();
        if !self.done.load(Ordering::Acquire) {
            f();
            self.done.store(true, Ordering::Release);
        }
    }

    pub fn is_done(&self) -> bool {
        self.done.load(Ordering::Acquire)
    }

    pub fn reset(&self) {
        let _guard = self.lock.lock().unwrap();
        self.done.store(false, Ordering::Release);
    }
}

impl Default for Once {
    fn default() -> Self {
        Self::new()
    }
}

pub struct RwLock<T> {
    inner: StdRwLock<T>,
}

impl<T> RwLock<T> {
    pub fn new(value: T) -> Self {
        RwLock {
            inner: StdRwLock::new(value),
        }
    }

    pub fn read(&self) -> std::sync::RwLockReadGuard<'_, T> {
        self.inner.read().unwrap()
    }

    pub fn write(&self) -> std::sync::RwLockWriteGuard<'_, T> {
        self.inner.write().unwrap()
    }

    pub fn into_inner(self) -> T {
        self.inner.into_inner().unwrap()
    }

    pub fn get_mut(&mut self) -> &mut T {
        self.inner.get_mut().unwrap()
    }
}

impl<T: Default> Default for RwLock<T> {
    fn default() -> Self {
        Self::new(T::default())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::Arc;
    use std::thread;

    #[test]
    fn test_wait_group_basic() {
        let wg = Arc::new(WaitGroup::new(3));
        assert!(!wg.is_done());

        let mut handles = Vec::new();
        for _ in 0..3 {
            let w = Arc::clone(&wg);
            handles.push(thread::spawn(move || {
                w.done();
            }));
        }
        for h in handles {
            h.join().unwrap();
        }
        assert!(wg.is_done());
        assert_eq!(wg.count(), 0);
    }

    #[test]
    fn test_wait_group_zero() {
        let wg = WaitGroup::new(0);
        assert!(wg.is_done());
        wg.wait();
    }

    #[test]
    fn test_wait_group_add() {
        let wg = WaitGroup::new(1);
        wg.add(2);
        assert_eq!(wg.count(), 3);
        wg.done();
        wg.done();
        wg.done();
        assert!(wg.is_done());
    }

    #[test]
    fn test_once_basic() {
        let once = Once::new();
        assert!(!once.is_done());
        let mut count = 0;
        once.call_once(|| count += 1);
        assert!(once.is_done());
        once.call_once(|| count += 1);
        assert!(once.is_done());
        assert_eq!(count, 1);
    }

    #[test]
    fn test_once_reset() {
        let once = Once::new();
        let mut count = 0;
        once.call_once(|| count += 1);
        assert_eq!(count, 1);
        once.reset();
        assert!(!once.is_done());
        once.call_once(|| count += 1);
        assert_eq!(count, 2);
    }

    #[test]
    fn test_rwlock_read_write() {
        let lock = RwLock::new(0u64);
        {
            let mut w = lock.write();
            *w = 42;
        }
        {
            let r = lock.read();
            assert_eq!(*r, 42);
        }
    }

    #[test]
    fn test_rwlock_concurrent_reads() {
        let lock = Arc::new(RwLock::new(42u64));
        let mut handles = Vec::new();
        for _ in 0..4 {
            let l = Arc::clone(&lock);
            handles.push(thread::spawn(move || {
                let r = l.read();
                *r
            }));
        }
        for h in handles {
            let val = h.join().unwrap();
            assert_eq!(val, 42);
        }
    }
}
