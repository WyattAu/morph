use crate::ids::FiberId;
use std::sync::Mutex;

/// The kind of I/O operation a fiber is waiting on.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum IoOp {
    /// Waiting for the descriptor to become readable.
    Read,
    /// Waiting for the descriptor to accept a write.
    Write,
    /// Waiting for an inbound connection.
    Accept,
    /// Waiting for an outbound connection to complete.
    Connect,
}

/// Identifies the fiber to wake once an [`IoRequest`] completes.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct FiberWaker {
    /// The fiber to resume when the operation is ready.
    pub fiber_id: FiberId,
}

/// A single I/O operation submitted to a [`Reactor`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct IoRequest {
    /// The file descriptor being operated on.
    pub fd: u64,
    /// What the fiber is waiting for on `fd`.
    pub op: IoOp,
    /// The fiber to wake when the operation becomes ready.
    pub waker: FiberWaker,
}

impl IoRequest {
    /// Builds a request that wakes `fiber_id` when `op` on `fd` is ready.
    pub fn new(fd: u64, op: IoOp, fiber_id: FiberId) -> Self {
        IoRequest {
            fd,
            op,
            waker: FiberWaker { fiber_id },
        }
    }
}

/// The platform event-notification mechanism backing a [`Reactor`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Poller {
    /// Linux `epoll`.
    Epoll,
    /// Windows I/O completion ports.
    Iocp,
    /// Portable poll loop used on other platforms.
    Fallback,
}

/// Collects pending [`IoRequest`]s and hands them to the runtime in batches.
pub struct Reactor {
    poller: Poller,
    pending: Mutex<Vec<IoRequest>>,
}

impl Reactor {
    /// Creates a reactor using the poller appropriate for the target platform.
    pub fn new() -> Self {
        let poller = Self::detect_poller();
        Reactor {
            poller,
            pending: Mutex::new(Vec::new()),
        }
    }

    fn detect_poller() -> Poller {
        if cfg!(target_os = "linux") {
            Poller::Epoll
        } else if cfg!(target_os = "windows") {
            Poller::Iocp
        } else {
            Poller::Fallback
        }
    }

    /// Queues `req` to be returned by the next [`Reactor::poll`].
    pub fn submit(&self, req: IoRequest) {
        self.pending.lock().unwrap().push(req);
    }

    /// Takes all queued requests, leaving the reactor empty.
    ///
    /// Requests are returned in submission order.
    pub fn poll(&self) -> Vec<IoRequest> {
        let mut pending = self.pending.lock().unwrap();
        std::mem::take(&mut *pending)
    }

    /// Returns the poller implementation in use.
    pub fn poller(&self) -> Poller {
        self.poller
    }

    /// Returns how many requests are waiting for the next [`Reactor::poll`].
    pub fn pending_count(&self) -> usize {
        self.pending.lock().unwrap().len()
    }
}

impl Default for Reactor {
    /// Creates a reactor, exactly as [`Reactor::new`] does.
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_reactor_submit_poll() {
        let reactor = Reactor::new();
        let fid = FiberId::new();
        reactor.submit(IoRequest::new(0, IoOp::Read, fid));
        reactor.submit(IoRequest::new(1, IoOp::Write, fid));
        assert_eq!(reactor.pending_count(), 2);
        let ready = reactor.poll();
        assert_eq!(ready.len(), 2);
        assert_eq!(ready[0].fd, 0);
        assert_eq!(ready[0].op, IoOp::Read);
        assert_eq!(ready[1].fd, 1);
        assert_eq!(ready[1].op, IoOp::Write);
        assert_eq!(reactor.pending_count(), 0);
    }

    #[test]
    fn test_reactor_poller_detection() {
        let reactor = Reactor::new();
        if cfg!(target_os = "linux") {
            assert_eq!(reactor.poller(), Poller::Epoll);
        }
    }
}
