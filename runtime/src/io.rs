use crate::ids::FiberId;
use std::sync::Mutex;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum IoOp {
    Read,
    Write,
    Accept,
    Connect,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct FiberWaker {
    pub fiber_id: FiberId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct IoRequest {
    pub fd: u64,
    pub op: IoOp,
    pub waker: FiberWaker,
}

impl IoRequest {
    pub fn new(fd: u64, op: IoOp, fiber_id: FiberId) -> Self {
        IoRequest {
            fd,
            op,
            waker: FiberWaker { fiber_id },
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Poller {
    Epoll,
    Iocp,
    Fallback,
}

pub struct Reactor {
    poller: Poller,
    pending: Mutex<Vec<IoRequest>>,
}

impl Reactor {
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

    pub fn submit(&self, req: IoRequest) {
        self.pending.lock().unwrap().push(req);
    }

    pub fn poll(&self) -> Vec<IoRequest> {
        let mut pending = self.pending.lock().unwrap();
        std::mem::take(&mut *pending)
    }

    pub fn poller(&self) -> Poller {
        self.poller
    }

    pub fn pending_count(&self) -> usize {
        self.pending.lock().unwrap().len()
    }
}

impl Default for Reactor {
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
