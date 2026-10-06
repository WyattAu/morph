use crate::error::RuntimeError;
use crate::ids::{ActorId, FiberId, FutureId};
use crate::io::IoRequest;

const INITIAL_STACK_SIZE: usize = 4096;

/// The lifecycle position of a [`Fiber`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FiberState {
    /// Created but not yet resumed.
    Ready,
    /// Currently executing its closure.
    Running,
    /// Yielded and waiting on the given reason.
    Suspended(SuspendReason),
    /// Finished successfully.
    Completed,
    /// Finished with an error.
    Panicked,
}

/// Why a [`Fiber`] yielded control back to the scheduler.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SuspendReason {
    /// Waiting for the given I/O operation to become ready.
    IOWait(IoRequest),
    /// Waiting for a message from the given actor.
    WaitingForMessage(ActorId),
    /// Waiting for the given future to complete.
    WaitingForFuture(FutureId),
    /// Descheduled by the scheduler, eligible to run again later.
    Preempted,
    /// Blocked on a resource that is not yet available.
    Blocked,
}

/// The result of one step of a fiber's executor.
pub enum FiberYield {
    /// The fiber finished with the given outcome.
    Complete(Result<(), RuntimeError>),
    /// The fiber yielded and must be resumed later.
    Suspend(SuspendReason),
}

/// Mutable state handed to a fiber's executor on every step.
pub struct FiberContext {
    /// The id of the fiber being executed.
    pub fiber_id: FiberId,
}

/// A cooperatively scheduled green thread.
///
/// A fiber owns a byte stack that grows on demand and an executor closure that
/// is stepped by [`Fiber::resume`] until it completes or suspends.
pub struct Fiber {
    id: FiberId,
    state: FiberState,
    stack: Vec<u8>,
    stack_ptr: usize,
    #[allow(clippy::type_complexity)]
    executor: Option<Box<dyn FnMut(&mut FiberContext) -> FiberYield + Send>>,
    result: Option<Result<(), RuntimeError>>,
}

impl Fiber {
    /// Creates a fiber in the [`FiberState::Ready`] state.
    ///
    /// The fiber is given a fresh stack and will run `executor` on each call to
    /// [`Fiber::resume`].
    pub fn new(executor: impl FnMut(&mut FiberContext) -> FiberYield + Send + 'static) -> Self {
        Fiber {
            id: FiberId::new(),
            state: FiberState::Ready,
            stack: vec![0u8; INITIAL_STACK_SIZE],
            stack_ptr: INITIAL_STACK_SIZE,
            executor: Some(Box::new(executor)),
            result: None,
        }
    }

    /// Returns this fiber's id.
    pub fn id(&self) -> FiberId {
        self.id
    }

    /// Returns the fiber's current state.
    pub fn state(&self) -> FiberState {
        self.state
    }

    /// Runs the executor for one step.
    ///
    /// On completion the executor is dropped, so a completed fiber cannot be
    /// stepped again. The return value is the new [`FiberState`].
    ///
    /// # Errors
    ///
    /// Returns a [`RuntimeError::Panic`] if the fiber is already running, has
    /// already completed or panicked, or has lost its executor.
    pub fn resume(&mut self) -> Result<FiberState, RuntimeError> {
        match self.state {
            FiberState::Ready | FiberState::Suspended(_) => {
                self.state = FiberState::Running;
                let mut ctx = FiberContext { fiber_id: self.id };
                if let Some(exec) = self.executor.as_mut() {
                    match exec(&mut ctx) {
                        FiberYield::Complete(res) => {
                            self.result = Some(res);
                            self.state = if self.result.as_ref().unwrap().is_ok() {
                                FiberState::Completed
                            } else {
                                FiberState::Panicked
                            };
                            self.executor = None;
                        }
                        FiberYield::Suspend(reason) => {
                            self.state = FiberState::Suspended(reason);
                        }
                    }
                    Ok(self.state)
                } else {
                    Err(RuntimeError::Panic {
                        message: "fiber has no executor".into(),
                    })
                }
            }
            FiberState::Running => Err(RuntimeError::Panic {
                message: "fiber already running".into(),
            }),
            FiberState::Completed => Err(RuntimeError::Panic {
                message: "fiber already completed".into(),
            }),
            FiberState::Panicked => Err(RuntimeError::Panic {
                message: "fiber panicked".into(),
            }),
        }
    }

    /// Returns the total capacity of the fiber's stack in bytes.
    pub fn stack_size(&self) -> usize {
        self.stack.len()
    }

    /// Returns how many bytes of the fiber's stack are currently in use.
    pub fn stack_used(&self) -> usize {
        self.stack.len() - self.stack_ptr
    }

    /// Doubles the capacity of the fiber's stack.
    ///
    /// Any addresses previously handed out by the fiber become stale, so this
    /// must only be called at a suspension point.
    pub fn grow_stack(&mut self) {
        let new_size = self.stack.len() * 2;
        self.stack.resize(new_size, 0);
    }

    /// Returns the recorded outcome, or `None` if the fiber has not finished.
    pub fn result(&self) -> Option<&Result<(), RuntimeError>> {
        self.result.as_ref()
    }
}

impl std::fmt::Debug for Fiber {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Fiber")
            .field("id", &self.id)
            .field("state", &self.state)
            .field("stack_size", &self.stack.len())
            .finish()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::atomic::{AtomicUsize, Ordering};
    use std::sync::Arc;

    #[test]
    fn test_fiber_create_ready() {
        let fiber = Fiber::new(|_ctx| FiberYield::Complete(Ok(())));
        assert_eq!(fiber.state(), FiberState::Ready);
        assert_eq!(fiber.stack_size(), INITIAL_STACK_SIZE);
    }

    #[test]
    fn test_fiber_complete() {
        let mut fiber = Fiber::new(|_ctx| FiberYield::Complete(Ok(())));
        let state = fiber.resume().unwrap();
        assert_eq!(state, FiberState::Completed);
        assert!(fiber.result().unwrap().is_ok());
    }

    #[test]
    fn test_fiber_panic() {
        let mut fiber = Fiber::new(|_ctx| {
            FiberYield::Complete(Err(RuntimeError::Panic {
                message: "boom".into(),
            }))
        });
        let state = fiber.resume().unwrap();
        assert_eq!(state, FiberState::Panicked);
        assert!(fiber.result().unwrap().is_err());
    }

    #[test]
    fn test_fiber_suspend_resume() {
        let counter = Arc::new(AtomicUsize::new(0));
        let c1 = counter.clone();
        let mut fiber = Fiber::new(move |_ctx| {
            let prev = c1.fetch_add(1, Ordering::SeqCst);
            if prev == 0 {
                FiberYield::Suspend(SuspendReason::Preempted)
            } else {
                FiberYield::Complete(Ok(()))
            }
        });

        let state = fiber.resume().unwrap();
        assert_eq!(state, FiberState::Suspended(SuspendReason::Preempted));
        assert_eq!(counter.load(Ordering::SeqCst), 1);

        let state = fiber.resume().unwrap();
        assert_eq!(state, FiberState::Completed);
        assert_eq!(counter.load(Ordering::SeqCst), 2);
    }

    #[test]
    fn test_fiber_cannot_resume_completed() {
        let mut fiber = Fiber::new(|_ctx| FiberYield::Complete(Ok(())));
        fiber.resume().unwrap();
        let err = fiber.resume().unwrap_err();
        assert!(matches!(err, RuntimeError::Panic { .. }));
    }

    #[test]
    fn test_fiber_stack_grows() {
        let mut fiber = Fiber::new(|_ctx| FiberYield::Complete(Ok(())));
        assert_eq!(fiber.stack_size(), 4096);
        fiber.grow_stack();
        assert_eq!(fiber.stack_size(), 8192);
        fiber.grow_stack();
        assert_eq!(fiber.stack_size(), 16384);
    }
}
