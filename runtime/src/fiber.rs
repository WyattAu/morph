use crate::error::RuntimeError;
use crate::ids::{ActorId, FiberId, FutureId};
use crate::io::IoRequest;

const INITIAL_STACK_SIZE: usize = 4096;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FiberState {
    Ready,
    Running,
    Suspended(SuspendReason),
    Completed,
    Panicked,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SuspendReason {
    IOWait(IoRequest),
    WaitingForMessage(ActorId),
    WaitingForFuture(FutureId),
    Preempted,
    Blocked,
}

pub enum FiberYield {
    Complete(Result<(), RuntimeError>),
    Suspend(SuspendReason),
}

pub struct FiberContext {
    pub fiber_id: FiberId,
}

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

    pub fn id(&self) -> FiberId {
        self.id
    }

    pub fn state(&self) -> FiberState {
        self.state
    }

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

    pub fn stack_size(&self) -> usize {
        self.stack.len()
    }

    pub fn stack_used(&self) -> usize {
        self.stack.len() - self.stack_ptr
    }

    pub fn grow_stack(&mut self) {
        let new_size = self.stack.len() * 2;
        self.stack.resize(new_size, 0);
    }

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
