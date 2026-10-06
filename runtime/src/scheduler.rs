use crate::actor::Actor;
use crate::chase_lev::ChaseLevDeque;
use crate::error::RuntimeError;
use crate::fiber::{Fiber, FiberState};
use crate::ids::{ActorId, FiberId};
use std::collections::VecDeque;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Arc, Mutex, RwLock};

/// Decides which [`Fiber`] runs next and when it is resumed.
///
/// Implementations must be usable from multiple threads, hence the
/// `Send + Sync` bound.
pub trait Scheduler: Send + Sync {
    /// Queues `fiber` for execution and returns its id.
    fn spawn(&self, fiber: Fiber) -> FiberId;

    /// Queues an actor's handler fiber and returns the actor's id.
    ///
    /// The actor itself is not retained by the scheduler.
    fn spawn_actor(&self, actor: Actor) -> ActorId;

    /// Runs `fiber` to completion on the calling thread.
    ///
    /// # Errors
    ///
    /// Propagates whatever error the fiber's executor reported.
    fn block_on(&self, fiber: Fiber) -> Result<(), RuntimeError>;

    /// Voluntarily gives up the rest of this thread's time slice.
    fn yield_now(&self);

    /// Returns the id of the fiber running on this thread, if any.
    fn current_fiber_id(&self) -> Option<FiberId>;
}

/// One worker of a [`WorkStealingScheduler`], owning a private run queue.
pub struct WorkerThread {
    id: usize,
    local_queue: ChaseLevDeque<Fiber>,
}

impl WorkerThread {
    /// Creates worker `id` with an empty local queue.
    pub fn new(id: usize) -> Self {
        WorkerThread {
            id,
            local_queue: ChaseLevDeque::new(),
        }
    }

    /// Adds a fiber to the owner end of the local queue.
    pub fn push(&self, fiber: Fiber) {
        self.local_queue.push(fiber);
    }

    /// Takes a fiber from the owner end of the local queue.
    pub fn pop(&self) -> Option<Fiber> {
        self.local_queue.pop()
    }

    /// Takes a fiber from the stealable end of the local queue.
    pub fn steal_from(&self) -> Option<Fiber> {
        self.local_queue.steal()
    }

    /// Returns the number of queued fibers.
    ///
    /// The count is a snapshot and may be stale immediately.
    pub fn len(&self) -> usize {
        self.local_queue.len()
    }

    /// Returns `true` if the local queue is empty.
    pub fn is_empty(&self) -> bool {
        self.local_queue.is_empty()
    }

    /// Returns this worker's index.
    pub fn id(&self) -> usize {
        self.id
    }
}

/// A scheduler that keeps one run queue per worker and lets idle workers steal
/// from a randomly chosen peer.
pub struct WorkStealingScheduler {
    workers: Arc<RwLock<Vec<WorkerThread>>>,
    global_queue: ChaseLevDeque<Fiber>,
    num_threads: usize,
    current_fiber: Arc<Mutex<Option<FiberId>>>,
    next_victim: AtomicU64,
}

impl WorkStealingScheduler {
    /// Creates a scheduler with `num_threads` workers, at least one.
    pub fn new(num_threads: usize) -> Self {
        let n = num_threads.max(1);
        let workers = (0..n).map(WorkerThread::new).collect();
        WorkStealingScheduler {
            workers: Arc::new(RwLock::new(workers)),
            global_queue: ChaseLevDeque::new(),
            num_threads: n,
            current_fiber: Arc::new(Mutex::new(None)),
            next_victim: AtomicU64::new(0),
        }
    }

    fn schedule(&self, fiber: Fiber) {
        let workers = self.workers.read().unwrap();
        if let Some(worker) = workers.first() {
            worker.push(fiber);
        } else {
            drop(workers);
            self.global_queue.push(fiber);
        }
    }

    /// Attempts to steal a fiber on behalf of worker `thief_id`.
    ///
    /// Picks a victim round-robin via a shared counter and returns `None` if
    /// the victim has nothing to give, is the thief itself, or there is only
    /// one worker.
    pub fn steal(&self, thief_id: usize) -> Option<Fiber> {
        if self.num_threads <= 1 {
            return None;
        }
        let victim = (self.next_victim.fetch_add(1, Ordering::Relaxed) as usize) % self.num_threads;
        if victim == thief_id {
            return None;
        }
        let workers = self.workers.read().unwrap();
        workers.get(victim).and_then(|w| w.steal_from())
    }

    /// Returns the number of workers.
    pub fn num_workers(&self) -> usize {
        self.num_threads
    }

    /// Returns how many fibers are queued on worker `worker_id`.
    ///
    /// Returns `0` if `worker_id` is out of range.
    pub fn worker_queue_len(&self, worker_id: usize) -> usize {
        let workers = self.workers.read().unwrap();
        workers.get(worker_id).map(|w| w.len()).unwrap_or(0)
    }

    /// Returns how many fibers are queued in the global overflow queue.
    pub fn global_queue_len(&self) -> usize {
        self.global_queue.len()
    }
}

impl Scheduler for WorkStealingScheduler {
    fn spawn(&self, fiber: Fiber) -> FiberId {
        let id = fiber.id();
        self.schedule(fiber);
        id
    }

    fn spawn_actor(&self, mut actor: Actor) -> ActorId {
        let id = actor.id();
        if let Some(fiber) = actor.take_fiber() {
            self.spawn(fiber);
        }
        id
    }

    fn block_on(&self, mut fiber: Fiber) -> Result<(), RuntimeError> {
        {
            let mut current = self.current_fiber.lock().unwrap();
            *current = Some(fiber.id());
        }
        loop {
            match fiber.resume()? {
                FiberState::Completed => {
                    return fiber.result().cloned().unwrap_or(Ok(()));
                }
                FiberState::Panicked => {
                    return fiber.result().cloned().unwrap_or(Err(RuntimeError::Panic {
                        message: "fiber panicked".into(),
                    }));
                }
                FiberState::Suspended(_) => {
                    std::thread::yield_now();
                }
                FiberState::Ready | FiberState::Running => {}
            }
        }
    }

    fn yield_now(&self) {
        std::thread::yield_now();
    }

    fn current_fiber_id(&self) -> Option<FiberId> {
        *self.current_fiber.lock().unwrap()
    }
}

/// A scheduler that advances fibers in a fixed order, for reproducible runs.
///
/// Fibers are kept in a single FIFO queue and a logical clock is bumped once
/// per fiber step, so a given program always yields the same interleaving.
pub struct DeterministicScheduler {
    queue: Arc<Mutex<VecDeque<Fiber>>>,
    logical_clock: Arc<Mutex<u64>>,
}

impl DeterministicScheduler {
    /// Creates an empty deterministic scheduler with its clock at zero.
    pub fn new() -> Self {
        DeterministicScheduler {
            queue: Arc::new(Mutex::new(VecDeque::new())),
            logical_clock: Arc::new(Mutex::new(0)),
        }
    }

    /// Advances the logical clock by one and returns the new value.
    pub fn tick(&self) -> u64 {
        let mut clock = self.logical_clock.lock().unwrap();
        *clock += 1;
        *clock
    }

    /// Returns the current logical clock value.
    pub fn clock(&self) -> u64 {
        *self.logical_clock.lock().unwrap()
    }

    /// Returns the number of fibers waiting to be run.
    pub fn queue_len(&self) -> usize {
        self.queue.lock().unwrap().len()
    }

    #[allow(dead_code)]
    fn drain_queue(&self) -> Result<(), RuntimeError> {
        loop {
            let fiber = {
                let mut queue = self.queue.lock().unwrap();
                queue.pop_front()
            };
            match fiber {
                Some(mut f) => {
                    self.tick();
                    loop {
                        match f.resume()? {
                            FiberState::Completed => {
                                break;
                            }
                            FiberState::Panicked => {
                                return f.result().cloned().unwrap_or(Err(RuntimeError::Panic {
                                    message: "fiber panicked".into(),
                                }));
                            }
                            FiberState::Suspended(_) => {
                                self.queue.lock().unwrap().push_back(f);
                                break;
                            }
                            FiberState::Ready | FiberState::Running => {}
                        }
                    }
                }
                None => return Ok(()),
            }
        }
    }
}

impl Default for DeterministicScheduler {
    fn default() -> Self {
        Self::new()
    }
}

impl Scheduler for DeterministicScheduler {
    fn spawn(&self, fiber: Fiber) -> FiberId {
        let id = fiber.id();
        self.queue.lock().unwrap().push_back(fiber);
        id
    }

    fn spawn_actor(&self, mut actor: Actor) -> ActorId {
        let id = actor.id();
        if let Some(fiber) = actor.take_fiber() {
            self.spawn(fiber);
        }
        id
    }

    fn block_on(&self, mut fiber: Fiber) -> Result<(), RuntimeError> {
        loop {
            match fiber.resume()? {
                FiberState::Completed => {
                    return fiber.result().cloned().unwrap_or(Ok(()));
                }
                FiberState::Panicked => {
                    return fiber.result().cloned().unwrap_or(Err(RuntimeError::Panic {
                        message: "fiber panicked".into(),
                    }));
                }
                FiberState::Suspended(_) => {
                    self.queue.lock().unwrap().push_back(fiber);
                    let next = self.queue.lock().unwrap().pop_front();
                    match next {
                        Some(f) => fiber = f,
                        None => return Ok(()),
                    }
                }
                FiberState::Ready | FiberState::Running => {}
            }
        }
    }

    fn yield_now(&self) {
        self.tick();
    }

    fn current_fiber_id(&self) -> Option<FiberId> {
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::fiber::FiberYield;
    use std::sync::atomic::AtomicUsize;

    #[test]
    fn test_deterministic_block_on_simple() {
        let scheduler = DeterministicScheduler::new();
        let fiber = Fiber::new(|_ctx| FiberYield::Complete(Ok(())));
        let result = scheduler.block_on(fiber);
        assert!(result.is_ok());
    }

    #[test]
    fn test_deterministic_block_on_suspending() {
        let scheduler = DeterministicScheduler::new();
        let counter = Arc::new(AtomicUsize::new(0));
        let c1 = counter.clone();
        let fiber = Fiber::new(move |_ctx| {
            let prev = c1.fetch_add(1, Ordering::SeqCst);
            if prev < 2 {
                FiberYield::Suspend(crate::fiber::SuspendReason::Preempted)
            } else {
                FiberYield::Complete(Ok(()))
            }
        });
        let result = scheduler.block_on(fiber);
        assert!(result.is_ok());
        assert_eq!(counter.load(Ordering::SeqCst), 3);
    }

    #[test]
    fn test_work_stealing_spawn() {
        let scheduler = WorkStealingScheduler::new(4);
        let fiber = Fiber::new(|_ctx| FiberYield::Complete(Ok(())));
        let id = scheduler.spawn(fiber);
        assert_ne!(id, FiberId(0));
        assert!(scheduler.worker_queue_len(0) > 0 || scheduler.global_queue_len() > 0);
    }

    #[test]
    fn test_work_stealing_block_on() {
        let scheduler = WorkStealingScheduler::new(2);
        let fiber = Fiber::new(|_ctx| FiberYield::Complete(Ok(())));
        let result = scheduler.block_on(fiber);
        assert!(result.is_ok());
    }

    #[test]
    fn test_work_stealing_steal() {
        let scheduler = WorkStealingScheduler::new(4);
        let f1 = Fiber::new(|_ctx| FiberYield::Complete(Ok(())));
        scheduler.spawn(f1);
        assert!(scheduler.steal(1).is_some() || scheduler.steal(2).is_some());
    }

    #[test]
    fn test_deterministic_clock() {
        let scheduler = DeterministicScheduler::new();
        assert_eq!(scheduler.clock(), 0);
        scheduler.tick();
        assert_eq!(scheduler.clock(), 1);
        scheduler.tick();
        assert_eq!(scheduler.clock(), 2);
    }

    #[test]
    fn test_worker_thread_push_pop() {
        let w = WorkerThread::new(0);
        assert!(w.is_empty());
        w.push(Fiber::new(|_ctx| FiberYield::Complete(Ok(()))));
        assert_eq!(w.len(), 1);
        let f = w.pop();
        assert!(f.is_some());
        assert!(w.is_empty());
    }
}
