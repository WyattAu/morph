//! Runtime crate for the Morph language.

#![deny(missing_docs)]

/// Actor model implementation.
pub mod actor;
/// Reference-counted smart pointers.
pub mod arc;
/// Chase-Lev work-stealing deque.
pub mod chase_lev;
/// Runtime error types.
pub mod error;
/// Green thread (fiber) implementation.
pub mod fiber;
/// ID types for actors, fibers, and futures.
pub mod ids;
/// I/O reactor and polling.
pub mod io;
/// Memory allocators.
pub mod memory;
/// Multi-producer single-consumer queue.
pub mod mpsc;
/// Task schedulers.
pub mod scheduler;
/// Synchronization primitives.
pub mod sync;
/// Core value types and message payloads.
pub mod value;

pub use actor::{Actor, ActorMessage, ActorState, SupervisionStrategy};
pub use arc::{MorphArc, MorphWeak};
pub use chase_lev::ChaseLevDeque;
pub use error::RuntimeError;
pub use fiber::{Fiber, FiberContext, FiberState, FiberYield, SuspendReason};
pub use ids::{ActorId, FiberId, FutureId};
pub use io::{IoOp, IoRequest, Poller, Reactor};
pub use memory::{Allocator, ArenaAllocator, GlobalAllocator};
pub use mpsc::MpscQueue;
pub use scheduler::{DeterministicScheduler, Scheduler, WorkStealingScheduler, WorkerThread};
pub use sync::{Once, RwLock, WaitGroup};
pub use value::{MessagePayload, MorphString, MorphValue, SignalType};
