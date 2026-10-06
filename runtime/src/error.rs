use crate::ids::ActorId;

/// Failures that can be reported by the runtime.
#[derive(Debug, Clone, thiserror::Error)]
pub enum RuntimeError {
    /// A fiber terminated because it panicked.
    #[error("panic: {message}")]
    Panic {
        /// The panic payload rendered as a string.
        message: String,
    },

    /// An actor terminated because its message handler panicked.
    #[error("actor {actor:?} crashed: {reason}")]
    ActorCrashed {
        /// The actor whose handler failed.
        actor: ActorId,
        /// The panic payload rendered as a string.
        reason: String,
    },

    /// An I/O operation reported a failure.
    #[error("IO error: {0}")]
    IO(String),

    /// A blocking operation exceeded its deadline.
    #[error("timeout")]
    Timeout,

    /// The operation was abandoned by an explicit cancellation.
    #[error("cancelled")]
    Cancelled,

    /// An allocation could not be satisfied.
    #[error("out of memory: requested {requested} bytes")]
    OutOfMemory {
        /// Size of the allocation that could not be satisfied, in bytes.
        requested: usize,
    },

    /// Every worker is blocked and no progress is possible.
    #[error("deadlock detected")]
    Deadlock,
}

/// Result type for fiber and other unit-returning runtime operations.
pub type FiberResult = Result<(), RuntimeError>;
