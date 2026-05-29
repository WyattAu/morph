use crate::ids::ActorId;

#[derive(Debug, Clone, thiserror::Error)]
pub enum RuntimeError {
    #[error("panic: {message}")]
    Panic { message: String },

    #[error("actor {actor:?} crashed: {reason}")]
    ActorCrashed { actor: ActorId, reason: String },

    #[error("IO error: {0}")]
    IO(String),

    #[error("timeout")]
    Timeout,

    #[error("cancelled")]
    Cancelled,

    #[error("out of memory: requested {requested} bytes")]
    OutOfMemory { requested: usize },

    #[error("deadlock detected")]
    Deadlock,
}

pub type FiberResult = Result<(), RuntimeError>;
