use std::sync::atomic::{AtomicU64, Ordering};

/// Unique identifier for a green thread (fiber).
///
/// Values are handed out by a process-wide atomic counter starting at `1`, so
/// two fibers created in the same process never share an id.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct FiberId(pub u64);

/// Unique identifier for a spawned actor.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ActorId(pub u64);

/// Unique identifier for an asynchronous computation (future).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct FutureId(pub u64);

static NEXT_FIBER_ID: AtomicU64 = AtomicU64::new(1);
static NEXT_ACTOR_ID: AtomicU64 = AtomicU64::new(1);
static NEXT_FUTURE_ID: AtomicU64 = AtomicU64::new(1);

impl FiberId {
    /// Allocates the next unused fiber id.
    pub fn new() -> Self {
        FiberId(NEXT_FIBER_ID.fetch_add(1, Ordering::Relaxed))
    }
}

impl ActorId {
    /// Allocates the next unused actor id.
    pub fn new() -> Self {
        ActorId(NEXT_ACTOR_ID.fetch_add(1, Ordering::Relaxed))
    }
}

impl FutureId {
    /// Allocates the next unused future id.
    pub fn new() -> Self {
        FutureId(NEXT_FUTURE_ID.fetch_add(1, Ordering::Relaxed))
    }
}

impl Default for FiberId {
    /// Allocates a fresh id, exactly as [`FiberId::new`] does.
    fn default() -> Self {
        Self::new()
    }
}

impl Default for ActorId {
    /// Allocates a fresh id, exactly as [`ActorId::new`] does.
    fn default() -> Self {
        Self::new()
    }
}

impl Default for FutureId {
    /// Allocates a fresh id, exactly as [`FutureId::new`] does.
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_ids_are_unique() {
        let a = FiberId::new();
        let b = FiberId::new();
        assert_ne!(a, b);
        assert!(b.0 > a.0);
    }
}
