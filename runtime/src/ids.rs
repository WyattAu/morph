use std::sync::atomic::{AtomicU64, Ordering};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct FiberId(pub u64);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ActorId(pub u64);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct FutureId(pub u64);

static NEXT_FIBER_ID: AtomicU64 = AtomicU64::new(1);
static NEXT_ACTOR_ID: AtomicU64 = AtomicU64::new(1);
static NEXT_FUTURE_ID: AtomicU64 = AtomicU64::new(1);

impl FiberId {
    pub fn new() -> Self {
        FiberId(NEXT_FIBER_ID.fetch_add(1, Ordering::Relaxed))
    }
}

impl ActorId {
    pub fn new() -> Self {
        ActorId(NEXT_ACTOR_ID.fetch_add(1, Ordering::Relaxed))
    }
}

impl FutureId {
    pub fn new() -> Self {
        FutureId(NEXT_FUTURE_ID.fetch_add(1, Ordering::Relaxed))
    }
}

impl Default for FiberId {
    fn default() -> Self {
        Self::new()
    }
}

impl Default for ActorId {
    fn default() -> Self {
        Self::new()
    }
}

impl Default for FutureId {
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
