use std::sync::Arc as StdArc;
use std::sync::Weak as StdWeak;

const _: () = assert!(
    std::mem::size_of::<usize>() >= 4,
    "MorphArc requires at least 32-bit platform"
);

/// A reference-counted smart pointer with the same semantics as
/// [`std::sync::Arc`].
///
/// The value is dropped once the last [`MorphArc`] handle referring to it is
/// dropped. This is a distinct type from [`std::sync::Arc`] so that runtime
/// values cannot be confused with unrelated shared ownership.
pub struct MorphArc<T: ?Sized> {
    inner: StdArc<T>,
}

/// A non-owning reference to a [`MorphArc`] allocation.
///
/// A [`MorphWeak`] does not keep the value alive; it becomes un-upgradeable
/// once the last [`MorphArc`] handle is dropped.
pub struct MorphWeak<T: ?Sized> {
    inner: StdWeak<T>,
}

impl<T> MorphArc<T> {
    /// Allocates a new shared value.
    pub fn new(value: T) -> Self {
        MorphArc {
            inner: StdArc::new(value),
        }
    }

    /// Consumes `this` and returns a raw pointer to the value, leaking one
    /// strong reference.
    ///
    /// The pointer must eventually be reclaimed with [`MorphArc::from_raw`];
    /// until then the value will not be dropped.
    pub fn into_raw(this: Self) -> *const T {
        StdArc::into_raw(this.inner)
    }

    /// # Safety
    /// See [`std::sync::Arc::from_raw`].
    ///
    /// `ptr` must have been produced by [`MorphArc::into_raw`] and must not
    /// have been passed to `from_raw` before; each allocation must be
    /// reclaimed exactly once.
    pub unsafe fn from_raw(ptr: *const T) -> Self {
        MorphArc {
            // SAFETY: Caller must guarantee ptr was returned by MorphArc::into_raw,
            // the underlying Arc has exactly 1 strong reference, and no weak references.
            inner: StdArc::from_raw(ptr),
        }
    }

    /// Creates a non-owning [`MorphWeak`] pointing at the same allocation.
    pub fn downgrade(this: &Self) -> MorphWeak<T> {
        MorphWeak {
            inner: StdArc::downgrade(&this.inner),
        }
    }

    /// Returns the number of live [`MorphArc`] handles, including `this`.
    pub fn strong_count(this: &Self) -> usize {
        StdArc::strong_count(&this.inner)
    }

    /// Returns the number of live [`MorphWeak`] handles for this allocation.
    pub fn weak_count(this: &Self) -> usize {
        StdArc::weak_count(&this.inner)
    }

    /// Returns a mutable reference to the value if this is the only handle.
    ///
    /// Returns `None` if any other [`MorphArc`] or [`MorphWeak`] handle to the
    /// same allocation is alive, in which case uniqueness cannot be proven.
    pub fn get_mut(this: &mut Self) -> Option<&mut T> {
        StdArc::get_mut(&mut this.inner)
    }

    /// Consumes the handle and returns the value if it was the last one.
    ///
    /// Returns `None` (dropping the value) if other handles still exist.
    pub fn into_inner(this: Self) -> Option<T> {
        StdArc::into_inner(this.inner)
    }

    /// Returns `true` if both handles point at the same allocation.
    ///
    /// This compares addresses, not the values they contain.
    pub fn ptr_eq(this: &Self, other: &Self) -> bool {
        StdArc::ptr_eq(&this.inner, &other.inner)
    }
}

impl<T: ?Sized> std::ops::Deref for MorphArc<T> {
    type Target = T;

    fn deref(&self) -> &T {
        &self.inner
    }
}

impl<T: ?Sized> Clone for MorphArc<T> {
    fn clone(&self) -> Self {
        MorphArc {
            inner: StdArc::clone(&self.inner),
        }
    }
}

impl<T: Default> Default for MorphArc<T> {
    fn default() -> Self {
        MorphArc::new(T::default())
    }
}

impl<T: ?Sized + std::fmt::Debug> std::fmt::Debug for MorphArc<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.inner.fmt(f)
    }
}

impl<T: ?Sized + PartialEq> PartialEq for MorphArc<T> {
    fn eq(&self, other: &Self) -> bool {
        self.inner == other.inner
    }
}

impl<T: ?Sized + Eq> Eq for MorphArc<T> {}

impl<T: ?Sized + PartialOrd> PartialOrd for MorphArc<T> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        self.inner.partial_cmp(&other.inner)
    }
}

impl<T: ?Sized + Ord> Ord for MorphArc<T> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.inner.cmp(&other.inner)
    }
}

impl<T: ?Sized + std::hash::Hash> std::hash::Hash for MorphArc<T> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.inner.hash(state);
    }
}

impl<T> MorphWeak<T> {
    /// Attempts to reclaim an owning [`MorphArc`] handle.
    ///
    /// Returns `None` if the value has already been dropped.
    pub fn upgrade(&self) -> Option<MorphArc<T>> {
        self.inner.upgrade().map(|inner| MorphArc { inner })
    }

    /// Returns the number of live [`MorphArc`] handles for this allocation.
    pub fn strong_count(&self) -> usize {
        StdWeak::strong_count(&self.inner)
    }

    /// Returns the number of live [`MorphWeak`] handles, including `self`.
    pub fn weak_count(&self) -> usize {
        StdWeak::weak_count(&self.inner)
    }
}

impl<T: ?Sized> Clone for MorphWeak<T> {
    fn clone(&self) -> Self {
        MorphWeak {
            inner: StdWeak::clone(&self.inner),
        }
    }
}

impl<T: ?Sized + std::fmt::Debug> std::fmt::Debug for MorphWeak<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.inner.fmt(f)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_arc_basic() {
        let arc = MorphArc::new(42);
        assert_eq!(*arc, 42);
    }

    #[test]
    fn test_arc_clone_increments_count() {
        let arc = MorphArc::new(42);
        let arc2 = arc.clone();
        assert_eq!(MorphArc::strong_count(&arc), 2);
        assert_eq!(MorphArc::strong_count(&arc2), 2);
        assert!(MorphArc::ptr_eq(&arc, &arc2));
    }

    #[test]
    fn test_arc_drop_decrements() {
        let arc = MorphArc::new(42);
        let arc2 = arc.clone();
        assert_eq!(MorphArc::strong_count(&arc), 2);
        drop(arc2);
        assert_eq!(MorphArc::strong_count(&arc), 1);
    }

    #[test]
    fn test_arc_into_inner() {
        let arc = MorphArc::new(99);
        let arc2 = arc.clone();
        assert_eq!(MorphArc::into_inner(arc), None);
        drop(arc2);
    }

    #[test]
    fn test_arc_into_inner_unique() {
        let arc = MorphArc::new(99);
        let val = MorphArc::into_inner(arc);
        assert_eq!(val, Some(99));
    }

    #[test]
    fn test_weak_upgrade() {
        let arc = MorphArc::new(42);
        let weak = MorphArc::downgrade(&arc);
        assert_eq!(MorphArc::weak_count(&arc), 1);
        let upgraded = weak.upgrade();
        assert!(upgraded.is_some());
        assert_eq!(*upgraded.unwrap(), 42);
        drop(arc);
        assert!(weak.upgrade().is_none());
    }

    #[test]
    fn test_into_raw_from_raw() {
        let arc = MorphArc::new(String::from("hello"));
        let ptr = MorphArc::into_raw(arc);
        let arc2 = unsafe { MorphArc::from_raw(ptr) };
        assert_eq!(&*arc2, "hello");
    }

    #[test]
    fn test_arc_get_mut() {
        let mut arc = MorphArc::new(42);
        {
            let r = MorphArc::get_mut(&mut arc);
            assert!(r.is_some());
            *r.unwrap() = 99;
        }
        assert_eq!(*arc, 99);
    }

    #[test]
    fn test_arc_get_mut_fails_with_clones() {
        let mut arc = MorphArc::new(42);
        let _clone = arc.clone();
        let r = MorphArc::get_mut(&mut arc);
        assert!(r.is_none());
    }
}
