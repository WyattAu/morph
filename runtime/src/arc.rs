use std::sync::Arc as StdArc;
use std::sync::Weak as StdWeak;

const _: () = assert!(
    std::mem::size_of::<usize>() >= 4,
    "MorphArc requires at least 32-bit platform"
);

pub struct MorphArc<T: ?Sized> {
    inner: StdArc<T>,
}

pub struct MorphWeak<T: ?Sized> {
    inner: StdWeak<T>,
}

impl<T> MorphArc<T> {
    pub fn new(value: T) -> Self {
        MorphArc {
            inner: StdArc::new(value),
        }
    }

    pub fn into_raw(this: Self) -> *const T {
        StdArc::into_raw(this.inner)
    }

    /// # Safety
    /// See [`std::sync::Arc::from_raw`].
    pub unsafe fn from_raw(ptr: *const T) -> Self {
        MorphArc {
            // SAFETY: Caller must guarantee ptr was returned by MorphArc::into_raw,
            // the underlying Arc has exactly 1 strong reference, and no weak references.
            inner: StdArc::from_raw(ptr),
        }
    }

    pub fn downgrade(this: &Self) -> MorphWeak<T> {
        MorphWeak {
            inner: StdArc::downgrade(&this.inner),
        }
    }

    pub fn strong_count(this: &Self) -> usize {
        StdArc::strong_count(&this.inner)
    }

    pub fn weak_count(this: &Self) -> usize {
        StdArc::weak_count(&this.inner)
    }

    pub fn get_mut(this: &mut Self) -> Option<&mut T> {
        StdArc::get_mut(&mut this.inner)
    }

    pub fn into_inner(this: Self) -> Option<T> {
        StdArc::into_inner(this.inner)
    }

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
    pub fn upgrade(&self) -> Option<MorphArc<T>> {
        self.inner.upgrade().map(|inner| MorphArc { inner })
    }

    pub fn strong_count(&self) -> usize {
        StdWeak::strong_count(&self.inner)
    }

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
