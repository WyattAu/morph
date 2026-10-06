use rustc_hash::{FxHashMap, FxHashSet};

use crate::ast::Visibility;
use crate::lexer::token::Span;
use crate::typeck::types::Ty;

/// A lexically scoped environment mapping names to their inferred types.
///
/// Scopes nest: [`TypeEnv::enter_scope`] produces a child that delegates
/// lookups to its parent, so an inner binding shadows an outer one of the same
/// name. The environment also tracks *consumed* (linear) names, which are
/// treated as out of scope so that using them after a move is an error.
pub struct TypeEnv {
    bindings: FxHashMap<String, (Ty, Visibility, Option<Span>)>,
    parent: Option<Box<TypeEnv>>,
    consumed: FxHashSet<String>,
}

impl Default for TypeEnv {
    /// Creates a root scope, exactly as [`TypeEnv::new`] does.
    fn default() -> Self {
        Self::new()
    }
}

impl TypeEnv {
    /// Creates an empty root scope with no parent.
    pub fn new() -> Self {
        Self {
            bindings: FxHashMap::default(),
            parent: None,
            consumed: FxHashSet::default(),
        }
    }

    /// Creates a scope nested inside `parent`.
    pub fn with_parent(parent: TypeEnv) -> Self {
        Self {
            bindings: FxHashMap::default(),
            parent: Some(Box::new(parent)),
            consumed: FxHashSet::default(),
        }
    }

    /// Returns a new child scope of this one, starting with no bindings.
    ///
    /// The parent is cloned, so the child can be inspected independently.
    pub fn enter_scope(&self) -> Self {
        Self {
            bindings: FxHashMap::default(),
            parent: Some(Box::new(self.clone())),
            consumed: FxHashSet::default(),
        }
    }

    /// Returns the enclosing scope, or `None` if this is the root scope.
    pub fn exit_scope(self) -> Option<TypeEnv> {
        self.parent.map(|p| *p)
    }

    /// Looks up `name` in this scope and then its ancestors.
    ///
    /// Returns `None` if the name is unbound or has been consumed.
    pub fn lookup(&self, name: &str) -> Option<&Ty> {
        if self.consumed.contains(name) {
            return None;
        }
        if let Some((ty, _, _)) = self.bindings.get(name) {
            Some(ty)
        } else if let Some(ref parent) = self.parent {
            parent.lookup(name)
        } else {
            None
        }
    }

    /// Binds `name` with an explicit visibility and declaration span.
    ///
    /// An existing binding for `name` in this scope is replaced.
    pub fn insert(&mut self, name: String, ty: Ty, visibility: Visibility, span: Option<Span>) {
        self.bindings.insert(name, (ty, visibility, span));
    }

    /// Binds `name` as a private local with no recorded declaration span.
    pub fn insert_var(&mut self, name: String, ty: Ty) {
        self.bindings.insert(name, (ty, Visibility::Private, None));
    }

    /// Marks the linear value `name` as consumed.
    ///
    /// Returns `true` if this call performed the consumption, and `false` if the
    /// name is unbound or was already consumed. Consuming is never undone.
    pub fn consume_var(&mut self, name: &str) -> bool {
        if self.bindings.contains_key(name) && !self.consumed.contains(name) {
            self.consumed.insert(name.to_string());
            true
        } else if let Some(ref mut parent) = self.parent {
            parent.consume_var(name)
        } else {
            false
        }
    }

    /// Returns `true` if `name` has been consumed in this scope or an ancestor.
    pub fn is_consumed(&self, name: &str) -> bool {
        if self.consumed.contains(name) {
            return true;
        }
        if let Some(ref parent) = self.parent {
            parent.is_consumed(name)
        } else {
            false
        }
    }

    /// Rebinds `name` to `ty`, shadowing any binding of the same name.
    pub fn shadow(&mut self, name: String, ty: Ty) {
        self.bindings.insert(name, (ty, Visibility::Private, None));
    }

    /// Looks up `name` and returns its type and visibility.
    ///
    /// Unlike [`TypeEnv::lookup`] this ignores consumption, so it can be used to
    /// inspect a binding that has already been moved out of.
    pub fn lookup_binding(&self, name: &str) -> Option<(&Ty, Visibility)> {
        if let Some((ty, vis, _)) = self.bindings.get(name) {
            Some((ty, *vis))
        } else if let Some(ref parent) = self.parent {
            parent.lookup_binding(name)
        } else {
            None
        }
    }

    /// Returns a mutable handle to the enclosing scope, if there is one.
    pub fn parent_mut(&mut self) -> Option<&mut TypeEnv> {
        self.parent.as_deref_mut()
    }
}

impl Clone for TypeEnv {
    /// Deep-copies the whole scope chain, so the copy can diverge freely.
    fn clone(&self) -> Self {
        Self {
            bindings: self.bindings.clone(),
            parent: self.parent.clone(),
            consumed: self.consumed.clone(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::typeck::types::IntKind;

    #[test]
    fn test_insert_and_lookup() {
        let mut env = TypeEnv::new();
        env.insert_var("x".to_string(), Ty::Int(IntKind::I32));
        let ty = env.lookup("x");
        assert!(ty.is_some());
        assert_eq!(ty.unwrap(), &Ty::Int(IntKind::I32));
    }

    #[test]
    fn test_lookup_missing() {
        let env = TypeEnv::new();
        assert!(env.lookup("x").is_none());
    }

    #[test]
    fn test_nested_scope() {
        let mut outer = TypeEnv::new();
        outer.insert_var("x".to_string(), Ty::Int(IntKind::I32));
        let inner = outer.enter_scope();
        assert_eq!(inner.lookup("x"), Some(&Ty::Int(IntKind::I32)));
    }

    #[test]
    fn test_scope_exit() {
        let mut outer = TypeEnv::new();
        outer.insert_var("x".to_string(), Ty::Int(IntKind::I32));
        let mut inner = outer.enter_scope();
        inner.insert_var("y".to_string(), Ty::Bool);
        assert!(inner.lookup("y").is_some());
        let restored = inner.exit_scope().unwrap();
        assert!(restored.lookup("y").is_none());
        assert_eq!(restored.lookup("x"), Some(&Ty::Int(IntKind::I32)));
    }

    #[test]
    fn test_shadowing() {
        let mut env = TypeEnv::new();
        env.insert_var("x".to_string(), Ty::Int(IntKind::I32));
        env.shadow("x".to_string(), Ty::Bool);
        assert_eq!(env.lookup("x"), Some(&Ty::Bool));
    }

    #[test]
    fn test_consume_var() {
        let mut env = TypeEnv::new();
        env.insert_var("x".to_string(), Ty::Int(IntKind::I32));
        assert!(env.consume_var("x"));
        assert!(env.is_consumed("x"));
        assert!(env.lookup("x").is_none());
    }

    #[test]
    fn test_consume_nonexistent() {
        let mut env = TypeEnv::new();
        assert!(!env.consume_var("x"));
    }

    #[test]
    fn test_visibility_lookup() {
        let mut env = TypeEnv::new();
        env.insert(
            "x".to_string(),
            Ty::Int(IntKind::I32),
            Visibility::Public,
            None,
        );
        let binding = env.lookup_binding("x");
        assert!(binding.is_some());
        let (ty, vis) = binding.unwrap();
        assert_eq!(ty, &Ty::Int(IntKind::I32));
        assert_eq!(vis, Visibility::Public);
    }
}
