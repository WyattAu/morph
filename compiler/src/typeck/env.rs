use std::collections::{HashMap, HashSet};

use crate::ast::Visibility;
use crate::lexer::token::Span;
use crate::typeck::types::Ty;

pub struct TypeEnv {
    bindings: HashMap<String, (Ty, Visibility, Option<Span>)>,
    parent: Option<Box<TypeEnv>>,
    consumed: HashSet<String>,
}

impl Default for TypeEnv {
    fn default() -> Self {
        Self::new()
    }
}

impl TypeEnv {
    pub fn new() -> Self {
        Self {
            bindings: HashMap::new(),
            parent: None,
            consumed: HashSet::new(),
        }
    }

    pub fn with_parent(parent: TypeEnv) -> Self {
        Self {
            bindings: HashMap::new(),
            parent: Some(Box::new(parent)),
            consumed: HashSet::new(),
        }
    }

    pub fn enter_scope(&self) -> Self {
        Self {
            bindings: HashMap::new(),
            parent: Some(Box::new(self.clone())),
            consumed: HashSet::new(),
        }
    }

    pub fn exit_scope(self) -> Option<TypeEnv> {
        self.parent.map(|p| *p)
    }

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

    pub fn insert(&mut self, name: String, ty: Ty, visibility: Visibility, span: Option<Span>) {
        self.bindings.insert(name, (ty, visibility, span));
    }

    pub fn insert_var(&mut self, name: String, ty: Ty) {
        self.bindings.insert(name, (ty, Visibility::Private, None));
    }

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

    pub fn shadow(&mut self, name: String, ty: Ty) {
        self.bindings.insert(name, (ty, Visibility::Private, None));
    }

    pub fn lookup_binding(&self, name: &str) -> Option<(&Ty, Visibility)> {
        if let Some((ty, vis, _)) = self.bindings.get(name) {
            Some((ty, *vis))
        } else if let Some(ref parent) = self.parent {
            parent.lookup_binding(name)
        } else {
            None
        }
    }

    pub fn parent_mut(&mut self) -> Option<&mut TypeEnv> {
        self.parent.as_deref_mut()
    }
}

impl Clone for TypeEnv {
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
