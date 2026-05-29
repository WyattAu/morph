use std::collections::HashMap;

use crate::lexer::token::Span;
use crate::typeck::errors::TypeError;
use crate::typeck::types::Ty;

pub type Substitution = HashMap<u32, Ty>;

pub fn occurs(var: u32, ty: &Ty) -> bool {
    match ty {
        Ty::TypeVar(v) => *v == var,
        Ty::Tuple(elements) => elements.iter().any(|t| occurs(var, t)),
        Ty::Array(inner) => occurs(var, inner),
        Ty::Optional(inner) => occurs(var, inner),
        Ty::Result { ok, err } => occurs(var, ok) || occurs(var, err),
        Ty::Named { args, .. } => args.iter().any(|t| occurs(var, t)),
        Ty::Ref { inner, .. } => occurs(var, inner),
        Ty::Fn { params, ret, .. } => params.iter().any(|t| occurs(var, t)) || occurs(var, ret),
        Ty::Bool
        | Ty::Int(_)
        | Ty::Float(_)
        | Ty::Str
        | Ty::Void
        | Ty::Never
        | Ty::Actor(_)
        | Ty::Error => false,
    }
}

pub fn apply_subst(subst: &Substitution, ty: &Ty) -> Ty {
    match ty {
        Ty::TypeVar(v) => match subst.get(v) {
            Some(resolved) => apply_subst(subst, resolved),
            None => Ty::TypeVar(*v),
        },
        Ty::Tuple(elements) => Ty::Tuple(elements.iter().map(|t| apply_subst(subst, t)).collect()),
        Ty::Array(inner) => Ty::Array(Box::new(apply_subst(subst, inner))),
        Ty::Optional(inner) => Ty::Optional(Box::new(apply_subst(subst, inner))),
        Ty::Result { ok, err } => Ty::Result {
            ok: Box::new(apply_subst(subst, ok)),
            err: Box::new(apply_subst(subst, err)),
        },
        Ty::Named { name, args } => Ty::Named {
            name: name.clone(),
            args: args.iter().map(|t| apply_subst(subst, t)).collect(),
        },
        Ty::Ref { cap, inner } => Ty::Ref {
            cap: *cap,
            inner: Box::new(apply_subst(subst, inner)),
        },
        Ty::Fn {
            params,
            ret,
            effects,
        } => Ty::Fn {
            params: params.iter().map(|t| apply_subst(subst, t)).collect(),
            ret: Box::new(apply_subst(subst, ret)),
            effects: effects.clone(),
        },
        other => other.clone(),
    }
}

#[allow(clippy::result_large_err)]
pub fn unify(t1: &Ty, t2: &Ty, subst: &mut Substitution, span: Span) -> Result<(), TypeError> {
    let t1 = apply_subst(subst, t1);
    let t2 = apply_subst(subst, t2);

    if t1 == t2 {
        return Ok(());
    }

    match (&t1, &t2) {
        (Ty::Error, _) | (_, Ty::Error) => Ok(()),

        (Ty::TypeVar(v), other) | (other, Ty::TypeVar(v)) => {
            if occurs(*v, other) {
                return Err(TypeError::OccursCheck {
                    var: *v,
                    ty: other.clone(),
                    span,
                });
            }
            subst.insert(*v, other.clone());
            Ok(())
        }

        (Ty::Never, _) | (_, Ty::Never) => Ok(()),

        (Ty::Tuple(e1), Ty::Tuple(e2)) => {
            if e1.len() != e2.len() {
                return Err(TypeError::Mismatch {
                    expected: t1.clone(),
                    found: t2.clone(),
                    span,
                });
            }
            for (a, b) in e1.iter().zip(e2.iter()) {
                unify(a, b, subst, span)?;
            }
            Ok(())
        }

        (Ty::Array(i1), Ty::Array(i2)) => unify(i1, i2, subst, span),

        (Ty::Optional(i1), Ty::Optional(i2)) => unify(i1, i2, subst, span),

        (Ty::Result { ok: ok1, err: err1 }, Ty::Result { ok: ok2, err: err2 }) => {
            unify(ok1, ok2, subst, span)?;
            unify(err1, err2, subst, span)
        }

        (Ty::Named { name: n1, args: a1 }, Ty::Named { name: n2, args: a2 }) => {
            if n1 != n2 || a1.len() != a2.len() {
                return Err(TypeError::Mismatch {
                    expected: t1.clone(),
                    found: t2.clone(),
                    span,
                });
            }
            for (x, y) in a1.iter().zip(a2.iter()) {
                unify(x, y, subst, span)?;
            }
            Ok(())
        }

        (Ty::Ref { cap: c1, inner: i1 }, Ty::Ref { cap: c2, inner: i2 }) => {
            match (c1, c2) {
                (crate::typeck::types::Capability::Iso, crate::typeck::types::Capability::Iso) => {}
                (crate::typeck::types::Capability::Iso, crate::typeck::types::Capability::Val) => {}
                (crate::typeck::types::Capability::Val, crate::typeck::types::Capability::Val) => {}
                (crate::typeck::types::Capability::Ref, crate::typeck::types::Capability::Ref) => {}
                _ => {
                    return Err(TypeError::CapabilityViolation {
                        from: *c1,
                        to: *c2,
                        span,
                    });
                }
            }
            unify(i1, i2, subst, span)
        }

        (
            Ty::Fn {
                params: p1,
                ret: r1,
                effects: e1,
            },
            Ty::Fn {
                params: p2,
                ret: r2,
                effects: e2,
            },
        ) => {
            if p1.len() != p2.len() {
                return Err(TypeError::ArgCount {
                    expected: p1.len(),
                    found: p2.len(),
                    span,
                });
            }
            for (a, b) in p1.iter().zip(p2.iter()) {
                unify(b, a, subst, span)?;
            }
            unify(r1, r2, subst, span)?;
            if !e2.is_subset_of(e1) {
                return Err(TypeError::EffectViolation {
                    caller: e1.clone(),
                    callee: e2.clone(),
                    span,
                });
            }
            Ok(())
        }

        _ => Err(TypeError::Mismatch {
            expected: t1.clone(),
            found: t2.clone(),
            span,
        }),
    }
}

pub fn compose_subst(s1: &Substitution, s2: &Substitution) -> Substitution {
    let mut result: Substitution = s2.iter().map(|(k, v)| (*k, apply_subst(s1, v))).collect();
    for (k, v) in s1 {
        result.entry(*k).or_insert_with(|| v.clone());
    }
    result
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::typeck::types::{EffectSet, IntKind};

    fn dummy_span() -> Span {
        Span::dummy()
    }

    #[test]
    fn test_unify_same_type() {
        let mut subst = Substitution::new();
        let result = unify(&Ty::Bool, &Ty::Bool, &mut subst, dummy_span());
        assert!(result.is_ok());
        assert!(subst.is_empty());
    }

    #[test]
    fn test_unify_int_same_kind() {
        let mut subst = Substitution::new();
        let result = unify(
            &Ty::Int(IntKind::I32),
            &Ty::Int(IntKind::I32),
            &mut subst,
            dummy_span(),
        );
        assert!(result.is_ok());
    }

    #[test]
    fn test_unify_int_different_kind() {
        let mut subst = Substitution::new();
        let result = unify(
            &Ty::Int(IntKind::I32),
            &Ty::Int(IntKind::I64),
            &mut subst,
            dummy_span(),
        );
        assert!(result.is_err());
    }

    #[test]
    fn test_unify_type_var() {
        let mut subst = Substitution::new();
        let result = unify(
            &Ty::TypeVar(0),
            &Ty::Int(IntKind::I32),
            &mut subst,
            dummy_span(),
        );
        assert!(result.is_ok());
        assert_eq!(subst.get(&0), Some(&Ty::Int(IntKind::I32)));
    }

    #[test]
    fn test_unify_type_var_reverse() {
        let mut subst = Substitution::new();
        let result = unify(
            &Ty::Int(IntKind::I64),
            &Ty::TypeVar(1),
            &mut subst,
            dummy_span(),
        );
        assert!(result.is_ok());
        assert_eq!(subst.get(&1), Some(&Ty::Int(IntKind::I64)));
    }

    #[test]
    fn test_occurs_check() {
        let mut subst = Substitution::new();
        let recursive = Ty::Optional(Box::new(Ty::TypeVar(0)));
        let result = unify(&Ty::TypeVar(0), &recursive, &mut subst, dummy_span());
        assert!(result.is_err());
        match result {
            Err(TypeError::OccursCheck { var, .. }) => assert_eq!(var, 0),
            _ => panic!("expected OccursCheck error"),
        }
    }

    #[test]
    fn test_apply_subst() {
        let mut subst = Substitution::new();
        subst.insert(0, Ty::Int(IntKind::I32));
        subst.insert(1, Ty::Bool);

        let ty = Ty::Tuple(vec![Ty::TypeVar(0), Ty::TypeVar(1), Ty::Str]);
        let result = apply_subst(&subst, &ty);
        assert_eq!(
            result,
            Ty::Tuple(vec![Ty::Int(IntKind::I32), Ty::Bool, Ty::Str])
        );
    }

    #[test]
    fn test_compose_subst() {
        let mut s1 = Substitution::new();
        s1.insert(0, Ty::Bool);
        let mut s2 = Substitution::new();
        s2.insert(1, Ty::TypeVar(0));

        let composed = compose_subst(&s1, &s2);
        assert_eq!(composed.get(&0), Some(&Ty::Bool));
        assert_eq!(composed.get(&1), Some(&Ty::Bool));
    }

    #[test]
    fn test_unify_tuple() {
        let mut subst = Substitution::new();
        let t1 = Ty::Tuple(vec![Ty::TypeVar(0), Ty::Bool]);
        let t2 = Ty::Tuple(vec![Ty::Int(IntKind::I32), Ty::TypeVar(1)]);
        let result = unify(&t1, &t2, &mut subst, dummy_span());
        assert!(result.is_ok());
        assert_eq!(subst.get(&0), Some(&Ty::Int(IntKind::I32)));
        assert_eq!(subst.get(&1), Some(&Ty::Bool));
    }

    #[test]
    fn test_unify_tuple_length_mismatch() {
        let mut subst = Substitution::new();
        let t1 = Ty::Tuple(vec![Ty::Bool]);
        let t2 = Ty::Tuple(vec![Ty::Bool, Ty::Int(IntKind::I32)]);
        let result = unify(&t1, &t2, &mut subst, dummy_span());
        assert!(result.is_err());
    }

    #[test]
    fn test_unify_optional() {
        let mut subst = Substitution::new();
        let t1 = Ty::Optional(Box::new(Ty::TypeVar(0)));
        let t2 = Ty::Optional(Box::new(Ty::Int(IntKind::I64)));
        let result = unify(&t1, &t2, &mut subst, dummy_span());
        assert!(result.is_ok());
        assert_eq!(subst.get(&0), Some(&Ty::Int(IntKind::I64)));
    }

    #[test]
    fn test_unify_result() {
        let mut subst = Substitution::new();
        let t1 = Ty::Result {
            ok: Box::new(Ty::TypeVar(0)),
            err: Box::new(Ty::Named {
                name: "Error".to_string(),
                args: vec![],
            }),
        };
        let t2 = Ty::Result {
            ok: Box::new(Ty::Int(IntKind::I32)),
            err: Box::new(Ty::Named {
                name: "Error".to_string(),
                args: vec![],
            }),
        };
        let result = unify(&t1, &t2, &mut subst, dummy_span());
        assert!(result.is_ok());
        assert_eq!(subst.get(&0), Some(&Ty::Int(IntKind::I32)));
    }

    #[test]
    fn test_unify_never_with_anything() {
        let mut subst = Substitution::new();
        let result = unify(&Ty::Never, &Ty::Int(IntKind::I32), &mut subst, dummy_span());
        assert!(result.is_ok());
    }

    #[test]
    fn test_unify_error_sentinel() {
        let mut subst = Substitution::new();
        let result = unify(&Ty::Error, &Ty::Int(IntKind::I32), &mut subst, dummy_span());
        assert!(result.is_ok());
    }

    #[test]
    fn test_unify_fn_types() {
        let mut subst = Substitution::new();
        let t1 = Ty::Fn {
            params: vec![Ty::TypeVar(0)],
            ret: Box::new(Ty::TypeVar(1)),
            effects: EffectSet::empty(),
        };
        let t2 = Ty::Fn {
            params: vec![Ty::Int(IntKind::I32)],
            ret: Box::new(Ty::Bool),
            effects: EffectSet::empty(),
        };
        let result = unify(&t1, &t2, &mut subst, dummy_span());
        assert!(result.is_ok());
        assert_eq!(subst.get(&0), Some(&Ty::Int(IntKind::I32)));
        assert_eq!(subst.get(&1), Some(&Ty::Bool));
    }
}
