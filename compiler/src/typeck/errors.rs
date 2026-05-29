use crate::lexer::token::Span;
use crate::typeck::types::{Capability, Effect, EffectSet, Ty};

#[derive(Debug, Clone, thiserror::Error)]
pub enum TypeError {
    #[error("type mismatch: expected {expected}, found {found}")]
    Mismatch { expected: Ty, found: Ty, span: Span },
    #[error("undefined variable: {name}")]
    UndefinedVar { name: String, span: Span },
    #[error("use after move: variable {name} was consumed")]
    UseAfterMove { name: String, span: Span },
    #[error("cannot send {ty} across actor boundary")]
    NotSendable { ty: Ty, span: Span },
    #[error("capability violation: cannot transition {from:?} to {to:?}")]
    CapabilityViolation {
        from: Capability,
        to: Capability,
        span: Span,
    },
    #[error("effect violation: calling {callee:?} from {caller:?}")]
    EffectViolation {
        caller: EffectSet,
        callee: EffectSet,
        span: Span,
    },
    #[error("occurs check failed: infinite type {var} = {ty}")]
    OccursCheck { var: u32, ty: Ty, span: Span },
    #[error("non-exhaustive match: missing patterns")]
    NonExhaustiveMatch { span: Span },
    #[error("duplicate definition: {name}")]
    DuplicateDef { name: String, span: Span },
    #[error("undefined type: {name}")]
    UndefinedType { name: String, span: Span },
    #[error("wrong number of arguments: expected {expected}, found {found}")]
    ArgCount {
        expected: usize,
        found: usize,
        span: Span,
    },
    #[error("not a function")]
    NotAFunction { ty: Ty, span: Span },
    #[error("field not found: {field} on type {ty}")]
    FieldNotFound { field: String, ty: Ty, span: Span },
    #[error("null not allowed in non-optional type {ty}")]
    NullNotAllowed { ty: Ty, span: Span },
    #[error("pure function cannot perform {effect:?}")]
    PureViolation { effect: Effect, span: Span },
}
