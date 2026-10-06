use crate::lexer::token::Span;
use crate::typeck::types::{Capability, Effect, EffectSet, Ty};

/// Failures reported by the type checker.
///
/// Every variant carries the [`Span`] of the offending source text so the CLI
/// can point at the right location.
#[derive(Debug, Clone, thiserror::Error)]
pub enum TypeError {
    /// An expression had a type other than the one required.
    #[error("type mismatch: expected {expected}, found {found}")]
    Mismatch {
        /// The type the context required.
        expected: Ty,
        /// The type the expression actually produced.
        found: Ty,
        /// Source location of the expression.
        span: Span,
    },
    /// A name was referenced but never bound.
    #[error("undefined variable: {name}")]
    UndefinedVar {
        /// The unresolved name.
        name: String,
        /// Source location of the reference.
        span: Span,
    },
    /// A linear value was used after it had already been consumed.
    #[error("use after move: variable {name} was consumed")]
    UseAfterMove {
        /// The name of the consumed variable.
        name: String,
        /// Source location of the offending use.
        span: Span,
    },
    /// A value that cannot cross an actor boundary was sent to one.
    #[error("cannot send {ty} across actor boundary")]
    NotSendable {
        /// The type that is not sendable.
        ty: Ty,
        /// Source location of the send.
        span: Span,
    },
    /// A capability was used at a weaker level than it is held at.
    #[error("capability violation: cannot transition {from:?} to {to:?}")]
    CapabilityViolation {
        /// The capability the value is currently held at.
        from: Capability,
        /// The capability the context requires.
        to: Capability,
        /// Source location of the offending transition.
        span: Span,
    },
    /// A callee performs an effect its caller is not permitted to observe.
    #[error("effect violation: calling {callee:?} from {caller:?}")]
    EffectViolation {
        /// Effects allowed at the call site.
        caller: EffectSet,
        /// Effects performed by the callee.
        callee: EffectSet,
        /// Source location of the call.
        span: Span,
    },
    /// Unification would have produced an infinite type.
    #[error("occurs check failed: infinite type {var} = {ty}")]
    OccursCheck {
        /// The unification variable index.
        var: u32,
        /// The type the variable was being unified with.
        ty: Ty,
        /// Source location of the expression being unified.
        span: Span,
    },
    /// A `match` did not cover every case of the scrutinee's type.
    #[error("non-exhaustive match: missing patterns")]
    NonExhaustiveMatch {
        /// Source location of the `match`.
        span: Span,
    },
    /// Two definitions share a name in the same scope.
    #[error("duplicate definition: {name}")]
    DuplicateDef {
        /// The repeated name.
        name: String,
        /// Source location of the later definition.
        span: Span,
    },
    /// A type name was referenced but never defined.
    #[error("undefined type: {name}")]
    UndefinedType {
        /// The unresolved type name.
        name: String,
        /// Source location of the reference.
        span: Span,
    },
    /// A call passed the wrong number of arguments.
    #[error("wrong number of arguments: expected {expected}, found {found}")]
    ArgCount {
        /// The number of parameters the callee declares.
        expected: usize,
        /// The number of arguments supplied.
        found: usize,
        /// Source location of the call.
        span: Span,
    },
    /// A call was attempted on a value that is not callable.
    #[error("not a function")]
    NotAFunction {
        /// The type of the callee expression.
        ty: Ty,
        /// Source location of the callee.
        span: Span,
    },
    /// A field was accessed that the object type does not have.
    #[error("field not found: {field} on type {ty}")]
    FieldNotFound {
        /// The field name that was looked up.
        field: String,
        /// The type of the object being accessed.
        ty: Ty,
        /// Source location of the access.
        span: Span,
    },
    /// A `null` literal was used where a non-optional type was required.
    #[error("null not allowed in non-optional type {ty}")]
    NullNotAllowed {
        /// The non-optional type that was required.
        ty: Ty,
        /// Source location of the `null` literal.
        span: Span,
    },
    /// A function declared `pure` performed a tracked effect.
    #[error("pure function cannot perform {effect:?}")]
    PureViolation {
        /// The effect the function performed.
        effect: Effect,
        /// Source location of the offending expression.
        span: Span,
    },
}
