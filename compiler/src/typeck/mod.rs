//! Type checking and inference.

/// Bidirectional type checker driving inference over the AST.
pub mod checker;
/// Typing environment and linear (capability) context tracking.
pub mod env;
/// Type errors reported by the checker.
pub mod errors;
/// The checker's output: inferred types, effects, and warnings.
pub mod result;
/// The type representation used by the checker.
pub mod types;
/// Type variable substitution and unification.
pub mod unification;

pub use checker::TypeChecker;
pub use errors::TypeError;
pub use result::TypeCheckResult;
pub use types::{Capability, Effect, EffectSet, FloatKind, IntKind, Ty};
