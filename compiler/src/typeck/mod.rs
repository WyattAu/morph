pub mod checker;
pub mod env;
pub mod errors;
pub mod result;
pub mod types;
pub mod unification;

pub use checker::TypeChecker;
pub use errors::TypeError;
pub use result::TypeCheckResult;
pub use types::{Capability, Effect, EffectSet, FloatKind, IntKind, Ty};
