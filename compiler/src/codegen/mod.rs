//! Code generation: lowering a typed AST to the Morph intermediate
//! representation.

/// The lowering pass itself.
pub mod compiler;
/// Errors reported while lowering.
pub mod errors;
/// Size and alignment computation for IR types.
pub mod layout;
/// The Morph intermediate representation.
pub mod morph_ir;

pub use compiler::CodeGen;
pub use errors::CodeGenError;
pub use layout::{compute_layout, TypeLayout, TypeRegistry};
pub use morph_ir::{
    CompiledFunction, FieldInfo, Instruction, MorphIRModule, ParamInfo, TypeInfo, TypeInfoKind,
    VariantInfo,
};
