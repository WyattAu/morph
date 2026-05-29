pub mod compiler;
pub mod errors;
pub mod layout;
pub mod morph_ir;

pub use compiler::CodeGen;
pub use errors::CodeGenError;
pub use layout::{compute_layout, TypeLayout, TypeRegistry};
pub use morph_ir::{
    CompiledFunction, FieldInfo, Instruction, MorphIRModule, ParamInfo, TypeInfo, TypeInfoKind,
    VariantInfo,
};
