pub mod compiler;
pub mod errors;
pub mod layout;
pub mod morph_ir;

pub use compiler::CodeGen;
pub use errors::CodeGenError;
pub use layout::{TypeLayout, TypeRegistry, compute_layout};
pub use morph_ir::{
    CompiledFunction, FieldInfo, Instruction, MorphIRModule, ParamInfo, TypeInfo, TypeInfoKind,
    VariantInfo,
};
