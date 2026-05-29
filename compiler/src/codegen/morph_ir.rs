use crate::lexer::token::Span;
use crate::typeck::types::Ty;

#[derive(Debug, Clone, PartialEq)]
pub enum Instruction {
    PushInt(i64),
    PushFloat(f64),
    PushBool(bool),
    PushStr(u32),
    PushUnit,
    PushNull,

    LoadLocal(u32),
    StoreLocal(u32),
    LoadUpvalue(u32),
    StoreUpvalue(u32),

    Add,
    Sub,
    Mul,
    Div,
    Mod,
    Neg,
    Not,

    Eq,
    Ne,
    Lt,
    Gt,
    Le,
    Ge,

    And,
    Or,

    Jump(i32),
    JumpIf(i32),
    JumpIfNot(i32),
    Call(u32),
    Ret,

    MakeStruct(u32),
    GetField(u32),
    SetField(u32),
    MakeEnum(u8, u32),

    IsNull,
    GetTag,

    FreezeCap,
    BorrowCap,

    YieldFiber,
    SpawnFiber,

    ArcRetain,
    ArcRelease,

    Match(u32),
    DropMatch,

    TryBegin(i32),
    TryEnd,
    Throw,

    Alloc(u32),
    Dealloc(u32),
}

#[derive(Debug, Clone)]
pub struct MorphIRModule {
    pub name: String,
    pub functions: Vec<CompiledFunction>,
    pub strings: Vec<String>,
    pub type_info: Vec<TypeInfo>,
}

impl MorphIRModule {
    pub fn new(name: String) -> Self {
        Self {
            name,
            functions: Vec::new(),
            strings: Vec::new(),
            type_info: Vec::new(),
        }
    }
}

#[derive(Debug, Clone)]
pub struct CompiledFunction {
    pub name: String,
    pub params: Vec<ParamInfo>,
    pub return_type: Option<Ty>,
    pub locals: u32,
    pub instructions: Vec<Instruction>,
    pub span_map: Vec<(u32, Span)>,
}

impl CompiledFunction {
    pub fn new(name: String) -> Self {
        Self {
            name,
            params: Vec::new(),
            return_type: None,
            locals: 0,
            instructions: Vec::new(),
            span_map: Vec::new(),
        }
    }
}

#[derive(Debug, Clone)]
pub struct ParamInfo {
    pub name: String,
    pub ty: Ty,
    pub slot: u32,
}

#[derive(Debug, Clone)]
pub struct TypeInfo {
    pub name: String,
    pub size: u32,
    pub alignment: u32,
    pub kind: TypeInfoKind,
}

#[derive(Debug, Clone)]
pub enum TypeInfoKind {
    Primitive,
    Struct { fields: Vec<FieldInfo> },
    Enum { variants: Vec<VariantInfo> },
    Array { element_ty: Box<Ty>, count: u32 },
}

#[derive(Debug, Clone)]
pub struct FieldInfo {
    pub name: String,
    pub offset: u32,
    pub ty: Ty,
}

#[derive(Debug, Clone)]
pub struct VariantInfo {
    pub name: String,
    pub tag: u8,
    pub size: u32,
    pub fields: Vec<Ty>,
}
