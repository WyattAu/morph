use crate::lexer::token::Span;
use crate::typeck::types::Ty;

/// A single operation in the Morph intermediate representation.
///
/// The IR is a linear, stack-oriented instruction list per function; operands
/// are drawn from a virtual stack and locals are addressed by slot index.
/// [`CompiledFunction::span_map`] maps instruction offsets back to source text
/// for diagnostics.
#[derive(Debug, Clone, PartialEq)]
pub enum Instruction {
    /// Pushes an integer literal.
    PushInt(i64),
    /// Pushes a float literal.
    PushFloat(f64),
    /// Pushes a boolean literal.
    PushBool(bool),
    /// Pushes the string with the given index in [`MorphIRModule::strings`].
    PushStr(u32),
    /// Pushes the unit value.
    PushUnit,
    /// Pushes the null value.
    PushNull,

    /// Reads the local in the given slot.
    LoadLocal(u32),
    /// Writes the local in the given slot.
    StoreLocal(u32),
    /// Reads the captured upvalue with the given index.
    LoadUpvalue(u32),
    /// Writes the captured upvalue with the given index.
    StoreUpvalue(u32),

    /// Adds the top two stack values.
    Add,
    /// Subtracts the top two stack values.
    Sub,
    /// Multiplies the top two stack values.
    Mul,
    /// Divides the top two stack values.
    Div,
    /// Takes the top two stack values modulo.
    Mod,
    /// Negates the top stack value.
    Neg,
    /// Logically negates the top stack value.
    Not,

    /// Tests the top two stack values for equality.
    Eq,
    /// Tests the top two stack values for inequality.
    Ne,
    /// Tests `a < b`.
    Lt,
    /// Tests `a > b`.
    Gt,
    /// Tests `a <= b`.
    Le,
    /// Tests `a >= b`.
    Ge,

    /// Short-circuiting logical and.
    And,
    /// Short-circuiting logical or.
    Or,

    /// Unconditionally jumps by the given relative instruction offset.
    Jump(i32),
    /// Jumps by the given offset if the popped value is true.
    JumpIf(i32),
    /// Jumps by the given offset if the popped value is false.
    JumpIfNot(i32),
    /// Calls the function with the given index in [`MorphIRModule::functions`].
    Call(u32),
    /// Returns from the current function.
    Ret,

    /// Builds a struct, taking the given type index in [`MorphIRModule::type_info`].
    MakeStruct(u32),
    /// Reads the field with the given index.
    GetField(u32),
    /// Writes the field with the given index.
    SetField(u32),
    /// Builds an enum with the given tag and variant index.
    MakeEnum(u8, u32),

    /// Tests whether the top stack value is null.
    IsNull,
    /// Reads the tag of an enum value.
    GetTag,

    /// Downgrades an `Iso` capability to `Val`.
    FreezeCap,
    /// Downgrades a capability to a shared `Ref`.
    BorrowCap,

    /// Suspends the current fiber.
    YieldFiber,
    /// Spawns a new fiber.
    SpawnFiber,

    /// Increments an `ArcHandle` reference count.
    ArcRetain,
    /// Decrements an `ArcHandle` reference count.
    ArcRelease,

    /// Enters a `match`, pushing the scrutinee.
    Match(u32),
    /// Leaves a `match` block, discarding the discriminant.
    DropMatch,

    /// Begins a fallible region, jumping by the given offset on error.
    TryBegin(i32),
    /// Ends a fallible region.
    TryEnd,
    /// Throws the value on top of the stack to the enclosing region.
    Throw,

    /// Allocates the given number of bytes.
    Alloc(u32),
    /// Deallocates the given number of bytes.
    Dealloc(u32),
}

/// A whole lowered program: its functions plus the constant pools they index
/// into.
///
/// [`Instruction::PushStr`] takes an index into [`MorphIRModule::strings`] and
/// [`Instruction::MakeStruct`] one into [`MorphIRModule::type_info`], so these
/// pools must stay in step with the emitted instructions.
#[derive(Debug, Clone)]
pub struct MorphIRModule {
    /// The module's name, used in diagnostics.
    pub name: String,
    /// Every function in the module, in emission order.
    pub functions: Vec<CompiledFunction>,
    /// The module's deduplicated string literals.
    pub strings: Vec<String>,
    /// Layout information for the struct and enum types the module builds.
    pub type_info: Vec<TypeInfo>,
}

impl MorphIRModule {
    /// Creates an empty module with all pools empty.
    pub fn new(name: String) -> Self {
        Self {
            name,
            functions: Vec::new(),
            strings: Vec::new(),
            type_info: Vec::new(),
        }
    }
}

/// One function's lowered instruction list plus the metadata a backend needs.
#[derive(Debug, Clone)]
pub struct CompiledFunction {
    /// The function's name, used in diagnostics and symbol tables.
    pub name: String,
    /// The function's parameters and their local slots.
    pub params: Vec<ParamInfo>,
    /// The declared return type, if the function returns a value.
    pub return_type: Option<Ty>,
    /// The number of local slots the function needs, parameters included.
    pub locals: u32,
    /// The instruction list, in execution order.
    pub instructions: Vec<Instruction>,
    /// Instruction offsets paired with the source spans they came from.
    pub span_map: Vec<(u32, Span)>,
}

impl CompiledFunction {
    /// Creates a function with no params, no locals, and no instructions.
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

/// One parameter of a [`CompiledFunction`] and the local slot it occupies.
#[derive(Debug, Clone)]
pub struct ParamInfo {
    /// The parameter's source-level name.
    pub name: String,
    /// The parameter's type.
    pub ty: Ty,
    /// The local slot index the argument is loaded into.
    pub slot: u32,
}

/// Size, alignment, and shape of a type used by the module.
#[derive(Debug, Clone)]
pub struct TypeInfo {
    /// The type's name.
    pub name: String,
    /// The type's size in bytes.
    pub size: u32,
    /// The type's required alignment in bytes; always a power of two.
    pub alignment: u32,
    /// Whether the type is a primitive, struct, enum, or array.
    pub kind: TypeInfoKind,
}

/// The shape of a type recorded in [`TypeInfo`].
#[derive(Debug, Clone)]
pub enum TypeInfoKind {
    /// A primitive or otherwise opaque type with no fields.
    Primitive,
    /// A struct, whose fields are laid out at the given byte offsets.
    Struct {
        /// The struct's fields, ordered by ascending offset.
        fields: Vec<FieldInfo>,
    },
    /// An enum, discriminated by its variant tag.
    Enum {
        /// The enum's variants, each carrying its tag value.
        variants: Vec<VariantInfo>,
    },
    /// A fixed-length array.
    Array {
        /// The type of each element.
        element_ty: Box<Ty>,
        /// The number of elements.
        count: u32,
    },
}

/// One field's placement within a struct.
#[derive(Debug, Clone)]
pub struct FieldInfo {
    /// The field's name.
    pub name: String,
    /// The field's byte offset from the start of the struct.
    pub offset: u32,
    /// The field's type.
    pub ty: Ty,
}

/// One variant of an enum recorded in [`TypeInfo`].
#[derive(Debug, Clone)]
pub struct VariantInfo {
    /// The variant's name.
    pub name: String,
    /// The discriminant written into the tag by [`Instruction::MakeEnum`].
    pub tag: u8,
    /// The variant's payload size in bytes.
    pub size: u32,
    /// The types of the variant's positional fields.
    pub fields: Vec<Ty>,
}
