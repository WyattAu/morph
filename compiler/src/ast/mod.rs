//! Abstract syntax tree produced by the parser.

/// Recursive traversal and rewrite support for AST nodes.
pub mod visit;

use crate::lexer::token::Span;

/// A unique identifier for a node in a parsed program.
///
/// Ids are assigned while lowering and are used to key the maps in
/// [`crate::typeck::TypeCheckResult`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct NodeId(
    /// The raw identifier value.
    pub u32,
);

impl NodeId {
    /// Placeholder id used for nodes that have not been lowered yet.
    pub const DUMMY: NodeId = NodeId(0);

    /// Returns the raw identifier value.
    pub fn as_u32(self) -> u32 {
        self.0
    }
}

impl Default for NodeId {
    /// Returns [`NodeId::DUMMY`], since no real id is assigned by default.
    fn default() -> Self {
        Self::DUMMY
    }
}

/// An AST node: a payload paired with its id and source location.
#[derive(Debug, Clone, PartialEq)]
pub struct Node<T> {
    /// The node's unique id.
    pub id: NodeId,
    /// The node's payload.
    pub kind: T,
    /// Where the node appears in the source.
    pub span: Span,
}

impl<T> Node<T> {
    /// Wraps `kind` with a [`NodeId::DUMMY`] id and the given span.
    pub fn new(kind: T, span: Span) -> Self {
        Self {
            id: NodeId::DUMMY,
            kind,
            span,
        }
    }

    /// Wraps `kind` with an explicit id and the given span.
    pub fn with_id(id: NodeId, kind: T, span: Span) -> Self {
        Self { id, kind, span }
    }
}

/// A literal value as written in the source.
///
/// Numeric literals keep their original text where noted, so that precision and
/// the original literal suffix survive parsing.
#[derive(Debug, Clone, PartialEq)]
pub enum Literal {
    /// An integer literal.
    Int(i64),
    /// A floating point literal, retained as text to avoid precision loss.
    Float(String),
    /// A string literal, already unescaped.
    String(String),
    /// A boolean literal.
    Bool(bool),
    /// The `null` literal.
    Null,
}

/// A binary operator.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum BinOp {
    /// Addition.
    Add,
    /// Subtraction.
    Sub,
    /// Multiplication.
    Mul,
    /// Division.
    Div,
    /// Remainder.
    Mod,
    /// Equality.
    Eq,
    /// Inequality.
    Ne,
    /// Less-than.
    Lt,
    /// Greater-than.
    Gt,
    /// Less-than-or-equal.
    Le,
    /// Greater-than-or-equal.
    Ge,
    /// Short-circuiting logical and.
    And,
    /// Short-circuiting logical or.
    Or,
    /// Dynamic type test.
    Is,
    /// Downcast.
    As,
}

/// A unary or prefix operator.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum UnOp {
    /// Arithmetic negation.
    Neg,
    /// Logical negation.
    Not,
    /// Capability-isolating borrow (`^`).
    Ref,
}

/// An expression.
#[derive(Debug, Clone, PartialEq)]
pub enum Expr {
    /// A literal value.
    Literal(Literal),
    /// A variable reference by name.
    Var(String),
    /// A binary operation applied to two operands.
    BinaryOp {
        /// The operator.
        op: BinOp,
        /// Left operand.
        lhs: Box<Node<Expr>>,
        /// Right operand.
        rhs: Box<Node<Expr>>,
    },
    /// A unary operation applied to one operand.
    UnaryOp {
        /// The operator.
        op: UnOp,
        /// The operand.
        operand: Box<Node<Expr>>,
    },
    /// A function call.
    Call {
        /// The callee expression.
        callee: Box<Node<Expr>>,
        /// Argument expressions, in source order.
        args: Vec<Node<Expr>>,
    },
    /// A field access on `object`.
    FieldAccess {
        /// The expression being accessed.
        object: Box<Node<Expr>>,
        /// The field name.
        field: String,
    },
    /// A subscript of `object` by `index`.
    Index {
        /// The expression being indexed.
        object: Box<Node<Expr>>,
        /// The index expression.
        index: Box<Node<Expr>>,
    },
    /// An anonymous function.
    Lambda {
        /// Parameter declarations.
        params: Vec<Node<Param>>,
        /// The function body.
        body: Box<Node<Expr>>,
    },
    /// An `if` expression with an optional `else`.
    If {
        /// The condition, which must be a boolean.
        condition: Box<Node<Expr>>,
        /// Branch taken when the condition is true.
        then_branch: Box<Node<Expr>>,
        /// Branch taken when the condition is false, if written.
        else_branch: Option<Box<Node<Expr>>>,
    },
    /// A `match` expression.
    Match {
        /// The value being matched against.
        scrutinee: Box<Node<Expr>>,
        /// The arms to try, in source order.
        arms: Vec<Node<MatchArm>>,
    },
    /// A sequence of statements with an optional trailing expression.
    Block {
        /// Statements in source order.
        stmts: Vec<Node<Stmt>>,
        /// The block's value expression, if present.
        expr: Option<Box<Node<Expr>>>,
    },
    /// The `lhs |> rhs` pipe operator.
    Pipe {
        /// The upstream expression.
        lhs: Box<Node<Expr>>,
        /// The downstream expression, which receives `lhs` as an argument.
        rhs: Box<Node<Expr>>,
    },
    /// The `expr?` operator, which propagates a `Result` or `Option` failure.
    ErrorPropagate {
        /// The fallible expression.
        expr: Box<Node<Expr>>,
    },
    /// The `lhs ?? rhs` operator, which falls back to `rhs` on absence.
    NullCoalesce {
        /// The preferred value.
        lhs: Box<Node<Expr>>,
        /// The fallback used when `lhs` is absent.
        rhs: Box<Node<Expr>>,
    },
    /// The `async expr` wrapper.
    Async {
        /// The expression to run asynchronously.
        expr: Box<Node<Expr>>,
    },
    /// The `spawn expr` wrapper, which starts an actor.
    Spawn {
        /// The expression to spawn.
        expr: Box<Node<Expr>>,
    },
    /// A struct construction with named fields.
    StructInit {
        /// The struct type's name.
        name: String,
        /// Field initialisers in source order.
        fields: Vec<(String, Node<Expr>)>,
    },
    /// A walrus assignment `name = value` used as an expression.
    Walrus {
        /// The name being assigned.
        name: String,
        /// The assigned value.
        value: Box<Node<Expr>>,
        /// An explicit type annotation, if written.
        type_ann: Option<Node<Type>>,
    },
}

/// A statement.
#[derive(Debug, Clone, PartialEq)]
pub enum Stmt {
    /// An expression evaluated for its effect; its value is discarded.
    ExprStmt(Node<Expr>),
    /// A `let`-style variable declaration.
    VarDecl {
        /// The declared name.
        name: String,
        /// An explicit type annotation, if written.
        type_ann: Option<Node<Type>>,
        /// The initialiser expression.
        value: Node<Expr>,
    },
    /// An assignment to an existing place expression.
    Assign {
        /// The place being assigned to.
        target: Node<Expr>,
        /// The assigned value.
        value: Node<Expr>,
    },
    /// A `return`, optionally carrying a value.
    Return(Option<Node<Expr>>),
    /// A `defer`, whose expression runs when the enclosing block exits.
    Defer(Node<Expr>),
    /// A `break` out of the innermost loop.
    Break,
    /// A `continue` to the next loop iteration.
    Continue,
    /// A `while` loop.
    While {
        /// The condition re-evaluated before each iteration.
        condition: Node<Expr>,
        /// The loop body.
        body: Vec<Node<Stmt>>,
    },
    /// A statement with no effect, used to satisfy a block's shape.
    Nop,
}

/// A top-level or nested item.
#[derive(Debug, Clone, PartialEq)]
pub enum Item {
    /// A function declaration.
    FnDecl(FnDecl),
    /// A type declaration.
    TypeDecl(TypeDecl),
    /// A constant declaration.
    ConstDecl(ConstDecl),
    /// A `use` / import declaration.
    UseDecl(UseDecl),
    /// An actor declaration.
    ActorDecl(ActorDecl),
    /// An inherent or trait implementation block.
    ImplBlock(ImplBlock),
    /// A trait declaration.
    TraitDecl(TraitDecl),
}

/// A declared parameter of a function, method, or closure.
#[derive(Debug, Clone, PartialEq)]
pub struct Param {
    /// The parameter's name.
    pub name: String,
    /// An explicit type annotation, if written.
    pub type_ann: Option<Node<Type>>,
}

/// A syntactic type.
#[derive(Debug, Clone, PartialEq)]
pub enum Type {
    /// A named type, applied to `args` if generic.
    Named(String),
    /// A generic type applied to `args`.
    Generic {
        /// The type's name.
        name: String,
        /// Type arguments in source order.
        args: Vec<Node<Type>>,
    },
    /// A tuple type.
    Tuple(Vec<Node<Type>>),
    /// An array type `[inner]`.
    Array(Box<Node<Type>>),
    /// An optional type `inner?`.
    Optional(Box<Node<Type>>),
    /// A capability-guarded reference type.
    Reference {
        /// The capability the reference is held at.
        cap: Capability,
        /// The referent type.
        inner: Box<Node<Type>>,
    },
    /// A function type.
    Function {
        /// Parameter types.
        params: Vec<Node<Type>>,
        /// Return type.
        ret: Box<Node<Type>>,
    },
    /// The `never` type.
    Never,
    /// The `_` placeholder, standing for an inferred type.
    Wildcard,
}

/// One arm of a `match` expression.
#[derive(Debug, Clone, PartialEq)]
pub struct MatchArm {
    /// The pattern the scrutinee is tested against.
    pub pattern: Node<Pattern>,
    /// A guard that must also hold for the arm to apply.
    pub guard: Option<Node<Expr>>,
    /// The arm's result.
    pub body: Node<Expr>,
}

/// A pattern for destructuring a value in a `match` arm.
#[derive(Debug, Clone, PartialEq)]
pub enum Pattern {
    /// Matches anything and binds nothing.
    Wildcard,
    /// Binds the whole value to a name.
    Var(String),
    /// Matches a literal value.
    Literal(Literal),
    /// Matches a struct or enum constructor applied to `fields`.
    Constructor {
        /// The constructor's name.
        name: String,
        /// Field patterns in declaration order.
        fields: Vec<(String, Node<Pattern>)>,
    },
    /// Matches a tuple element-wise.
    Tuple(Vec<Node<Pattern>>),
    /// Matches if any of the alternatives match.
    Or(Vec<Node<Pattern>>),
    /// Matches a value within an inclusive range.
    Range {
        /// Lower bound.
        start: Box<Node<Pattern>>,
        /// Upper bound.
        end: Box<Node<Pattern>>,
    },
    /// Matches the remaining fields, optionally binding them to a name.
    Rest(Option<String>),
}

/// A function declaration.
#[derive(Debug, Clone, PartialEq)]
pub struct FnDecl {
    /// Whether the function is visible outside its module.
    pub visibility: Visibility,
    /// The function's name.
    pub name: String,
    /// Declared generic parameters.
    pub generic_params: Vec<GenericParam>,
    /// Declared parameters.
    pub params: Vec<Node<Param>>,
    /// The declared return type, if written.
    pub return_type: Option<Node<Type>>,
    /// The function body.
    pub body: Node<Expr>,
    /// The effects the function declares, if written.
    pub effects: Option<EffectSet>,
}

/// A type declaration, wrapping a struct, enum, or alias body.
#[derive(Debug, Clone, PartialEq)]
pub struct TypeDecl {
    /// Whether the type is visible outside its module.
    pub visibility: Visibility,
    /// The type's name.
    pub name: String,
    /// Declared generic parameters.
    pub generic_params: Vec<GenericParam>,
    /// The type's definition.
    pub body: TypeBody,
}

/// The definition of a declared type.
#[derive(Debug, Clone, PartialEq)]
pub enum TypeBody {
    /// A struct with the given fields.
    Struct(Vec<Node<Field>>),
    /// An enum with the given variants.
    Enum(Vec<Node<Variant>>),
    /// A type alias for the given type.
    Alias(Node<Type>),
}

/// A field of a struct declaration.
#[derive(Debug, Clone, PartialEq)]
pub struct Field {
    /// The field's name.
    pub name: String,
    /// The field's declared type.
    pub type_ann: Node<Type>,
}

/// A variant of an enum declaration.
#[derive(Debug, Clone, PartialEq)]
pub struct Variant {
    /// The variant's name.
    pub name: String,
    /// Positional field types.
    pub fields: Vec<Node<Type>>,
    /// An optional named payload, for single-field variants.
    pub data: Option<Node<Type>>,
}

/// A constant declaration.
#[derive(Debug, Clone, PartialEq)]
pub struct ConstDecl {
    /// Whether the constant is visible outside its module.
    pub visibility: Visibility,
    /// The constant's name.
    pub name: String,
    /// The constant's declared type.
    pub type_ann: Node<Type>,
    /// The initialiser expression.
    pub value: Node<Expr>,
}

/// A `use` declaration importing names from a module path.
#[derive(Debug, Clone, PartialEq)]
pub struct UseDecl {
    /// The module path segments, outermost first.
    pub path: Vec<String>,
    /// An optional `as` alias for the imported name.
    pub alias: Option<String>,
}

/// An actor declaration.
#[derive(Debug, Clone, PartialEq)]
pub struct ActorDecl {
    /// The actor's name.
    pub name: String,
    /// Declared generic parameters.
    pub generic_params: Vec<GenericParam>,
    /// The actor's members.
    pub members: Vec<Node<ActorMember>>,
}

/// A member of an actor: state, an event, a handler, or a method.
#[derive(Debug, Clone, PartialEq)]
pub enum ActorMember {
    /// A piece of actor state, optionally with an initialiser.
    State {
        /// The state field's name.
        name: String,
        /// The state field's declared type.
        type_ann: Node<Type>,
        /// The initialiser expression, if written.
        init: Option<Node<Expr>>,
    },
    /// A declared message type with its payload parameters.
    Event {
        /// The event's name.
        name: String,
        /// The event's payload parameters.
        params: Vec<Node<Param>>,
    },
    /// A handler run when a named event arrives.
    OnHandler {
        /// The event name this handler reacts to.
        name: String,
        /// The handler body.
        body: Node<Expr>,
    },
    /// An ordinary method on the actor.
    FnMember(FnDecl),
}

/// An implementation block for a type or trait.
#[derive(Debug, Clone, PartialEq)]
pub struct ImplBlock {
    /// Declared generic parameters.
    pub generic_params: Vec<GenericParam>,
    /// The name of the type or trait being implemented.
    pub name: String,
    /// Explicit type arguments given for the implementation.
    pub generic_args: Vec<Node<Type>>,
    /// The methods defined in this block.
    pub methods: Vec<Node<FnDecl>>,
}

/// A trait declaration.
#[derive(Debug, Clone, PartialEq)]
pub struct TraitDecl {
    /// The trait's name.
    pub name: String,
    /// Declared generic parameters.
    pub generic_params: Vec<GenericParam>,
    /// The trait's required methods.
    pub methods: Vec<Node<TraitMethod>>,
}

/// A method signature declared by a trait or contract.
#[derive(Debug, Clone, PartialEq)]
pub struct TraitMethod {
    /// The method's name.
    pub name: String,
    /// The method's parameters.
    pub params: Vec<Node<Param>>,
    /// The declared return type, if written.
    pub return_type: Option<Node<Type>>,
}

/// Whether an item is visible outside its module.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Visibility {
    /// Visible to other modules.
    Public,
    /// Visible only within the current module.
    Private,
}

/// A declared generic type or function parameter.
#[derive(Debug, Clone, PartialEq)]
pub struct GenericParam {
    /// The parameter's name.
    pub name: String,
    /// An optional constraint type.
    pub constraint: Option<Node<Type>>,
}

/// The set of effects a function declares performing.
#[derive(Debug, Clone, PartialEq)]
pub struct EffectSet {
    /// The individual effects.
    pub effects: Vec<Effect>,
}

/// A single tracked effect.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Effect {
    /// No tracked effects; the function is pure.
    Pure,
    /// File or console I/O.
    IO,
    /// Network I/O.
    Net,
    /// Clock access or sleeping.
    Time,
    /// Process-level facilities such as the environment.
    System,
}

/// The capability a reference is held at.
///
/// Stronger capabilities can be weakened but not the reverse, so moving out of
/// an `Iso` reference is allowed while moving out of a `Ref` is not.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Capability {
    /// Unique, transferable ownership; may be moved.
    Iso,
    /// Shared read-only access to a value owned elsewhere.
    Val,
    /// A borrowed reference; ownership stays with the issuer.
    Ref,
}

/// A contract: a named bundle of method signatures.
#[derive(Debug, Clone, PartialEq)]
pub struct Contract {
    /// The contract's name.
    pub name: String,
    /// The methods the contract requires.
    pub methods: Vec<TraitMethod>,
}
