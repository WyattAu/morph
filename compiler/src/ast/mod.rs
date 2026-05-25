pub mod visit;

use crate::lexer::token::Span;

#[derive(Debug, Clone, PartialEq)]
pub struct Node<T> {
    pub kind: T,
    pub span: Span,
}

impl<T> Node<T> {
    pub fn new(kind: T, span: Span) -> Self {
        Self { kind, span }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum Literal {
    Int(i64),
    Float(String),
    String(String),
    Bool(bool),
    Null,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    Eq,
    Ne,
    Lt,
    Gt,
    Le,
    Ge,
    And,
    Or,
    Is,
    As,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum UnOp {
    Neg,
    Not,
    Ref,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Expr {
    Literal(Literal),
    Var(String),
    BinaryOp {
        op: BinOp,
        lhs: Box<Node<Expr>>,
        rhs: Box<Node<Expr>>,
    },
    UnaryOp {
        op: UnOp,
        operand: Box<Node<Expr>>,
    },
    Call {
        callee: Box<Node<Expr>>,
        args: Vec<Node<Expr>>,
    },
    FieldAccess {
        object: Box<Node<Expr>>,
        field: String,
    },
    Index {
        object: Box<Node<Expr>>,
        index: Box<Node<Expr>>,
    },
    Lambda {
        params: Vec<Node<Param>>,
        body: Box<Node<Expr>>,
    },
    If {
        condition: Box<Node<Expr>>,
        then_branch: Box<Node<Expr>>,
        else_branch: Option<Box<Node<Expr>>>,
    },
    Match {
        scrutinee: Box<Node<Expr>>,
        arms: Vec<Node<MatchArm>>,
    },
    Block {
        stmts: Vec<Node<Stmt>>,
        expr: Option<Box<Node<Expr>>>,
    },
    Pipe {
        lhs: Box<Node<Expr>>,
        rhs: Box<Node<Expr>>,
    },
    ErrorPropagate {
        expr: Box<Node<Expr>>,
    },
    NullCoalesce {
        lhs: Box<Node<Expr>>,
        rhs: Box<Node<Expr>>,
    },
    Async {
        expr: Box<Node<Expr>>,
    },
    Spawn {
        expr: Box<Node<Expr>>,
    },
    StructInit {
        name: String,
        fields: Vec<(String, Node<Expr>)>,
    },
    Walrus {
        name: String,
        value: Box<Node<Expr>>,
        type_ann: Option<Node<Type>>,
    },
}

#[derive(Debug, Clone, PartialEq)]
pub enum Stmt {
    ExprStmt(Node<Expr>),
    VarDecl {
        name: String,
        type_ann: Option<Node<Type>>,
        value: Node<Expr>,
    },
    Assign {
        target: Node<Expr>,
        value: Node<Expr>,
    },
    Return(Option<Node<Expr>>),
    Defer(Node<Expr>),
    Break,
    Continue,
    While {
        condition: Node<Expr>,
        body: Vec<Node<Stmt>>,
    },
    Nop,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Item {
    FnDecl(FnDecl),
    TypeDecl(TypeDecl),
    ConstDecl(ConstDecl),
    UseDecl(UseDecl),
    ActorDecl(ActorDecl),
    ImplBlock(ImplBlock),
    TraitDecl(TraitDecl),
}

#[derive(Debug, Clone, PartialEq)]
pub struct Param {
    pub name: String,
    pub type_ann: Option<Node<Type>>,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Type {
    Named(String),
    Generic {
        name: String,
        args: Vec<Node<Type>>,
    },
    Tuple(Vec<Node<Type>>),
    Array(Box<Node<Type>>),
    Optional(Box<Node<Type>>),
    Reference {
        cap: Capability,
        inner: Box<Node<Type>>,
    },
    Function {
        params: Vec<Node<Type>>,
        ret: Box<Node<Type>>,
    },
    Never,
    Wildcard,
}

#[derive(Debug, Clone, PartialEq)]
pub struct MatchArm {
    pub pattern: Node<Pattern>,
    pub guard: Option<Node<Expr>>,
    pub body: Node<Expr>,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Pattern {
    Wildcard,
    Var(String),
    Literal(Literal),
    Constructor {
        name: String,
        fields: Vec<(String, Node<Pattern>)>,
    },
    Tuple(Vec<Node<Pattern>>),
    Or(Vec<Node<Pattern>>),
    Range {
        start: Box<Node<Pattern>>,
        end: Box<Node<Pattern>>,
    },
    Rest(Option<String>),
}

#[derive(Debug, Clone, PartialEq)]
pub struct FnDecl {
    pub visibility: Visibility,
    pub name: String,
    pub generic_params: Vec<GenericParam>,
    pub params: Vec<Node<Param>>,
    pub return_type: Option<Node<Type>>,
    pub body: Node<Expr>,
    pub effects: Option<EffectSet>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct TypeDecl {
    pub visibility: Visibility,
    pub name: String,
    pub generic_params: Vec<GenericParam>,
    pub body: TypeBody,
}

#[derive(Debug, Clone, PartialEq)]
pub enum TypeBody {
    Struct(Vec<Node<Field>>),
    Enum(Vec<Node<Variant>>),
    Alias(Node<Type>),
}

#[derive(Debug, Clone, PartialEq)]
pub struct Field {
    pub name: String,
    pub type_ann: Node<Type>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Variant {
    pub name: String,
    pub fields: Vec<Node<Type>>,
    pub data: Option<Node<Type>>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct ConstDecl {
    pub visibility: Visibility,
    pub name: String,
    pub type_ann: Node<Type>,
    pub value: Node<Expr>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct UseDecl {
    pub path: Vec<String>,
    pub alias: Option<String>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct ActorDecl {
    pub name: String,
    pub generic_params: Vec<GenericParam>,
    pub members: Vec<Node<ActorMember>>,
}

#[derive(Debug, Clone, PartialEq)]
pub enum ActorMember {
    State {
        name: String,
        type_ann: Node<Type>,
        init: Option<Node<Expr>>,
    },
    Event {
        name: String,
        params: Vec<Node<Param>>,
    },
    OnHandler {
        name: String,
        body: Node<Expr>,
    },
    FnMember(FnDecl),
}

#[derive(Debug, Clone, PartialEq)]
pub struct ImplBlock {
    pub generic_params: Vec<GenericParam>,
    pub name: String,
    pub generic_args: Vec<Node<Type>>,
    pub methods: Vec<Node<FnDecl>>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct TraitDecl {
    pub name: String,
    pub generic_params: Vec<GenericParam>,
    pub methods: Vec<Node<TraitMethod>>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct TraitMethod {
    pub name: String,
    pub params: Vec<Node<Param>>,
    pub return_type: Option<Node<Type>>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Visibility {
    Public,
    Private,
}

#[derive(Debug, Clone, PartialEq)]
pub struct GenericParam {
    pub name: String,
    pub constraint: Option<Node<Type>>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct EffectSet {
    pub effects: Vec<Effect>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Effect {
    Pure,
    IO,
    Net,
    Time,
    System,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Capability {
    Iso,
    Val,
    Ref,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Contract {
    pub name: String,
    pub methods: Vec<TraitMethod>,
}
