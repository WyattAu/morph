use std::fmt;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Span {
    pub start: usize,
    pub end: usize,
    pub line: u32,
    pub col: u32,
}

impl Span {
    pub fn new(start: usize, end: usize, line: u32, col: u32) -> Self {
        Self {
            start,
            end,
            line,
            col,
        }
    }

    pub fn dummy() -> Self {
        Self::new(0, 0, 1, 1)
    }

    pub fn merge(self, other: Span) -> Span {
        Span {
            start: self.start.min(other.start),
            end: self.end.max(other.end),
            line: self.line.min(other.line),
            col: if self.line <= other.line {
                self.col
            } else {
                other.col
            },
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum TokenKind {
    Fn,
    Ret,
    Use,
    Pub,
    Mut,
    Type,
    Act,
    State,
    Event,
    On,
    Spawn,
    Async,
    Fix,
    If,
    Else,
    Loop,
    Defer,
    Const,
    Void,
    In,
    Is,
    As,

    IntLiteral(i64),
    FloatLiteral(String),
    StringLiteral(String),
    BoolLiteral(bool),
    Null,

    Identifier(String),

    Plus,
    Minus,
    Star,
    Slash,
    Percent,
    EqEq,
    BangEq,
    Lt,
    Gt,
    LtEq,
    GtEq,
    AmpAmp,
    PipePipe,
    Bang,
    Pipe,
    PipeGt,
    Walrus,
    QuestionQuestion,
    Question,
    Arrow,
    FatArrow,
    Assign,

    LParen,
    RParen,
    LBrace,
    RBrace,
    LBracket,
    RBracket,
    Comma,
    Semicolon,
    Colon,
    ColonColon,
    Dot,
    Underscore,

    Caret,
    Hash,
    Amp,

    LtGeneric,
    GtGeneric,

    At,

    Eof,
}

#[derive(Debug, Clone)]
pub struct Token {
    pub kind: TokenKind,
    pub span: Span,
}

impl Token {
    pub fn new(kind: TokenKind, span: Span) -> Self {
        Self { kind, span }
    }

    pub fn is_keyword(&self) -> bool {
        matches!(
            self.kind,
            TokenKind::Fn
                | TokenKind::Ret
                | TokenKind::Use
                | TokenKind::Pub
                | TokenKind::Mut
                | TokenKind::Type
                | TokenKind::Act
                | TokenKind::State
                | TokenKind::Event
                | TokenKind::On
                | TokenKind::Spawn
                | TokenKind::Async
                | TokenKind::Fix
                | TokenKind::If
                | TokenKind::Else
                | TokenKind::Loop
                | TokenKind::Defer
                | TokenKind::Const
                | TokenKind::Void
                | TokenKind::In
                | TokenKind::Is
                | TokenKind::As
        )
    }
}

impl fmt::Display for TokenKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TokenKind::Fn => write!(f, "fn"),
            TokenKind::Ret => write!(f, "ret"),
            TokenKind::Use => write!(f, "use"),
            TokenKind::Pub => write!(f, "pub"),
            TokenKind::Mut => write!(f, "mut"),
            TokenKind::Type => write!(f, "type"),
            TokenKind::Act => write!(f, "act"),
            TokenKind::State => write!(f, "state"),
            TokenKind::Event => write!(f, "event"),
            TokenKind::On => write!(f, "on"),
            TokenKind::Spawn => write!(f, "spawn"),
            TokenKind::Async => write!(f, "async"),
            TokenKind::Fix => write!(f, "fix"),
            TokenKind::If => write!(f, "if"),
            TokenKind::Else => write!(f, "else"),
            TokenKind::Loop => write!(f, "loop"),
            TokenKind::Defer => write!(f, "defer"),
            TokenKind::Const => write!(f, "const"),
            TokenKind::Void => write!(f, "void"),
            TokenKind::In => write!(f, "in"),
            TokenKind::Is => write!(f, "is"),
            TokenKind::As => write!(f, "as"),
            TokenKind::IntLiteral(v) => write!(f, "{}", v),
            TokenKind::FloatLiteral(v) => write!(f, "{}", v),
            TokenKind::StringLiteral(v) => write!(f, "\"{}\"", v),
            TokenKind::BoolLiteral(v) => write!(f, "{}", v),
            TokenKind::Null => write!(f, "null"),
            TokenKind::Identifier(v) => write!(f, "{}", v),
            TokenKind::Plus => write!(f, "+"),
            TokenKind::Minus => write!(f, "-"),
            TokenKind::Star => write!(f, "*"),
            TokenKind::Slash => write!(f, "/"),
            TokenKind::Percent => write!(f, "%"),
            TokenKind::EqEq => write!(f, "=="),
            TokenKind::BangEq => write!(f, "!="),
            TokenKind::Lt => write!(f, "<"),
            TokenKind::Gt => write!(f, ">"),
            TokenKind::LtEq => write!(f, "<="),
            TokenKind::GtEq => write!(f, ">="),
            TokenKind::AmpAmp => write!(f, "&&"),
            TokenKind::PipePipe => write!(f, "||"),
            TokenKind::Bang => write!(f, "!"),
            TokenKind::Pipe => write!(f, "|"),
            TokenKind::PipeGt => write!(f, "|>"),
            TokenKind::Walrus => write!(f, ":="),
            TokenKind::QuestionQuestion => write!(f, "??"),
            TokenKind::Question => write!(f, "?"),
            TokenKind::Arrow => write!(f, "->"),
            TokenKind::FatArrow => write!(f, "=>"),
            TokenKind::Assign => write!(f, "="),
            TokenKind::LParen => write!(f, "("),
            TokenKind::RParen => write!(f, ")"),
            TokenKind::LBrace => write!(f, "{{"),
            TokenKind::RBrace => write!(f, "}}"),
            TokenKind::LBracket => write!(f, "["),
            TokenKind::RBracket => write!(f, "]"),
            TokenKind::Comma => write!(f, ","),
            TokenKind::Semicolon => write!(f, ";"),
            TokenKind::Colon => write!(f, ":"),
            TokenKind::ColonColon => write!(f, "::"),
            TokenKind::Dot => write!(f, "."),
            TokenKind::Underscore => write!(f, "_"),
            TokenKind::Caret => write!(f, "^"),
            TokenKind::Hash => write!(f, "#"),
            TokenKind::Amp => write!(f, "&"),
            TokenKind::LtGeneric => write!(f, "<"),
            TokenKind::GtGeneric => write!(f, ">"),
            TokenKind::At => write!(f, "@"),
            TokenKind::Eof => write!(f, "end of file"),
        }
    }
}
