use std::fmt;

/// The source location of a token, as byte offsets plus a line/column pair.
///
/// `start` and `end` are byte offsets into the source; `line` and `col` are
/// 1-based and describe `start` only.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Span {
    /// Byte offset of the first character.
    pub start: usize,
    /// Byte offset one past the last character.
    pub end: usize,
    /// 1-based line number of `start`.
    pub line: u32,
    /// 1-based column number of `start`.
    pub col: u32,
}

impl Span {
    /// Builds a span from explicit offsets and a line/column pair.
    pub fn new(start: usize, end: usize, line: u32, col: u32) -> Self {
        Self {
            start,
            end,
            line,
            col,
        }
    }

    /// Returns a zero-width span at the start of the file.
    ///
    /// Used where a location is required but the token is synthetic.
    pub fn dummy() -> Self {
        Self::new(0, 0, 1, 1)
    }

    /// Returns the smallest span covering both `self` and `other`.
    ///
    /// The returned line and column are taken from whichever span starts
    /// earlier, so they still describe the merged span's `start`.
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

/// A lexical token: a keyword, literal, identifier, or punctuation symbol.
///
/// [`Display`](fmt::Display) renders each variant back to its source spelling,
/// which is what parser error messages quote.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum TokenKind {
    /// The `fn` keyword.
    Fn,
    /// The `ret` keyword.
    Ret,
    /// The `use` keyword.
    Use,
    /// The `pub` keyword.
    Pub,
    /// The `mut` keyword.
    Mut,
    /// The `type` keyword.
    Type,
    /// The `act` keyword, which begins an actor declaration.
    Act,
    /// The `state` keyword, which begins an actor state block.
    State,
    /// The `event` keyword, which declares a message type.
    Event,
    /// The `on` keyword, which begins an event handler.
    On,
    /// The `spawn` keyword.
    Spawn,
    /// The `async` keyword.
    Async,
    /// The `fix` keyword, marking a block that returns a fixed value.
    Fix,
    /// The `if` keyword.
    If,
    /// The `else` keyword.
    Else,
    /// The `loop` keyword.
    Loop,
    /// The `defer` keyword.
    Defer,
    /// The `const` keyword.
    Const,
    /// The `void` keyword.
    Void,
    /// The `in` keyword.
    In,
    /// The `is` keyword, the dynamic type test.
    Is,
    /// The `as` keyword, the downcast operator.
    As,

    /// An integer literal, with its parsed value.
    IntLiteral(i64),
    /// A float literal, retained as text to avoid precision loss.
    FloatLiteral(String),
    /// A string literal, already unescaped.
    StringLiteral(String),
    /// A `true` or `false` literal.
    BoolLiteral(bool),
    /// The `null` literal.
    Null,

    /// An identifier or keyword-like name.
    Identifier(String),

    /// The `+` operator.
    Plus,
    /// The `-` operator.
    Minus,
    /// The `*` operator.
    Star,
    /// The `/` operator.
    Slash,
    /// The `%` operator.
    Percent,
    /// The `==` operator.
    EqEq,
    /// The `!=` operator.
    BangEq,
    /// The `<` operator.
    Lt,
    /// The `>` operator.
    Gt,
    /// The `<=` operator.
    LtEq,
    /// The `>=` operator.
    GtEq,
    /// The `&&` operator.
    AmpAmp,
    /// The `||` operator.
    PipePipe,
    /// The `!` operator.
    Bang,
    /// The `|` operator.
    Pipe,
    /// The `|>` pipe operator.
    PipeGt,
    /// The `:=` walrus assignment.
    Walrus,
    /// The `??` null-coalescing operator.
    QuestionQuestion,
    /// The `?` error-propagation or optional marker.
    Question,
    /// The `->` return type arrow.
    Arrow,
    /// The `=>` match arm arrow.
    FatArrow,
    /// The `=` assignment.
    Assign,

    /// The `(` delimiter.
    LParen,
    /// The `)` delimiter.
    RParen,
    /// The `{` delimiter.
    LBrace,
    /// The `}` delimiter.
    RBrace,
    /// The `[` delimiter.
    LBracket,
    /// The `]` delimiter.
    RBracket,
    /// The `,` separator.
    Comma,
    /// The `;` terminator.
    Semicolon,
    /// The `:` separator.
    Colon,
    /// The `::` path separator.
    ColonColon,
    /// The `.` field access operator.
    Dot,
    /// The `_` wildcard.
    Underscore,

    /// The `^` capability-isolating borrow marker.
    Caret,
    /// The `#` value-capability marker.
    Hash,
    /// The `&` reference-capability marker.
    Amp,

    /// A `<` recognised as the start of a generic argument list.
    LtGeneric,
    /// A `>` recognised as the end of a generic argument list.
    GtGeneric,

    /// The `@` annotation marker.
    At,

    /// The end of the token stream; always the last token produced.
    Eof,
}

/// A lexed token together with the source text it came from.
#[derive(Debug, Clone)]
pub struct Token {
    /// What kind of token this is.
    pub kind: TokenKind,
    /// Where the token appears in the source.
    pub span: Span,
}

impl Token {
    /// Pairs a token kind with its source location.
    pub fn new(kind: TokenKind, span: Span) -> Self {
        Self { kind, span }
    }

    /// Returns `true` if this token is one of the language's reserved words.
    ///
    /// Keywords cannot be used as identifiers; the lexer still emits them as
    /// their own kinds so the parser can accept them by name.
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
