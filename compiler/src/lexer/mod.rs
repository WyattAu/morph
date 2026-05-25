use std::iter::Peekable;
use std::str::Chars;

pub mod token;

use token::{Span, Token, TokenKind};

#[derive(Debug, Clone, thiserror::Error, PartialEq, Eq)]
pub enum LexError {
    #[error("invalid character '{ch}' at line {line}, column {col}")]
    InvalidChar {
        ch: char,
        line: u32,
        col: u32,
        pos: usize,
    },
    #[error("unterminated string literal at line {line}, column {col}")]
    UnterminatedString { line: u32, col: u32, pos: usize },
    #[error("invalid number literal '{text}' at line {line}, column {col}")]
    InvalidNumber {
        text: String,
        line: u32,
        col: u32,
        pos: usize,
    },
    #[error("unterminated block comment at line {line}, column {col}")]
    UnterminatedBlockComment { line: u32, col: u32, pos: usize },
    #[error("invalid escape sequence '\\{ch}' at line {line}, column {col}")]
    InvalidEscape {
        ch: char,
        line: u32,
        col: u32,
        pos: usize,
    },
    #[error("invalid unicode escape at line {line}, column {col}")]
    InvalidUnicodeEscape { line: u32, col: u32, pos: usize },
}

impl LexError {
    #[allow(dead_code)]
    fn span(&self) -> Span {
        let (line, col, pos) = match self {
            LexError::InvalidChar { line, col, pos, .. } => (*line, *col, *pos),
            LexError::UnterminatedString { line, col, pos } => (*line, *col, *pos),
            LexError::InvalidNumber { line, col, pos, .. } => (*line, *col, *pos),
            LexError::UnterminatedBlockComment { line, col, pos } => (*line, *col, *pos),
            LexError::InvalidEscape { line, col, pos, .. } => (*line, *col, *pos),
            LexError::InvalidUnicodeEscape { line, col, pos } => (*line, *col, *pos),
        };
        Span::new(pos, pos + 1, line, col)
    }
}

struct LexerState<'a> {
    source: &'a str,
    chars: Peekable<Chars<'a>>,
    position: usize,
    line: u32,
    column: u32,
}

impl<'a> LexerState<'a> {
    fn new(source: &'a str) -> Self {
        Self {
            source,
            chars: source.chars().peekable(),
            position: 0,
            line: 1,
            column: 1,
        }
    }

    fn peek(&mut self) -> Option<char> {
        self.chars.peek().copied()
    }

    fn advance(&mut self) -> Option<char> {
        let ch = self.chars.next()?;
        self.position += ch.len_utf8();
        if ch == '\n' {
            self.line += 1;
            self.column = 1;
        } else {
            self.column += 1;
        }
        Some(ch)
    }

    fn current_span(&self, start_pos: usize, start_col: u32) -> Span {
        Span::new(start_pos, self.position, self.line, start_col)
    }

    fn skip_whitespace(&mut self) {
        while let Some(ch) = self.peek() {
            if ch.is_whitespace() {
                self.advance();
            } else {
                break;
            }
        }
    }

    fn skip_line_comment(&mut self) {
        while let Some(ch) = self.peek() {
            if ch == '\n' {
                break;
            }
            self.advance();
        }
    }

    fn skip_block_comment(&mut self) -> Result<(), LexError> {
        let start_line = self.line;
        let start_col = self.column;
        let start_pos = self.position;

        let mut depth: u32 = 1;
        while depth > 0 {
            match self.peek() {
                None => {
                    return Err(LexError::UnterminatedBlockComment {
                        line: start_line,
                        col: start_col,
                        pos: start_pos,
                    });
                }
                Some('/') => {
                    self.advance();
                    if self.peek() == Some('*') {
                        self.advance();
                        depth += 1;
                    }
                }
                Some('*') => {
                    self.advance();
                    if self.peek() == Some('/') {
                        self.advance();
                        depth -= 1;
                    }
                }
                Some(_) => {
                    self.advance();
                }
            }
        }
        Ok(())
    }

    fn lex_string(&mut self) -> Result<TokenKind, LexError> {
        let start_line = self.line;
        let start_col = self.column;
        let start_pos = self.position;

        let mut value = String::new();
        loop {
            match self.peek() {
                None => {
                    return Err(LexError::UnterminatedString {
                        line: start_line,
                        col: start_col,
                        pos: start_pos,
                    });
                }
                Some('"') => {
                    self.advance();
                    break;
                }
                Some('\\') => {
                    self.advance();
                    let escape_pos = self.position;
                    match self.peek() {
                        Some('n') => {
                            self.advance();
                            value.push('\n');
                        }
                        Some('t') => {
                            self.advance();
                            value.push('\t');
                        }
                        Some('r') => {
                            self.advance();
                            value.push('\r');
                        }
                        Some('\\') => {
                            self.advance();
                            value.push('\\');
                        }
                        Some('"') => {
                            self.advance();
                            value.push('"');
                        }
                        Some('0') => {
                            self.advance();
                            value.push('\0');
                        }
                        Some('u') => {
                            self.advance();
                            if self.peek() != Some('{') {
                                return Err(LexError::InvalidUnicodeEscape {
                                    line: self.line,
                                    col: self.column,
                                    pos: escape_pos,
                                });
                            }
                            self.advance();
                            let mut hex = String::new();
                            while let Some(ch) = self.peek() {
                                if ch == '}' {
                                    self.advance();
                                    break;
                                }
                                if ch.is_ascii_hexdigit() {
                                    hex.push(ch);
                                    self.advance();
                                } else {
                                    return Err(LexError::InvalidUnicodeEscape {
                                        line: self.line,
                                        col: self.column,
                                        pos: escape_pos,
                                    });
                                }
                            }
                            let code_point = u32::from_str_radix(&hex, 16).map_err(|_| {
                                LexError::InvalidUnicodeEscape {
                                    line: self.line,
                                    col: self.column,
                                    pos: escape_pos,
                                }
                            })?;
                            let c = char::from_u32(code_point).ok_or_else(|| {
                                LexError::InvalidUnicodeEscape {
                                    line: self.line,
                                    col: self.column,
                                    pos: escape_pos,
                                }
                            })?;
                            value.push(c);
                        }
                        Some(ch) => {
                            let line = self.line;
                            let col = self.column;
                            self.advance();
                            return Err(LexError::InvalidEscape {
                                ch,
                                line,
                                col,
                                pos: escape_pos,
                            });
                        }
                        None => {
                            return Err(LexError::UnterminatedString {
                                line: start_line,
                                col: start_col,
                                pos: start_pos,
                            });
                        }
                    }
                }
                Some(ch) => {
                    self.advance();
                    value.push(ch);
                }
            }
        }
        Ok(TokenKind::StringLiteral(value))
    }

    fn lex_number(&mut self, first: char) -> Result<TokenKind, LexError> {
        let start_col = self.column - 1;
        let start_pos = self.position - 1;
        let start_line = self.line;

        if first == '0' {
            match self.peek() {
                Some('x') | Some('X') => {
                    self.advance();
                    return self.lex_hex_number(start_pos, start_line, start_col);
                }
                Some('b') | Some('B') => {
                    self.advance();
                    return self.lex_binary_number(start_pos, start_line, start_col);
                }
                _ => {}
            }
        }

        let mut digits = String::new();
        digits.push(first);
        while let Some(ch) = self.peek() {
            if ch.is_ascii_digit() || ch == '_' {
                self.advance();
                digits.push(ch);
            } else {
                break;
            }
        }

        if self.peek() == Some('.') {
            if let Some(next_after_dot) = self.peek_at(self.position + 1) {
                if next_after_dot.is_ascii_digit() {
                    self.advance();
                    digits.push('.');
                    while let Some(ch) = self.peek() {
                        if ch.is_ascii_digit() || ch == '_' {
                            self.advance();
                            digits.push(ch);
                        } else {
                            break;
                        }
                    }
                    if let Some('e') | Some('E') = self.peek() {
                        self.advance();
                        digits.push('e');
                        if let Some('+') | Some('-') = self.peek() {
                            let sign = self.advance().unwrap();
                            digits.push(sign);
                        }
                        while let Some(ch) = self.peek() {
                            if ch.is_ascii_digit() || ch == '_' {
                                self.advance();
                                digits.push(ch);
                            } else {
                                break;
                            }
                        }
                    }
                    let cleaned: String = digits.chars().filter(|c| *c != '_').collect();
                    return Ok(TokenKind::FloatLiteral(cleaned));
                }
            }
        }

        if let Some('e') | Some('E') = self.peek() {
            self.advance();
            digits.push('e');
            if let Some('+') | Some('-') = self.peek() {
                let sign = self.advance().unwrap();
                digits.push(sign);
            }
            while let Some(ch) = self.peek() {
                if ch.is_ascii_digit() || ch == '_' {
                    self.advance();
                    digits.push(ch);
                } else {
                    break;
                }
            }
            let cleaned: String = digits.chars().filter(|c| *c != '_').collect();
            return Ok(TokenKind::FloatLiteral(cleaned));
        }

        let cleaned: String = digits.chars().filter(|c| *c != '_').collect();
        let value = cleaned.parse::<i64>().map_err(|_| LexError::InvalidNumber {
            text: cleaned,
            line: start_line,
            col: start_col,
            pos: start_pos,
        })?;
        Ok(TokenKind::IntLiteral(value))
    }

    fn lex_hex_number(
        &mut self,
        start_pos: usize,
        start_line: u32,
        start_col: u32,
    ) -> Result<TokenKind, LexError> {
        let mut hex = String::new();
        while let Some(ch) = self.peek() {
            if ch.is_ascii_hexdigit() || ch == '_' {
                self.advance();
                if ch != '_' {
                    hex.push(ch);
                }
            } else {
                break;
            }
        }
        if hex.is_empty() {
            return Err(LexError::InvalidNumber {
                text: "0x".to_string(),
                line: start_line,
                col: start_col,
                pos: start_pos,
            });
        }
        let value = i64::from_str_radix(&hex, 16).map_err(|_| LexError::InvalidNumber {
            text: format!("0x{}", hex),
            line: start_line,
            col: start_col,
            pos: start_pos,
        })?;
        Ok(TokenKind::IntLiteral(value))
    }

    fn lex_binary_number(
        &mut self,
        start_pos: usize,
        start_line: u32,
        start_col: u32,
    ) -> Result<TokenKind, LexError> {
        let mut bits = String::new();
        while let Some(ch) = self.peek() {
            if ch == '0' || ch == '1' || ch == '_' {
                self.advance();
                if ch != '_' {
                    bits.push(ch);
                }
            } else {
                break;
            }
        }
        if bits.is_empty() {
            return Err(LexError::InvalidNumber {
                text: "0b".to_string(),
                line: start_line,
                col: start_col,
                pos: start_pos,
            });
        }
        let value = i64::from_str_radix(&bits, 2).map_err(|_| LexError::InvalidNumber {
            text: format!("0b{}", bits),
            line: start_line,
            col: start_col,
            pos: start_pos,
        })?;
        Ok(TokenKind::IntLiteral(value))
    }

    fn peek_at(&self, pos: usize) -> Option<char> {
        self.source[pos..].chars().next()
    }

    fn lex_identifier_or_keyword(&mut self, first: char) -> TokenKind {
        let mut ident = String::new();
        ident.push(first);
        while let Some(ch) = self.peek() {
            if ch.is_alphanumeric() || ch == '_' {
                self.advance();
                ident.push(ch);
            } else {
                break;
            }
        }

        if ident == "_" {
            return TokenKind::Underscore;
        }

        match ident.as_str() {
            "fn" => TokenKind::Fn,
            "ret" => TokenKind::Ret,
            "use" => TokenKind::Use,
            "pub" => TokenKind::Pub,
            "mut" => TokenKind::Mut,
            "type" => TokenKind::Type,
            "act" => TokenKind::Act,
            "state" => TokenKind::State,
            "event" => TokenKind::Event,
            "on" => TokenKind::On,
            "spawn" => TokenKind::Spawn,
            "async" => TokenKind::Async,
            "fix" => TokenKind::Fix,
            "if" => TokenKind::If,
            "else" => TokenKind::Else,
            "loop" => TokenKind::Loop,
            "defer" => TokenKind::Defer,
            "const" => TokenKind::Const,
            "void" => TokenKind::Void,
            "in" => TokenKind::In,
            "is" => TokenKind::Is,
            "as" => TokenKind::As,
            "true" => TokenKind::BoolLiteral(true),
            "false" => TokenKind::BoolLiteral(false),
            "null" => TokenKind::Null,
            _ => TokenKind::Identifier(ident),
        }
    }
}

pub struct Lexer;

impl Lexer {
    pub fn new() -> Self {
        Self
    }

    pub fn tokenize(source: &str) -> Vec<Result<Token, LexError>> {
        let mut state = LexerState::new(source);
        let mut tokens = Vec::new();

        loop {
            state.skip_whitespace();

            let start_pos = state.position;
            let start_col = state.column;
            let start_line = state.line;

            let ch = match state.peek() {
                Some(ch) => ch,
                None => {
                    tokens.push(Ok(Token::new(
                        TokenKind::Eof,
                        Span::new(start_pos, start_pos, start_line, start_col),
                    )));
                    break;
                }
            };

            let result = match ch {
                '/' => {
                    state.advance();
                    match state.peek() {
                        Some('/') => {
                            state.advance();
                            state.skip_line_comment();
                            continue;
                        }
                        Some('*') => {
                            state.advance();
                            match state.skip_block_comment() {
                                Ok(()) => continue,
                                Err(e) => Err(e),
                            }
                        }
                        _ => Ok(Token::new(
                            TokenKind::Slash,
                            state.current_span(start_pos, start_col),
                        )),
                    }
                }
                '"' => {
                    state.advance();
                    match state.lex_string() {
                        Ok(kind) => Ok(Token::new(kind, state.current_span(start_pos, start_col))),
                        Err(e) => Err(e),
                    }
                }
                '0'..='9' => {
                    state.advance();
                    match state.lex_number(ch) {
                        Ok(kind) => Ok(Token::new(kind, state.current_span(start_pos, start_col))),
                        Err(e) => Err(e),
                    }
                }
                'a'..='z' | 'A'..='Z' | '_' => {
                    state.advance();
                    let kind = state.lex_identifier_or_keyword(ch);
                    Ok(Token::new(kind, state.current_span(start_pos, start_col)))
                }
                '+' => {
                    state.advance();
                    Ok(Token::new(
                        TokenKind::Plus,
                        state.current_span(start_pos, start_col),
                    ))
                }
                '-' => {
                    state.advance();
                    if state.peek() == Some('>') {
                        state.advance();
                        Ok(Token::new(
                            TokenKind::Arrow,
                            state.current_span(start_pos, start_col),
                        ))
                    } else {
                        Ok(Token::new(
                            TokenKind::Minus,
                            state.current_span(start_pos, start_col),
                        ))
                    }
                }
                '*' => {
                    state.advance();
                    Ok(Token::new(
                        TokenKind::Star,
                        state.current_span(start_pos, start_col),
                    ))
                }
                '%' => {
                    state.advance();
                    Ok(Token::new(
                        TokenKind::Percent,
                        state.current_span(start_pos, start_col),
                    ))
                }
                '=' => {
                    state.advance();
                    match state.peek() {
                        Some('=') => {
                            state.advance();
                            Ok(Token::new(
                                TokenKind::EqEq,
                                state.current_span(start_pos, start_col),
                            ))
                        }
                        Some('>') => {
                            state.advance();
                            Ok(Token::new(
                                TokenKind::FatArrow,
                                state.current_span(start_pos, start_col),
                            ))
                        }
                        _ => Ok(Token::new(
                            TokenKind::Assign,
                            state.current_span(start_pos, start_col),
                        )),
                    }
                }
                '!' => {
                    state.advance();
                    if state.peek() == Some('=') {
                        state.advance();
                        Ok(Token::new(
                            TokenKind::BangEq,
                            state.current_span(start_pos, start_col),
                        ))
                    } else {
                        Ok(Token::new(
                            TokenKind::Bang,
                            state.current_span(start_pos, start_col),
                        ))
                    }
                }
                '<' => {
                    state.advance();
                    if state.peek() == Some('=') {
                        state.advance();
                        Ok(Token::new(
                            TokenKind::LtEq,
                            state.current_span(start_pos, start_col),
                        ))
                    } else {
                        Ok(Token::new(
                            TokenKind::Lt,
                            state.current_span(start_pos, start_col),
                        ))
                    }
                }
                '>' => {
                    state.advance();
                    if state.peek() == Some('=') {
                        state.advance();
                        Ok(Token::new(
                            TokenKind::GtEq,
                            state.current_span(start_pos, start_col),
                        ))
                    } else {
                        Ok(Token::new(
                            TokenKind::Gt,
                            state.current_span(start_pos, start_col),
                        ))
                    }
                }
                '&' => {
                    state.advance();
                    if state.peek() == Some('&') {
                        state.advance();
                        Ok(Token::new(
                            TokenKind::AmpAmp,
                            state.current_span(start_pos, start_col),
                        ))
                    } else {
                        Ok(Token::new(
                            TokenKind::Amp,
                            state.current_span(start_pos, start_col),
                        ))
                    }
                }
                '|' => {
                    state.advance();
                    match state.peek() {
                        Some('|') => {
                            state.advance();
                            Ok(Token::new(
                                TokenKind::PipePipe,
                                state.current_span(start_pos, start_col),
                            ))
                        }
                        Some('>') => {
                            state.advance();
                            Ok(Token::new(
                                TokenKind::PipeGt,
                                state.current_span(start_pos, start_col),
                            ))
                        }
                        _ => Ok(Token::new(
                            TokenKind::Pipe,
                            state.current_span(start_pos, start_col),
                        )),
                    }
                }
                ':' => {
                    state.advance();
                    if state.peek() == Some('=') {
                        state.advance();
                        Ok(Token::new(
                            TokenKind::Walrus,
                            state.current_span(start_pos, start_col),
                        ))
                    } else if state.peek() == Some(':') {
                        state.advance();
                        Ok(Token::new(
                            TokenKind::ColonColon,
                            state.current_span(start_pos, start_col),
                        ))
                    } else {
                        Ok(Token::new(
                            TokenKind::Colon,
                            state.current_span(start_pos, start_col),
                        ))
                    }
                }
                '?' => {
                    state.advance();
                    if state.peek() == Some('?') {
                        state.advance();
                        Ok(Token::new(
                            TokenKind::QuestionQuestion,
                            state.current_span(start_pos, start_col),
                        ))
                    } else {
                        Ok(Token::new(
                            TokenKind::Question,
                            state.current_span(start_pos, start_col),
                        ))
                    }
                }
                '(' => {
                    state.advance();
                    Ok(Token::new(
                        TokenKind::LParen,
                        state.current_span(start_pos, start_col),
                    ))
                }
                ')' => {
                    state.advance();
                    Ok(Token::new(
                        TokenKind::RParen,
                        state.current_span(start_pos, start_col),
                    ))
                }
                '{' => {
                    state.advance();
                    Ok(Token::new(
                        TokenKind::LBrace,
                        state.current_span(start_pos, start_col),
                    ))
                }
                '}' => {
                    state.advance();
                    Ok(Token::new(
                        TokenKind::RBrace,
                        state.current_span(start_pos, start_col),
                    ))
                }
                '[' => {
                    state.advance();
                    Ok(Token::new(
                        TokenKind::LBracket,
                        state.current_span(start_pos, start_col),
                    ))
                }
                ']' => {
                    state.advance();
                    Ok(Token::new(
                        TokenKind::RBracket,
                        state.current_span(start_pos, start_col),
                    ))
                }
                ',' => {
                    state.advance();
                    Ok(Token::new(
                        TokenKind::Comma,
                        state.current_span(start_pos, start_col),
                    ))
                }
                ';' => {
                    state.advance();
                    Ok(Token::new(
                        TokenKind::Semicolon,
                        state.current_span(start_pos, start_col),
                    ))
                }
                '.' => {
                    state.advance();
                    Ok(Token::new(
                        TokenKind::Dot,
                        state.current_span(start_pos, start_col),
                    ))
                }
                '^' => {
                    state.advance();
                    Ok(Token::new(
                        TokenKind::Caret,
                        state.current_span(start_pos, start_col),
                    ))
                }
                '#' => {
                    state.advance();
                    Ok(Token::new(
                        TokenKind::Hash,
                        state.current_span(start_pos, start_col),
                    ))
                }
                '@' => {
                    state.advance();
                    Ok(Token::new(
                        TokenKind::At,
                        state.current_span(start_pos, start_col),
                    ))
                }
                _ => {
                    state.advance();
                    Err(LexError::InvalidChar {
                        ch,
                        line: start_line,
                        col: start_col,
                        pos: start_pos,
                    })
                }
            };

            match result {
                Ok(token) => tokens.push(Ok(token)),
                Err(e) => {
                    tokens.push(Err(e));
                }
            }
        }

        tokens
    }
}

impl Default for Lexer {
    fn default() -> Self {
        Self::new()
    }
}

pub fn tokenize(source: &str) -> Vec<Result<Token, LexError>> {
    Lexer::tokenize(source)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn tokenize_ok(source: &str) -> Vec<Token> {
        Lexer::tokenize(source)
            .into_iter()
            .map(|r| r.expect("expected successful tokenization"))
            .collect()
    }

    #[allow(dead_code)]
    fn first_kind(tokens: &[Token]) -> &TokenKind {
        &tokens.first().expect("expected at least one token").kind
    }

    #[test]
    fn test_keywords() {
        let keywords = [
            "fn", "ret", "use", "pub", "mut", "type", "act", "state", "event", "on", "spawn",
            "async", "fix", "if", "else", "loop", "defer", "const", "void", "in", "is", "as",
        ];
        for kw in &keywords {
            let tokens = tokenize_ok(kw);
            assert!(tokens[0].is_keyword(), "expected '{}' to be a keyword", kw);
        }
    }

    #[test]
    fn test_identifiers() {
        let tokens = tokenize_ok("foo bar_baz x123 _thing");
        assert!(matches!(tokens[0].kind, TokenKind::Identifier(ref s) if s == "foo"));
        assert!(matches!(tokens[1].kind, TokenKind::Identifier(ref s) if s == "bar_baz"));
        assert!(matches!(tokens[2].kind, TokenKind::Identifier(ref s) if s == "x123"));
        assert!(matches!(tokens[3].kind, TokenKind::Identifier(ref s) if s == "_thing"));
    }

    #[test]
    fn test_underscore() {
        let tokens = tokenize_ok("_");
        assert!(matches!(tokens[0].kind, TokenKind::Underscore));
    }

    #[test]
    fn test_int_decimal() {
        let tokens = tokenize_ok("42 0 9999");
        assert!(matches!(tokens[0].kind, TokenKind::IntLiteral(42)));
        assert!(matches!(tokens[1].kind, TokenKind::IntLiteral(0)));
        assert!(matches!(tokens[2].kind, TokenKind::IntLiteral(9999)));
    }

    #[test]
    fn test_int_hex() {
        let tokens = tokenize_ok("0xFF 0x00 0xABCD");
        assert!(matches!(tokens[0].kind, TokenKind::IntLiteral(255)));
        assert!(matches!(tokens[1].kind, TokenKind::IntLiteral(0)));
        assert!(matches!(tokens[2].kind, TokenKind::IntLiteral(0xABCD)));
    }

    #[test]
    fn test_int_binary() {
        let tokens = tokenize_ok("0b1010 0b0 0b11111111");
        assert!(matches!(tokens[0].kind, TokenKind::IntLiteral(10)));
        assert!(matches!(tokens[1].kind, TokenKind::IntLiteral(0)));
        assert!(matches!(tokens[2].kind, TokenKind::IntLiteral(255)));
    }

    #[test]
    fn test_int_with_underscores() {
        let tokens = tokenize_ok("1_000_000");
        assert!(matches!(tokens[0].kind, TokenKind::IntLiteral(1_000_000)));
    }

    #[test]
    fn test_float() {
        let tokens = tokenize_ok("3.14 0.0 1e10 2.5e-3");
        assert!(matches!(tokens[0].kind, TokenKind::FloatLiteral(ref s) if s == "3.14"));
        assert!(matches!(tokens[1].kind, TokenKind::FloatLiteral(ref s) if s == "0.0"));
        assert!(matches!(tokens[2].kind, TokenKind::FloatLiteral(ref s) if s == "1e10"));
        assert!(matches!(tokens[3].kind, TokenKind::FloatLiteral(ref s) if s == "2.5e-3"));
    }

    #[test]
    fn test_string_literal() {
        let tokens = tokenize_ok(r#""hello""world""#);
        assert!(matches!(tokens[0].kind, TokenKind::StringLiteral(ref s) if s == "hello"));
        assert!(matches!(tokens[1].kind, TokenKind::StringLiteral(ref s) if s == "world"));
    }

    #[test]
    fn test_string_escapes() {
        let tokens = tokenize_ok(r#""hello\nworld""hello\ttab""#);
        assert!(matches!(tokens[0].kind, TokenKind::StringLiteral(ref s) if s == "hello\nworld"));
        assert!(matches!(tokens[1].kind, TokenKind::StringLiteral(ref s) if s == "hello\ttab"));
    }

    #[test]
    fn test_string_unicode_escape() {
        let tokens = tokenize_ok(r#""\u{0041}""#);
        assert!(matches!(tokens[0].kind, TokenKind::StringLiteral(ref s) if s == "A"));
    }

    #[test]
    fn test_bool_and_null() {
        let tokens = tokenize_ok("true false null");
        assert!(matches!(tokens[0].kind, TokenKind::BoolLiteral(true)));
        assert!(matches!(tokens[1].kind, TokenKind::BoolLiteral(false)));
        assert!(matches!(tokens[2].kind, TokenKind::Null));
    }

    #[test]
    fn test_operators() {
        let tokens = tokenize_ok("+ - * / % == != < > <= >= && || ! |> := ?? ? -> => =");
        let expected = [
            TokenKind::Plus,
            TokenKind::Minus,
            TokenKind::Star,
            TokenKind::Slash,
            TokenKind::Percent,
            TokenKind::EqEq,
            TokenKind::BangEq,
            TokenKind::Lt,
            TokenKind::Gt,
            TokenKind::LtEq,
            TokenKind::GtEq,
            TokenKind::AmpAmp,
            TokenKind::PipePipe,
            TokenKind::Bang,
            TokenKind::PipeGt,
            TokenKind::Walrus,
            TokenKind::QuestionQuestion,
            TokenKind::Question,
            TokenKind::Arrow,
            TokenKind::FatArrow,
            TokenKind::Assign,
        ];
        for (i, expected_kind) in expected.iter().enumerate() {
            assert_eq!(tokens[i].kind, *expected_kind, "mismatch at token {}", i);
        }
    }

    #[test]
    fn test_delimiters() {
        let tokens = tokenize_ok("( ) { } [ ] , ; : :: . @");
        let expected = [
            TokenKind::LParen,
            TokenKind::RParen,
            TokenKind::LBrace,
            TokenKind::RBrace,
            TokenKind::LBracket,
            TokenKind::RBracket,
            TokenKind::Comma,
            TokenKind::Semicolon,
            TokenKind::Colon,
            TokenKind::ColonColon,
            TokenKind::Dot,
            TokenKind::At,
        ];
        for (i, expected_kind) in expected.iter().enumerate() {
            assert_eq!(tokens[i].kind, *expected_kind, "mismatch at token {}", i);
        }
    }

    #[test]
    fn test_capability_sigils() {
        let tokens = tokenize_ok("^ # &");
        assert!(matches!(tokens[0].kind, TokenKind::Caret));
        assert!(matches!(tokens[1].kind, TokenKind::Hash));
        assert!(matches!(tokens[2].kind, TokenKind::Amp));
    }

    #[test]
    fn test_pipe_token() {
        let tokens = tokenize_ok("|");
        assert!(matches!(tokens[0].kind, TokenKind::Pipe));
    }

    #[test]
    fn test_line_comment() {
        let tokens = tokenize_ok("x // this is a comment\ny");
        assert!(matches!(tokens[0].kind, TokenKind::Identifier(_)));
        assert!(matches!(tokens[1].kind, TokenKind::Identifier(_)));
        assert_eq!(tokens.len(), 3);
    }

    #[test]
    fn test_block_comment() {
        let tokens = tokenize_ok("x /* comment */ y");
        assert!(matches!(tokens[0].kind, TokenKind::Identifier(_)));
        assert!(matches!(tokens[1].kind, TokenKind::Identifier(_)));
        assert_eq!(tokens.len(), 3);
    }

    #[test]
    fn test_nested_block_comment() {
        let tokens = tokenize_ok("x /* outer /* inner */ still outer */ y");
        assert!(matches!(tokens[0].kind, TokenKind::Identifier(_)));
        assert!(matches!(tokens[1].kind, TokenKind::Identifier(_)));
        assert_eq!(tokens.len(), 3);
    }

    #[test]
    fn test_span_tracking() {
        let tokens = tokenize_ok("fn");
        let tok = &tokens[0];
        assert_eq!(tok.span.start, 0);
        assert_eq!(tok.span.end, 2);
        assert_eq!(tok.span.line, 1);
        assert_eq!(tok.span.col, 1);
    }

    #[test]
    fn test_span_multiline() {
        let tokens = tokenize_ok("x\ny");
        let tok_x = &tokens[0];
        let tok_y = &tokens[1];
        assert_eq!(tok_x.span.line, 1);
        assert_eq!(tok_y.span.line, 2);
        assert_eq!(tok_y.span.col, 1);
    }

    #[test]
    fn test_error_invalid_char() {
        let results = Lexer::tokenize("$");
        assert!(results[0].is_err());
        match &results[0] {
            Err(LexError::InvalidChar { ch, .. }) => assert_eq!(*ch, '$'),
            _ => panic!("expected InvalidChar error"),
        }
    }

    #[test]
    fn test_error_unterminated_string() {
        let results = Lexer::tokenize(r#""hello"#);
        assert!(results[0].is_err());
        match &results[0] {
            Err(LexError::UnterminatedString { .. }) => {}
            _ => panic!("expected UnterminatedString error"),
        }
    }

    #[test]
    fn test_error_unterminated_block_comment() {
        let results = Lexer::tokenize("/* never closed");
        assert!(results[0].is_err());
        match &results[0] {
            Err(LexError::UnterminatedBlockComment { .. }) => {}
            _ => panic!("expected UnterminatedBlockComment error"),
        }
    }

    #[test]
    fn test_error_invalid_escape() {
        let results = Lexer::tokenize(r#""\z""#);
        assert!(results[0].is_err());
        match &results[0] {
            Err(LexError::InvalidEscape { ch, .. }) => assert_eq!(*ch, 'z'),
            _ => panic!("expected InvalidEscape error"),
        }
    }

    #[test]
    fn test_eof() {
        let tokens = tokenize_ok("");
        assert_eq!(tokens.len(), 1);
        assert!(matches!(tokens[0].kind, TokenKind::Eof));
    }

    #[test]
    fn test_complex_source() {
        let source = r#"
            fn add(a: i32, b: i32) -> i32 {
                ret a + b
            }
        "#;
        let tokens = tokenize_ok(source);
        let kinds: Vec<&TokenKind> = tokens.iter().map(|t| &t.kind).collect();
        assert!(matches!(kinds[0], TokenKind::Fn));
        assert!(matches!(kinds[1], TokenKind::Identifier(_)));
        assert!(matches!(kinds[2], TokenKind::LParen));
        assert!(matches!(kinds.last(), Some(TokenKind::Eof)));
    }
}
