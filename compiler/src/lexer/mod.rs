//! Lexical analysis: source text to a stream of tokens.
//!
//! Token and span types live in the `token` submodule.

/// Token representation and source spans.
pub mod token;

use token::{Span, Token, TokenKind};

/// Failures reported while scanning source text.
///
/// Lexing does not stop at the first error: [`Lexer::tokenize`] returns one
/// result per token so that later tokens are still available for parsing.
#[derive(Debug, Clone, thiserror::Error, PartialEq, Eq)]
pub enum LexError {
    /// A character that cannot begin any token.
    #[error("invalid character '{ch}' at line {line}, column {col}")]
    InvalidChar {
        /// The offending character.
        ch: char,
        /// 1-based line number.
        line: u32,
        /// 1-based column number.
        col: u32,
        /// Byte offset of the character.
        pos: usize,
    },
    /// A string literal ran to the end of the line or file without a closing
    /// quote.
    #[error("unterminated string literal at line {line}, column {col}")]
    UnterminatedString {
        /// 1-based line number where the literal started.
        line: u32,
        /// 1-based column number where the literal started.
        col: u32,
        /// Byte offset where the literal started.
        pos: usize,
    },
    /// A numeric literal that could not be parsed.
    #[error("invalid number literal '{text}' at line {line}, column {col}")]
    InvalidNumber {
        /// The literal's source text.
        text: String,
        /// 1-based line number where the literal started.
        line: u32,
        /// 1-based column number where the literal started.
        col: u32,
        /// Byte offset where the literal started.
        pos: usize,
    },
    /// A block comment that was never closed.
    #[error("unterminated block comment at line {line}, column {col}")]
    UnterminatedBlockComment {
        /// 1-based line number where the comment started.
        line: u32,
        /// 1-based column number where the comment started.
        col: u32,
        /// Byte offset where the comment started.
        pos: usize,
    },
    /// An unknown backslash escape inside a string literal.
    #[error("invalid escape sequence '\\{ch}' at line {line}, column {col}")]
    InvalidEscape {
        /// The character following the backslash.
        ch: char,
        /// 1-based line number where the escape appeared.
        line: u32,
        /// 1-based column number where the escape appeared.
        col: u32,
        /// Byte offset of the backslash.
        pos: usize,
    },
    /// A `\\u{...}` escape that is malformed or out of range.
    #[error("invalid unicode escape at line {line}, column {col}")]
    InvalidUnicodeEscape {
        /// 1-based line number where the escape appeared.
        line: u32,
        /// 1-based column number where the escape appeared.
        col: u32,
        /// Byte offset of the backslash.
        pos: usize,
    },
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

// --- Lookup tables for ASCII fast-path (stable, no nightly SIMD) ---
// These tables enable branchless classification and are auto-vectorizable.
// For hot loops we check `b < 128` then table lookup; otherwise fallback to Unicode.

const fn build_ident_continue_table() -> [bool; 256] {
    let mut tbl = [false; 256];
    let mut i = 0;
    while i < 256 {
        let b = i as u8;
        tbl[i] = matches!(b, b'A'..=b'Z' | b'a'..=b'z' | b'0'..=b'9' | b'_');
        i += 1;
    }
    tbl
}

const fn build_digit_table() -> [bool; 256] {
    let mut tbl = [false; 256];
    let mut i = 0;
    while i < 256 {
        tbl[i] = (i as u8).is_ascii_digit();
        i += 1;
    }
    tbl
}

const fn build_hex_table() -> [bool; 256] {
    let mut tbl = [false; 256];
    let mut i = 0;
    while i < 256 {
        let b = i as u8;
        tbl[i] = b.is_ascii_hexdigit();
        i += 1;
    }
    tbl
}

const fn build_whitespace_table() -> [bool; 256] {
    let mut tbl = [false; 256];
    tbl[b' ' as usize] = true;
    tbl[b'\t' as usize] = true;
    tbl[b'\n' as usize] = true;
    tbl[b'\r' as usize] = true;
    // Note: other Unicode whitespaces (e.g. U+00A0) are handled via fallback `char::is_whitespace`
    tbl
}

static IDENT_CONTINUE_TABLE: [bool; 256] = build_ident_continue_table();
static DIGIT_TABLE: [bool; 256] = build_digit_table();
static HEX_TABLE: [bool; 256] = build_hex_table();
static WHITESPACE_TABLE: [bool; 256] = build_whitespace_table();

struct LexerState<'a> {
    source: &'a str,
    // Keep raw bytes for SIMD-friendly ASCII fast-paths.
    // `position` is always a valid UTF-8 boundary (byte offset).
    bytes: &'a [u8],
    position: usize,
    line: u32,
    column: u32,
}

impl<'a> LexerState<'a> {
    #[inline]
    fn new(source: &'a str) -> Self {
        Self {
            source,
            bytes: source.as_bytes(),
            position: 0,
            line: 1,
            column: 1,
        }
    }

    #[inline]
    fn peek(&self) -> Option<char> {
        self.source[self.position..].chars().next()
    }

    #[inline]
    fn peek_byte(&self) -> Option<u8> {
        self.bytes.get(self.position).copied()
    }

    #[inline]
    fn advance(&mut self) -> Option<char> {
        let ch = self.source[self.position..].chars().next()?;
        let len = ch.len_utf8();
        self.position += len;
        if ch == '\n' {
            self.line += 1;
            self.column = 1;
        } else {
            self.column += 1;
        }
        Some(ch)
    }

    // Fast byte advance for known ASCII (1 byte, no newline handling caller must update line/col).
    #[inline(always)]
    fn advance_ascii_byte(&mut self, b: u8) {
        self.position += 1;
        if b == b'\n' {
            self.line += 1;
            self.column = 1;
        } else {
            self.column += 1;
        }
    }

    #[inline]
    fn current_span(&self, start_pos: usize, start_col: u32) -> Span {
        Span::new(start_pos, self.position, self.line, start_col)
    }

    // --- Hot path: whitespace skipping ---------------------------------------
    // ASCII fast-path: bulk-scan bytes using lookup table. Falls back to
    // `char::is_whitespace` for non-ASCII (e.g. U+00A0, U+2003).
    // Uses `WHITESPACE_TABLE` + explicit byte compare so LLVM can vectorize
    // the loop (effectively SIMD via auto-vectorization / memchr idiom).
    #[inline]
    fn skip_whitespace(&mut self) {
        let len = self.bytes.len();
        while self.position < len {
            let b = self.bytes[self.position];
            if b < 128 {
                if WHITESPACE_TABLE[b as usize] {
                    // Inline advance for ASCII whitespace
                    self.position += 1;
                    if b == b'\n' {
                        self.line += 1;
                        self.column = 1;
                    } else {
                        self.column += 1;
                    }
                    // --- Bulk ASCII whitespace chunk ---
                    // After one hit, try to consume a run without per-char decode.
                    // This loop is deliberately simple so LLVM vectorizes it.
                    // Equivalent to `memchr` for non-whitespace.
                    while self.position < len {
                        let b2 = self.bytes[self.position];
                        if b2 < 128 {
                            if WHITESPACE_TABLE[b2 as usize] {
                                self.position += 1;
                                if b2 == b'\n' {
                                    self.line += 1;
                                    self.column = 1;
                                } else {
                                    self.column += 1;
                                }
                                continue;
                            } else {
                                break;
                            }
                        } else {
                            break; // non-ASCII -> fallback below
                        }
                    }
                    // Check if next char is Unicode whitespace
                    if self.position < len && self.bytes[self.position] >= 128 {
                        if let Some(ch) = self.peek() {
                            if ch.is_whitespace() {
                                self.advance();
                                continue;
                            }
                        }
                    }
                    break;
                } else {
                    break;
                }
            } else {
                // Non-ASCII: decode and check full Unicode whitespace
                if let Some(ch) = self.peek() {
                    if ch.is_whitespace() {
                        self.advance();
                        continue;
                    }
                }
                break;
            }
        }
    }

    #[inline]
    fn skip_line_comment(&mut self) {
        // Fast-path: scan for newline using memchr idiom (byte search).
        // `position` is already after `//`.
        let remaining = &self.bytes[self.position..];
        // `iter().position` on bytes is lowered to `memchr` on most targets and is SIMD-accelerated.
        if let Some(offset) = remaining.iter().position(|&b| b == b'\n') {
            // Count columns: comments don't contain newlines except terminator, so column += offset
            // (We still need line/col accurate for next token)
            self.position += offset;
            self.column += offset as u32;
            // Leave '\n' to be consumed by skip_whitespace (which handles line increment)
        } else {
            // No newline till EOF
            let remaining_len = remaining.len();
            self.position += remaining_len;
            self.column += remaining_len as u32;
        }
    }

    #[inline]
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

    // --- Hot path: string literal -------------------------------------------
    // ASCII fast-path: use byte search (`memchr` idiom) to jump between
    // delimiters. Only falls back to char-by-char for escapes and Unicode.
    #[inline]
    fn lex_string(&mut self) -> Result<TokenKind, LexError> {
        let start_line = self.line;
        let start_col = self.column;
        let start_pos = self.position;

        // Use owned String but extend via `push_str` on slices to avoid per-char allocation.
        // `Cow` would be possible if `TokenKind` were `Cow<'a,str>`, but we keep owned `String`
        // for API stability and still avoid intermediate allocations by slicing.
        let mut value = String::new();
        // Heuristic: reserve a bit to reduce realloc for long strings
        // (cheap, and helps for bulk literals)
        // We don't know length; reserve 32 as default.
        value.reserve(32);

        loop {
            // Fast scan for next `"` or `\` using byte search.
            // This is the SIMD fast-path: `memchr`/`memchr2` style search over bytes.
            let remaining_bytes = &self.bytes[self.position..];
            if remaining_bytes.is_empty() {
                return Err(LexError::UnterminatedString {
                    line: start_line,
                    col: start_col,
                    pos: start_pos,
                });
            }
            // Find delimiter: position of `"` or `\`
            // Manual loop is auto-vectorized; equivalent to `memchr2`.
            let mut delim_offset: Option<(usize, u8)> = None;
            // Process in chunks of 16 for better vectorization hint
            // We keep it simple but add `#[inline]` and use `position` search.
            // Using `iter().position` with predicate is recognized as memchr.
            let search_len = remaining_bytes.len();
            let mut i = 0;
            // Unrolled 8-byte fast check before falling back to position()
            // This helps LLVM emit SIMD for long strings.
            while i + 8 <= search_len {
                let chunk = &remaining_bytes[i..i + 8];
                // Check chunk for `"` or `\`
                // Using lookup to let compiler vectorize
                let mut found = None;
                for (j, &b) in chunk.iter().enumerate() {
                    if b == b'"' || b == b'\\' {
                        found = Some((i + j, b));
                        break;
                    }
                }
                if let Some(f) = found {
                    delim_offset = Some(f);
                    break;
                }
                // Also quickly skip if chunk is all ASCII non-delimiter and no high bit?
                // If any byte >=128, we still treat as content; slicing handles UTF-8.
                i += 8;
            }
            if delim_offset.is_none() {
                // Tail search
                for (j, &b) in remaining_bytes[i..].iter().enumerate() {
                    if b == b'"' || b == b'\\' {
                        delim_offset = Some((i + j, b));
                        break;
                    }
                }
            }

            match delim_offset {
                None => {
                    // No delimiter till EOF -> unterminated, but push remaining content for error recovery?
                    return Err(LexError::UnterminatedString {
                        line: start_line,
                        col: start_col,
                        pos: start_pos,
                    });
                }
                Some((offset, b'"')) => {
                    // Chunk before `"` is pure content (may contain UTF-8, but no escapes/delims)
                    if offset > 0 {
                        let chunk_str = &self.source[self.position..self.position + offset];
                        // Update line/col for chunk: count newlines
                        // Strings rarely contain newlines; fast count via bytes
                        let chunk_bytes = &remaining_bytes[..offset];
                        let mut newlines = 0u32;
                        let mut last_nl_pos = 0usize;
                        for (idx, &cb) in chunk_bytes.iter().enumerate() {
                            if cb == b'\n' {
                                newlines += 1;
                                last_nl_pos = idx;
                            }
                        }
                        if newlines > 0 {
                            self.line += newlines;
                            // column = bytes after last newline +1
                            self.column = (offset - last_nl_pos) as u32;
                        } else {
                            // column tracks char count, but for non-newline chunk, bytes == chars for ASCII;
                            // for Unicode we need char count. Use `chars().count()` only when non-ASCII present.
                            let has_non_ascii = chunk_bytes.iter().any(|&c| c >= 128);
                            if has_non_ascii {
                                self.column += chunk_str.chars().count() as u32;
                            } else {
                                self.column += offset as u32;
                            }
                        }
                        value.push_str(chunk_str);
                        self.position += offset;
                    }
                    // Consume closing `"`
                    self.position += 1;
                    self.column += 1;
                    break;
                }
                Some((offset, b'\\')) => {
                    // Push content up to `\`
                    if offset > 0 {
                        let chunk_str = &self.source[self.position..self.position + offset];
                        let chunk_bytes = &remaining_bytes[..offset];
                        let has_non_ascii = chunk_bytes.iter().any(|&c| c >= 128);
                        if chunk_bytes.contains(&b'\n') {
                            // Rare: handle newlines inside string
                            let mut newlines = 0u32;
                            let mut last_nl_pos = 0usize;
                            for (idx, &cb) in chunk_bytes.iter().enumerate() {
                                if cb == b'\n' {
                                    newlines += 1;
                                    last_nl_pos = idx;
                                }
                            }
                            self.line += newlines;
                            self.column = (offset - last_nl_pos) as u32;
                        } else if has_non_ascii {
                            self.column += chunk_str.chars().count() as u32;
                        } else {
                            self.column += offset as u32;
                        }
                        value.push_str(chunk_str);
                        self.position += offset;
                    }
                    // Now at `\`, handle escape (fallback to original logic but using bytes for speed)
                    // Consume `\`
                    self.position += 1;
                    self.column += 1;
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
                            let c = char::from_u32(code_point).ok_or({
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
                    // Continue loop to find next delimiter
                }
                Some((_, _)) => unreachable!(),
            }
        }
        Ok(TokenKind::StringLiteral(value))
    }

    #[inline]
    fn lex_number(&mut self, first: char) -> Result<TokenKind, LexError> {
        let start_col = self.column - 1;
        let start_pos = self.position - 1;
        let start_line = self.line;

        if first == '0' {
            match self.peek_byte() {
                Some(b'x') | Some(b'X') => {
                    self.advance_ascii_byte(self.bytes[self.position]);
                    return self.lex_hex_number(start_pos, start_line, start_col);
                }
                Some(b'b') | Some(b'B') => {
                    self.advance_ascii_byte(self.bytes[self.position]);
                    return self.lex_binary_number(start_pos, start_line, start_col);
                }
                _ => {}
            }
        }

        // --- ASCII fast-path for decimal digits + underscores ---
        // Collect digits via byte scan, but avoid per-char String push; track byte range then slice.
        let digit_start = start_pos;
        // We have already consumed `first` (at start_pos). `position` points after it.
        // Bulk scan forward for [0-9_]
        let mut end = self.position;
        let len = self.bytes.len();
        while end < len {
            let b = self.bytes[end];
            if b < 128 {
                if DIGIT_TABLE[b as usize] || b == b'_' {
                    end += 1;
                } else {
                    break;
                }
            } else {
                break;
            }
        }
        // Update position/column in bulk
        let consumed = end - self.position;
        if consumed > 0 {
            self.position = end;
            self.column += consumed as u32;
        }
        // Slice for later cleaning; keep original digit string view
        // We need digits String for further_float detection; we'll build from slice

        // Check for fractional part: '.' followed by digit
        if self.peek_byte() == Some(b'.') {
            // Use byte lookahead for char after '.'
            let after_dot_pos = self.position + 1;
            if after_dot_pos < len {
                let after = self.bytes[after_dot_pos];
                let is_digit_after = after < 128 && DIGIT_TABLE[after as usize];
                // For non-ASCII after dot, we fallback to char check (should be digit)
                let fallback_is_digit = if after >= 128 {
                    self.source[after_dot_pos..]
                        .chars()
                        .next()
                        .is_some_and(|c| c.is_ascii_digit())
                } else {
                    false
                };
                if is_digit_after || fallback_is_digit {
                    // Consume '.' and fractional digits
                    self.advance_ascii_byte(b'.');
                    // Scan fractional digits
                    let mut frac_end = self.position;
                    while frac_end < len {
                        let b = self.bytes[frac_end];
                        if b < 128 {
                            if DIGIT_TABLE[b as usize] || b == b'_' {
                                frac_end += 1;
                            } else {
                                break;
                            }
                        } else {
                            break;
                        }
                    }
                    let frac_consumed = frac_end - self.position;
                    self.position = frac_end;
                    self.column += frac_consumed as u32;

                    // Exponent part
                    if matches!(self.peek_byte(), Some(b'e') | Some(b'E')) {
                        let e_byte = self.bytes[self.position];
                        self.advance_ascii_byte(e_byte);
                        if matches!(self.peek_byte(), Some(b'+') | Some(b'-')) {
                            let sign = self.bytes[self.position];
                            self.advance_ascii_byte(sign);
                        }
                        let mut exp_end = self.position;
                        while exp_end < len {
                            let b = self.bytes[exp_end];
                            if b < 128 {
                                if DIGIT_TABLE[b as usize] || b == b'_' {
                                    exp_end += 1;
                                } else {
                                    break;
                                }
                            } else {
                                break;
                            }
                        }
                        let exp_consumed = exp_end - self.position;
                        self.position = exp_end;
                        self.column += exp_consumed as u32;
                    }
                    let raw = &self.source[digit_start..self.position];
                    let cleaned: String = raw.chars().filter(|c| *c != '_').collect();
                    return Ok(TokenKind::FloatLiteral(cleaned));
                }
            }
        }

        if matches!(self.peek_byte(), Some(b'e') | Some(b'E')) {
            let e_byte = self.bytes[self.position];
            self.advance_ascii_byte(e_byte);
            if matches!(self.peek_byte(), Some(b'+') | Some(b'-')) {
                let sign = self.bytes[self.position];
                self.advance_ascii_byte(sign);
            }
            let mut exp_end = self.position;
            while exp_end < len {
                let b = self.bytes[exp_end];
                if b < 128 {
                    if DIGIT_TABLE[b as usize] || b == b'_' {
                        exp_end += 1;
                    } else {
                        break;
                    }
                } else {
                    break;
                }
            }
            let exp_consumed = exp_end - self.position;
            self.position = exp_end;
            self.column += exp_consumed as u32;
            let raw = &self.source[digit_start..self.position];
            let cleaned: String = raw.chars().filter(|c| *c != '_').collect();
            return Ok(TokenKind::FloatLiteral(cleaned));
        }

        let raw = &self.source[digit_start..self.position];
        let cleaned: String = raw.chars().filter(|c| *c != '_').collect();
        let value = cleaned
            .parse::<i64>()
            .map_err(|_| LexError::InvalidNumber {
                text: cleaned,
                line: start_line,
                col: start_col,
                pos: start_pos,
            })?;
        Ok(TokenKind::IntLiteral(value))
    }

    #[inline]
    fn lex_hex_number(
        &mut self,
        start_pos: usize,
        start_line: u32,
        start_col: u32,
    ) -> Result<TokenKind, LexError> {
        let hex_start = self.position;
        let len = self.bytes.len();
        let mut end = self.position;
        while end < len {
            let b = self.bytes[end];
            if b < 128 {
                if HEX_TABLE[b as usize] || b == b'_' {
                    end += 1;
                } else {
                    break;
                }
            } else {
                break;
            }
        }
        let raw_slice = &self.source[hex_start..end];
        let hex: String = raw_slice.chars().filter(|c| *c != '_').collect();
        let consumed = end - self.position;
        self.position = end;
        self.column += consumed as u32;
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

    #[inline]
    fn lex_binary_number(
        &mut self,
        start_pos: usize,
        start_line: u32,
        start_col: u32,
    ) -> Result<TokenKind, LexError> {
        let bin_start = self.position;
        let len = self.bytes.len();
        let mut end = self.position;
        while end < len {
            let b = self.bytes[end];
            if b == b'0' || b == b'1' || b == b'_' {
                end += 1;
            } else {
                break;
            }
        }
        let raw_slice = &self.source[bin_start..end];
        let bits: String = raw_slice.chars().filter(|c| *c != '_').collect();
        let consumed = end - self.position;
        self.position = end;
        self.column += consumed as u32;
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

    #[inline]
    #[allow(dead_code)]
    fn peek_at(&self, pos: usize) -> Option<char> {
        self.source[pos..].chars().next()
    }

    // --- Hot path: identifier / keyword -------------------------------------
    // ASCII fast-path: bulk scan using `IDENT_CONTINUE_TABLE`. For non-ASCII,
    // fallback to `is_alphanumeric` (Unicode correct). Uses `&str` slice for
    // keyword match to avoid allocating intermediate `String` per char.
    #[inline]
    fn lex_identifier_or_keyword(&mut self, first: char) -> TokenKind {
        // `first` already consumed; `start_pos` is one char before `position`
        let start_pos = self.position - first.len_utf8();
        let start_col = self.column - 1; // column already advanced for first char
                                         // Fast bulk scan for continuation bytes
        let len = self.bytes.len();
        let mut end = self.position;
        // ASCII fast chunk: 8 bytes at a time
        while end < len {
            let b = self.bytes[end];
            if b < 128 {
                if IDENT_CONTINUE_TABLE[b as usize] {
                    end += 1;
                    continue;
                } else {
                    break;
                }
            } else {
                // Unicode fallback: decode char
                if let Some(ch) = self.source[end..].chars().next() {
                    if ch.is_alphanumeric() || ch == '_' {
                        end += ch.len_utf8();
                        continue;
                    }
                }
                break;
            }
        }
        // Update state: column tracks char count
        let ident_slice = &self.source[start_pos..end];
        // Fast column update: if ASCII-only, column = start_col + byte_len
        // else need char count
        let has_non_ascii = ident_slice.as_bytes().iter().any(|&b| b >= 128);
        if has_non_ascii {
            let char_len = ident_slice.chars().count() as u32;
            self.column = start_col + char_len;
        } else {
            self.column = start_col + (end - start_pos) as u32;
        }
        self.position = end;

        if ident_slice == "_" {
            return TokenKind::Underscore;
        }

        // Keyword match on `&str` slice (no allocation). `Cow` could be used if caller wants
        // borrowed `TokenKind`, but `TokenKind` owns `String` for `Identifier`, so we allocate
        // only on non-keyword path and directly from slice.
        match ident_slice {
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
            _ => TokenKind::Identifier(ident_slice.to_owned()),
        }
    }
}

/// Turns Morph source text into a token stream.
///
/// The lexer is stateless: all scanning state is local to each call, so a
/// [`Lexer`] can be created and discarded freely.
pub struct Lexer;

impl Lexer {
    /// Creates a lexer.
    pub fn new() -> Self {
        Self
    }

    /// Scans `source` into tokens.
    ///
    /// Returns one entry per token in source order. A lexical error occupies
    /// the position of the token it interrupted, and scanning continues after
    /// it where possible. The stream always ends with [`TokenKind::Eof`].
    #[inline]
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
                    // Unicode fallback: advance and check if it's part of identifier/whitespace
                    // For true invalid char, report error.
                    // First check if char is alphanumeric (could be unicode ident start) – but
                    // our main loop only handles ASCII start; handle unicode ident start here.
                    if ch.is_alphabetic() || ch == '_' {
                        state.advance();
                        let kind = state.lex_identifier_or_keyword(ch);
                        Ok(Token::new(kind, state.current_span(start_pos, start_col)))
                    } else {
                        state.advance();
                        Err(LexError::InvalidChar {
                            ch,
                            line: start_line,
                            col: start_col,
                            pos: start_pos,
                        })
                    }
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
    /// Creates a lexer, exactly as [`Lexer::new`] does.
    fn default() -> Self {
        Self::new()
    }
}

/// Convenience wrapper around [`Lexer::tokenize`].
///
/// Equivalent to calling [`Lexer::tokenize`] directly.
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
