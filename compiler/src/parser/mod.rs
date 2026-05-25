use crate::ast::*;
use crate::lexer::token::{Span, Token, TokenKind};

#[derive(Debug, Clone, thiserror::Error)]
pub enum ParseError {
    #[error("unexpected token '{found}', expected {expected} at line {line}, column {col}")]
    UnexpectedToken {
        found: String,
        expected: String,
        line: u32,
        col: u32,
        span: Span,
    },
    #[error("unexpected end of file, expected {expected}")]
    UnexpectedEof { expected: String, span: Span },
    #[error("duplicate definition of '{name}' at line {line}, column {col}")]
    DuplicateDefinition {
        name: String,
        line: u32,
        col: u32,
        span: Span,
    },
    #[error("invalid expression at line {line}, column {col}")]
    InvalidExpression { line: u32, col: u32, span: Span },
}

struct Parser {
    tokens: Vec<Token>,
    pos: usize,
    errors: Vec<ParseError>,
}

impl Parser {
    fn new(tokens: Vec<Token>) -> Self {
        Self {
            tokens,
            pos: 0,
            errors: Vec::new(),
        }
    }

    fn current(&self) -> &Token {
        self.tokens.get(self.pos).unwrap_or_else(|| {
            self.tokens.last().expect("tokens should contain at least EOF")
        })
    }

    fn peek(&self) -> &TokenKind {
        &self.current().kind
    }

    fn peek_at(&self, offset: usize) -> &TokenKind {
        let idx = self.pos + offset;
        if idx < self.tokens.len() {
            &self.tokens[idx].kind
        } else {
            &TokenKind::Eof
        }
    }

    fn advance(&mut self) -> Token {
        let tok = self.current().clone();
        if self.pos < self.tokens.len() - 1 {
            self.pos += 1;
        }
        tok
    }

    fn expect(&mut self, expected: &TokenKind) -> Result<Token, ParseError> {
        let tok = self.current().clone();
        if &tok.kind == expected {
            self.advance();
            Ok(tok)
        } else {
            let span = tok.span;
            Err(ParseError::UnexpectedToken {
                found: format!("{}", tok.kind),
                expected: format!("{}", expected),
                line: span.line,
                col: span.col,
                span,
            })
        }
    }

    fn expect_identifier(&mut self) -> Result<(String, Span), ParseError> {
        let tok = self.current().clone();
        match &tok.kind {
            TokenKind::Identifier(name) => {
                let name = name.clone();
                let span = tok.span;
                self.advance();
                Ok((name, span))
            }
            _ => {
                let span = tok.span;
                Err(ParseError::UnexpectedToken {
                    found: format!("{}", tok.kind),
                    expected: "identifier".to_string(),
                    line: span.line,
                    col: span.col,
                    span,
                })
            }
        }
    }

    fn matches(&self, kind: &TokenKind) -> bool {
        self.peek() == kind
    }

    fn synchronize(&mut self) {
        while !self.matches(&TokenKind::Eof) {
            match self.peek() {
                TokenKind::Semicolon => {
                    self.advance();
                    return;
                }
                TokenKind::RBrace => {
                    self.advance();
                    return;
                }
                TokenKind::Fn
                | TokenKind::Type
                | TokenKind::Const
                | TokenKind::Use
                | TokenKind::Act
                | TokenKind::Pub => return,
                _ => {
                    self.advance();
                }
            }
        }
    }

    fn span_from(&self, start: &Token) -> Span {
        let current = self.current();
        Span {
            start: start.span.start,
            end: current.span.end,
            line: start.span.line,
            col: start.span.col,
        }
    }

    #[allow(dead_code)]
    fn parse_visibility(&mut self) -> Visibility {
        if self.matches(&TokenKind::Pub) {
            self.advance();
            Visibility::Public
        } else {
            Visibility::Private
        }
    }

    fn parse_program(&mut self) -> (Vec<Node<Item>>, Vec<ParseError>) {
        let mut items = Vec::new();
        while !self.matches(&TokenKind::Eof) {
            match self.parse_item() {
                Ok(item) => items.push(item),
                Err(e) => {
                    self.errors.push(e);
                    self.synchronize();
                }
            }
        }
        (items, std::mem::take(&mut self.errors))
    }

    fn parse_item(&mut self) -> Result<Node<Item>, ParseError> {
        let start = self.current().clone();
        match self.peek() {
            TokenKind::Fn => {
                let f = self.parse_fn_decl(Visibility::Private)?;
                Ok(Node::new(Item::FnDecl(f), self.span_from(&start)))
            }
            TokenKind::Pub => {
                self.advance();
                match self.peek() {
                    TokenKind::Fn => {
                        let f = self.parse_fn_decl(Visibility::Public)?;
                        Ok(Node::new(Item::FnDecl(f), self.span_from(&start)))
                    }
                    TokenKind::Type => {
                        let t = self.parse_type_decl(Visibility::Public)?;
                        Ok(Node::new(Item::TypeDecl(t), self.span_from(&start)))
                    }
                    TokenKind::Const => {
                        let c = self.parse_const_decl(Visibility::Public)?;
                        Ok(Node::new(Item::ConstDecl(c), self.span_from(&start)))
                    }
                    _ => {
                        let span = self.current().span;
                        Err(ParseError::UnexpectedToken {
                            found: format!("{}", self.peek()),
                            expected: "fn, type, or const".to_string(),
                            line: span.line,
                            col: span.col,
                            span,
                        })
                    }
                }
            }
            TokenKind::Type => {
                let t = self.parse_type_decl(Visibility::Private)?;
                Ok(Node::new(Item::TypeDecl(t), self.span_from(&start)))
            }
            TokenKind::Const => {
                let c = self.parse_const_decl(Visibility::Private)?;
                Ok(Node::new(Item::ConstDecl(c), self.span_from(&start)))
            }
            TokenKind::Use => {
                let u = self.parse_use_decl()?;
                Ok(Node::new(Item::UseDecl(u), self.span_from(&start)))
            }
            TokenKind::Act => {
                let a = self.parse_actor_decl()?;
                Ok(Node::new(Item::ActorDecl(a), self.span_from(&start)))
            }
            _ => {
                let span = self.current().span;
                Err(ParseError::UnexpectedToken {
                    found: format!("{}", self.peek()),
                    expected: "item declaration".to_string(),
                    line: span.line,
                    col: span.col,
                    span,
                })
            }
        }
    }

    fn parse_fn_decl(&mut self, vis: Visibility) -> Result<FnDecl, ParseError> {
        self.expect(&TokenKind::Fn)?;
        let (name, _) = self.expect_identifier()?;
        let generic_params = self.parse_generic_params()?;
        self.expect(&TokenKind::LParen)?;
        let params = self.parse_params()?;
        self.expect(&TokenKind::RParen)?;
        let return_type = if self.matches(&TokenKind::Arrow) {
            self.advance();
            Some(self.parse_type()?)
        } else {
            None
        };
        let effects = if self.matches(&TokenKind::At) {
            Some(self.parse_effect_set()?)
        } else {
            None
        };
        let body = self.parse_block_expr()?;
        Ok(FnDecl {
            visibility: vis,
            name,
            generic_params,
            params,
            return_type,
            body,
            effects,
        })
    }

    fn parse_generic_params(&mut self) -> Result<Vec<GenericParam>, ParseError> {
        if !self.matches(&TokenKind::Lt) && !self.matches(&TokenKind::LtGeneric) {
            return Ok(Vec::new());
        }
        self.advance();
        let mut params = Vec::new();
        while !self.matches(&TokenKind::Gt) && !self.matches(&TokenKind::GtGeneric) && !self.matches(&TokenKind::GtEq) {
            let (name, _) = self.expect_identifier()?;
            let constraint = if self.matches(&TokenKind::Colon) {
                self.advance();
                Some(self.parse_type()?)
            } else {
                None
            };
            params.push(GenericParam { name, constraint });
            if self.matches(&TokenKind::Comma) {
                self.advance();
            } else {
                break;
            }
        }
        if self.matches(&TokenKind::Gt) || self.matches(&TokenKind::GtGeneric) {
            self.advance();
        }
        Ok(params)
    }

    fn parse_generic_args(&mut self) -> Result<Vec<Node<Type>>, ParseError> {
        if !self.matches(&TokenKind::Lt) && !self.matches(&TokenKind::LtGeneric) {
            return Ok(Vec::new());
        }
        self.advance();
        let mut args = Vec::new();
        while !self.matches(&TokenKind::Gt) && !self.matches(&TokenKind::GtGeneric) && !self.matches(&TokenKind::GtEq) {
            args.push(self.parse_type()?);
            if self.matches(&TokenKind::Comma) {
                self.advance();
            } else {
                break;
            }
        }
        if self.matches(&TokenKind::Gt) || self.matches(&TokenKind::GtGeneric) {
            self.advance();
        }
        Ok(args)
    }

    fn parse_params(&mut self) -> Result<Vec<Node<Param>>, ParseError> {
        let mut params = Vec::new();
        while !self.matches(&TokenKind::RParen) && !self.matches(&TokenKind::Eof) {
            let start = self.current().clone();
            let (name, _) = self.expect_identifier()?;
            let type_ann = if self.matches(&TokenKind::Colon) {
                self.advance();
                Some(self.parse_type()?)
            } else {
                None
            };
            params.push(Node::new(
                Param { name, type_ann },
                self.span_from(&start),
            ));
            if self.matches(&TokenKind::Comma) {
                self.advance();
            } else {
                break;
            }
        }
        Ok(params)
    }

    fn parse_type(&mut self) -> Result<Node<Type>, ParseError> {
        let start = self.current().clone();
        let ty = self.parse_type_primary()?;
        if self.matches(&TokenKind::Question) {
            self.advance();
            return Ok(Node::new(
                Type::Optional(Box::new(ty)),
                self.span_from(&start),
            ));
        }
        Ok(ty)
    }

    fn parse_type_primary(&mut self) -> Result<Node<Type>, ParseError> {
        let start = self.current().clone();
        match self.peek().clone() {
            TokenKind::LParen => {
                self.advance();
                if self.matches(&TokenKind::RParen) {
                    self.advance();
                    return Ok(Node::new(Type::Tuple(Vec::new()), self.span_from(&start)));
                }
                let mut elements = vec![self.parse_type()?];
                while self.matches(&TokenKind::Comma) {
                    self.advance();
                    elements.push(self.parse_type()?);
                }
                self.expect(&TokenKind::RParen)?;
                Ok(Node::new(Type::Tuple(elements), self.span_from(&start)))
            }
            TokenKind::LBracket => {
                self.advance();
                let inner = self.parse_type()?;
                self.expect(&TokenKind::RBracket)?;
                Ok(Node::new(Type::Array(Box::new(inner)), self.span_from(&start)))
            }
            TokenKind::Caret => {
                self.advance();
                let inner = self.parse_type()?;
                Ok(Node::new(
                    Type::Reference {
                        cap: Capability::Iso,
                        inner: Box::new(inner),
                    },
                    self.span_from(&start),
                ))
            }
            TokenKind::Hash => {
                self.advance();
                let inner = self.parse_type()?;
                Ok(Node::new(
                    Type::Reference {
                        cap: Capability::Val,
                        inner: Box::new(inner),
                    },
                    self.span_from(&start),
                ))
            }
            TokenKind::Amp => {
                self.advance();
                let inner = self.parse_type()?;
                Ok(Node::new(
                    Type::Reference {
                        cap: Capability::Ref,
                        inner: Box::new(inner),
                    },
                    self.span_from(&start),
                ))
            }
            TokenKind::Underscore => {
                self.advance();
                Ok(Node::new(Type::Wildcard, self.span_from(&start)))
            }
            TokenKind::Identifier(name) => {
                let name = name.clone();
                self.advance();
                if self.matches(&TokenKind::Lt) || self.matches(&TokenKind::LtGeneric) {
                    let args = self.parse_generic_args()?;
                    Ok(Node::new(
                        Type::Generic { name, args },
                        self.span_from(&start),
                    ))
                } else {
                    Ok(Node::new(Type::Named(name), self.span_from(&start)))
                }
            }
            TokenKind::Void => {
                self.advance();
                Ok(Node::new(Type::Named("void".to_string()), self.span_from(&start)))
            }
            _ => {
                let span = self.current().span;
                Err(ParseError::UnexpectedToken {
                    found: format!("{}", self.peek()),
                    expected: "type".to_string(),
                    line: span.line,
                    col: span.col,
                    span,
                })
            }
        }
    }

    fn parse_effect_set(&mut self) -> Result<EffectSet, ParseError> {
        self.expect(&TokenKind::At)?;
        let mut effects = Vec::new();
        loop {
            let effect = match self.peek() {
                TokenKind::Identifier(ref s) if s == "Pure" => Effect::Pure,
                TokenKind::Identifier(ref s) if s == "IO" => Effect::IO,
                TokenKind::Identifier(ref s) if s == "Net" => Effect::Net,
                TokenKind::Identifier(ref s) if s == "Time" => Effect::Time,
                TokenKind::Identifier(ref s) if s == "System" => Effect::System,
                _ => break,
            };
            self.advance();
            effects.push(effect);
            if self.matches(&TokenKind::Comma) {
                self.advance();
            } else {
                break;
            }
        }
        Ok(EffectSet { effects })
    }

    fn parse_type_decl(&mut self, vis: Visibility) -> Result<TypeDecl, ParseError> {
        self.expect(&TokenKind::Type)?;
        let (name, _) = self.expect_identifier()?;
        let generic_params = self.parse_generic_params()?;
        self.expect(&TokenKind::Assign)?;
        let body = if self.matches(&TokenKind::LBrace) {
            self.advance();
            if matches!(self.peek_at(0), TokenKind::Identifier(_)) && self.peek_at(1) == &TokenKind::Colon {
                let fields = self.parse_struct_fields()?;
                self.expect(&TokenKind::RBrace)?;
                TypeBody::Struct(fields)
            } else {
                let variants = self.parse_enum_variants()?;
                self.expect(&TokenKind::RBrace)?;
                TypeBody::Enum(variants)
            }
        } else {
            TypeBody::Alias(self.parse_type()?)
        };
        if self.matches(&TokenKind::Semicolon) {
            self.advance();
        }
        Ok(TypeDecl {
            visibility: vis,
            name,
            generic_params,
            body,
        })
    }

    fn parse_struct_fields(&mut self) -> Result<Vec<Node<Field>>, ParseError> {
        let mut fields = Vec::new();
        while !self.matches(&TokenKind::RBrace) && !self.matches(&TokenKind::Eof) {
            let start = self.current().clone();
            let (name, _) = self.expect_identifier()?;
            self.expect(&TokenKind::Colon)?;
            let type_ann = self.parse_type()?;
            fields.push(Node::new(
                Field { name, type_ann },
                self.span_from(&start),
            ));
            if self.matches(&TokenKind::Comma) {
                self.advance();
            } else {
                break;
            }
        }
        Ok(fields)
    }

    fn parse_enum_variants(&mut self) -> Result<Vec<Node<Variant>>, ParseError> {
        let mut variants = Vec::new();
        while !self.matches(&TokenKind::RBrace) && !self.matches(&TokenKind::Eof) {
            let start = self.current().clone();
            let (name, _) = self.expect_identifier()?;
            let fields = if self.matches(&TokenKind::LParen) {
                self.advance();
                let mut field_types = Vec::new();
                while !self.matches(&TokenKind::RParen) && !self.matches(&TokenKind::Eof) {
                    field_types.push(self.parse_type()?);
                    if self.matches(&TokenKind::Comma) {
                        self.advance();
                    } else {
                        break;
                    }
                }
                self.expect(&TokenKind::RParen)?;
                field_types
            } else {
                Vec::new()
            };
            let data = if self.matches(&TokenKind::LBrace) {
                self.advance();
                let inner = self.parse_type()?;
                self.expect(&TokenKind::RBrace)?;
                Some(inner)
            } else {
                None
            };
            variants.push(Node::new(
                Variant {
                    name,
                    fields,
                    data,
                },
                self.span_from(&start),
            ));
            if self.matches(&TokenKind::Comma) {
                self.advance();
            } else {
                break;
            }
        }
        Ok(variants)
    }

    fn parse_const_decl(&mut self, vis: Visibility) -> Result<ConstDecl, ParseError> {
        self.expect(&TokenKind::Const)?;
        let (name, _) = self.expect_identifier()?;
        self.expect(&TokenKind::Colon)?;
        let type_ann = self.parse_type()?;
        self.expect(&TokenKind::Assign)?;
        let value = self.parse_expr()?;
        if self.matches(&TokenKind::Semicolon) {
            self.advance();
        }
        Ok(ConstDecl {
            visibility: vis,
            name,
            type_ann,
            value,
        })
    }

    fn parse_use_decl(&mut self) -> Result<UseDecl, ParseError> {
        self.expect(&TokenKind::Use)?;
        let (first, _) = self.expect_identifier()?;
        let mut path = vec![first];
        while self.matches(&TokenKind::ColonColon) || self.matches(&TokenKind::Dot) {
            self.advance();
            let (segment, _) = self.expect_identifier()?;
            path.push(segment);
        }
        let alias = if self.matches(&TokenKind::As) {
            self.advance();
            let (name, _) = self.expect_identifier()?;
            Some(name)
        } else {
            None
        };
        if self.matches(&TokenKind::Semicolon) {
            self.advance();
        }
        Ok(UseDecl { path, alias })
    }

    fn parse_actor_decl(&mut self) -> Result<ActorDecl, ParseError> {
        self.expect(&TokenKind::Act)?;
        let (name, _) = self.expect_identifier()?;
        let generic_params = self.parse_generic_params()?;
        self.expect(&TokenKind::LBrace)?;
        let mut members = Vec::new();
        while !self.matches(&TokenKind::RBrace) && !self.matches(&TokenKind::Eof) {
            let start = self.current().clone();
            match self.peek() {
                TokenKind::State => {
                    self.advance();
                    let (sname, _) = self.expect_identifier()?;
                    self.expect(&TokenKind::Colon)?;
                    let type_ann = self.parse_type()?;
                    let init = if self.matches(&TokenKind::Assign) {
                        self.advance();
                        Some(self.parse_expr()?)
                    } else {
                        None
                    };
                    if self.matches(&TokenKind::Semicolon) {
                        self.advance();
                    }
                    members.push(Node::new(
                        ActorMember::State {
                            name: sname,
                            type_ann,
                            init,
                        },
                        self.span_from(&start),
                    ));
                }
                TokenKind::Event => {
                    self.advance();
                    let (ename, _) = self.expect_identifier()?;
                    self.expect(&TokenKind::LParen)?;
                    let params = self.parse_params()?;
                    self.expect(&TokenKind::RParen)?;
                    if self.matches(&TokenKind::Semicolon) {
                        self.advance();
                    }
                    members.push(Node::new(
                        ActorMember::Event {
                            name: ename,
                            params,
                        },
                        self.span_from(&start),
                    ));
                }
                TokenKind::On => {
                    self.advance();
                    let (hname, _) = self.expect_identifier()?;
                    let body = self.parse_block_expr()?;
                    members.push(Node::new(
                        ActorMember::OnHandler {
                            name: hname,
                            body,
                        },
                        self.span_from(&start),
                    ));
                }
                TokenKind::Fn => {
                    let f = self.parse_fn_decl(Visibility::Private)?;
                    members.push(Node::new(
                        ActorMember::FnMember(f),
                        self.span_from(&start),
                    ));
                }
                _ => {
                    let span = self.current().span;
                    self.errors.push(ParseError::UnexpectedToken {
                        found: format!("{}", self.peek()),
                        expected: "state, event, on, or fn".to_string(),
                        line: span.line,
                        col: span.col,
                        span,
                    });
                    self.advance();
                }
            }
        }
        self.expect(&TokenKind::RBrace)?;
        Ok(ActorDecl {
            name,
            generic_params,
            members,
        })
    }

    fn parse_expr(&mut self) -> Result<Node<Expr>, ParseError> {
        self.parse_pipe_expr()
    }

    fn parse_pipe_expr(&mut self) -> Result<Node<Expr>, ParseError> {
        let start = self.current().clone();
        let mut lhs = self.parse_assign_expr()?;
        while self.matches(&TokenKind::PipeGt) {
            self.advance();
            let rhs = self.parse_assign_expr()?;
            let span = self.span_from(&start);
            lhs = Node::new(
                Expr::Pipe {
                    lhs: Box::new(lhs),
                    rhs: Box::new(rhs),
                },
                span,
            );
        }
        Ok(lhs)
    }

    fn parse_assign_expr(&mut self) -> Result<Node<Expr>, ParseError> {
        let start = self.current().clone();
        let lhs = self.parse_or_expr()?;
        if self.matches(&TokenKind::Walrus) {
            if let Expr::Var(name) = &lhs.kind {
                let name = name.clone();
                self.advance();
                let value = self.parse_expr()?;
                let type_ann = None;
                return Ok(Node::new(
                    Expr::Walrus {
                        name,
                        value: Box::new(value),
                        type_ann,
                    },
                    self.span_from(&start),
                ));
            } else {
                let span = lhs.span;
                return Err(ParseError::InvalidExpression {
                    line: span.line,
                    col: span.col,
                    span,
                });
            }
        }
        Ok(lhs)
    }

    fn parse_or_expr(&mut self) -> Result<Node<Expr>, ParseError> {
        let start = self.current().clone();
        let mut lhs = self.parse_and_expr()?;
        while self.matches(&TokenKind::PipePipe) {
            self.advance();
            let rhs = self.parse_and_expr()?;
            lhs = Node::new(
                Expr::BinaryOp {
                    op: BinOp::Or,
                    lhs: Box::new(lhs),
                    rhs: Box::new(rhs),
                },
                self.span_from(&start),
            );
        }
        Ok(lhs)
    }

    fn parse_and_expr(&mut self) -> Result<Node<Expr>, ParseError> {
        let start = self.current().clone();
        let mut lhs = self.parse_coalesce_expr()?;
        while self.matches(&TokenKind::AmpAmp) {
            self.advance();
            let rhs = self.parse_coalesce_expr()?;
            lhs = Node::new(
                Expr::BinaryOp {
                    op: BinOp::And,
                    lhs: Box::new(lhs),
                    rhs: Box::new(rhs),
                },
                self.span_from(&start),
            );
        }
        Ok(lhs)
    }

    fn parse_coalesce_expr(&mut self) -> Result<Node<Expr>, ParseError> {
        let start = self.current().clone();
        let mut lhs = self.parse_comparison_expr()?;
        while self.matches(&TokenKind::QuestionQuestion) {
            self.advance();
            let rhs = self.parse_comparison_expr()?;
            lhs = Node::new(
                Expr::NullCoalesce {
                    lhs: Box::new(lhs),
                    rhs: Box::new(rhs),
                },
                self.span_from(&start),
            );
        }
        Ok(lhs)
    }

    fn parse_comparison_expr(&mut self) -> Result<Node<Expr>, ParseError> {
        let start = self.current().clone();
        let mut lhs = self.parse_addition_expr()?;
        let op = match self.peek() {
            TokenKind::EqEq => Some(BinOp::Eq),
            TokenKind::BangEq => Some(BinOp::Ne),
            TokenKind::Lt | TokenKind::LtGeneric => Some(BinOp::Lt),
            TokenKind::Gt | TokenKind::GtGeneric => Some(BinOp::Gt),
            TokenKind::LtEq => Some(BinOp::Le),
            TokenKind::GtEq => Some(BinOp::Ge),
            TokenKind::Is => Some(BinOp::Is),
            TokenKind::As => Some(BinOp::As),
            _ => None,
        };
        if let Some(op) = op {
            self.advance();
            let rhs = self.parse_addition_expr()?;
            lhs = Node::new(
                Expr::BinaryOp {
                    op,
                    lhs: Box::new(lhs),
                    rhs: Box::new(rhs),
                },
                self.span_from(&start),
            );
        }
        Ok(lhs)
    }

    fn parse_addition_expr(&mut self) -> Result<Node<Expr>, ParseError> {
        let start = self.current().clone();
        let mut lhs = self.parse_multiplication_expr()?;
        loop {
            let op = match self.peek() {
                TokenKind::Plus => Some(BinOp::Add),
                TokenKind::Minus => Some(BinOp::Sub),
                _ => None,
            };
            if let Some(op) = op {
                self.advance();
                let rhs = self.parse_multiplication_expr()?;
                lhs = Node::new(
                    Expr::BinaryOp {
                        op,
                        lhs: Box::new(lhs),
                        rhs: Box::new(rhs),
                    },
                    self.span_from(&start),
                );
            } else {
                break;
            }
        }
        Ok(lhs)
    }

    fn parse_multiplication_expr(&mut self) -> Result<Node<Expr>, ParseError> {
        let start = self.current().clone();
        let mut lhs = self.parse_unary_expr()?;
        loop {
            let op = match self.peek() {
                TokenKind::Star => Some(BinOp::Mul),
                TokenKind::Slash => Some(BinOp::Div),
                TokenKind::Percent => Some(BinOp::Mod),
                _ => None,
            };
            if let Some(op) = op {
                self.advance();
                let rhs = self.parse_unary_expr()?;
                lhs = Node::new(
                    Expr::BinaryOp {
                        op,
                        lhs: Box::new(lhs),
                        rhs: Box::new(rhs),
                    },
                    self.span_from(&start),
                );
            } else {
                break;
            }
        }
        Ok(lhs)
    }

    fn parse_unary_expr(&mut self) -> Result<Node<Expr>, ParseError> {
        let start = self.current().clone();
        let op = match self.peek() {
            TokenKind::Bang => Some(UnOp::Not),
            TokenKind::Minus => Some(UnOp::Neg),
            TokenKind::Amp => Some(UnOp::Ref),
            _ => None,
        };
        if let Some(op) = op {
            self.advance();
            let operand = self.parse_unary_expr()?;
            return Ok(Node::new(
                Expr::UnaryOp {
                    op,
                    operand: Box::new(operand),
                },
                self.span_from(&start),
            ));
        }
        self.parse_postfix_expr()
    }

    fn parse_postfix_expr(&mut self) -> Result<Node<Expr>, ParseError> {
        let start = self.current().clone();
        let mut expr = self.parse_primary_expr()?;
        loop {
            match self.peek() {
                TokenKind::Question => {
                    self.advance();
                    let span = self.span_from(&start);
                    expr = Node::new(
                        Expr::ErrorPropagate {
                            expr: Box::new(expr),
                        },
                        span,
                    );
                }
                TokenKind::Dot => {
                    self.advance();
                    let (field, _) = self.expect_identifier()?;
                    let span = self.span_from(&start);
                    expr = Node::new(
                        Expr::FieldAccess {
                            object: Box::new(expr),
                            field,
                        },
                        span,
                    );
                }
                TokenKind::LParen => {
                    self.advance();
                    let mut args = Vec::new();
                    while !self.matches(&TokenKind::RParen) && !self.matches(&TokenKind::Eof) {
                        args.push(self.parse_expr()?);
                        if self.matches(&TokenKind::Comma) {
                            self.advance();
                        } else {
                            break;
                        }
                    }
                    self.expect(&TokenKind::RParen)?;
                    let span = self.span_from(&start);
                    expr = Node::new(
                        Expr::Call {
                            callee: Box::new(expr),
                            args,
                        },
                        span,
                    );
                }
                TokenKind::LBracket => {
                    self.advance();
                    let index = self.parse_expr()?;
                    self.expect(&TokenKind::RBracket)?;
                    let span = self.span_from(&start);
                    expr = Node::new(
                        Expr::Index {
                            object: Box::new(expr),
                            index: Box::new(index),
                        },
                        span,
                    );
                }
                _ => break,
            }
        }
        Ok(expr)
    }

    fn parse_primary_expr(&mut self) -> Result<Node<Expr>, ParseError> {
        let start = self.current().clone();
        match self.peek().clone() {
            TokenKind::IntLiteral(v) => {
                self.advance();
                Ok(Node::new(
                    Expr::Literal(Literal::Int(v)),
                    self.span_from(&start),
                ))
            }
            TokenKind::FloatLiteral(ref s) => {
                let s = s.clone();
                self.advance();
                Ok(Node::new(
                    Expr::Literal(Literal::Float(s)),
                    self.span_from(&start),
                ))
            }
            TokenKind::StringLiteral(ref s) => {
                let s = s.clone();
                self.advance();
                Ok(Node::new(
                    Expr::Literal(Literal::String(s)),
                    self.span_from(&start),
                ))
            }
            TokenKind::BoolLiteral(b) => {
                self.advance();
                Ok(Node::new(
                    Expr::Literal(Literal::Bool(b)),
                    self.span_from(&start),
                ))
            }
            TokenKind::Null => {
                self.advance();
                Ok(Node::new(
                    Expr::Literal(Literal::Null),
                    self.span_from(&start),
                ))
            }
            TokenKind::Identifier(ref name) => {
                let name = name.clone();
                self.advance();
                if self.matches(&TokenKind::LBrace) {
                    let looks_like_struct = matches!(self.peek_at(1), TokenKind::Identifier(_))
                        && matches!(
                            self.peek_at(2),
                            TokenKind::Colon | TokenKind::Comma | TokenKind::RBrace
                        )
                        || matches!(self.peek_at(1), TokenKind::RBrace);
                    if looks_like_struct {
                        let fields = self.parse_struct_init_fields()?;
                        return Ok(Node::new(
                            Expr::StructInit { name, fields },
                            self.span_from(&start),
                        ));
                    }
                }
                Ok(Node::new(Expr::Var(name), self.span_from(&start)))
            }
            TokenKind::LParen => {
                self.advance();
                if self.matches(&TokenKind::RParen) {
                    self.advance();
                    if self.matches(&TokenKind::Arrow) {
                        self.advance();
                        let body = self.parse_expr()?;
                        return Ok(Node::new(
                            Expr::Lambda {
                                params: Vec::new(),
                                body: Box::new(body),
                            },
                            self.span_from(&start),
                        ));
                    }
                    return Ok(Node::new(
                        Expr::Literal(Literal::Null),
                        self.span_from(&start),
                    ));
                }
                let first = self.parse_expr()?;
                if self.matches(&TokenKind::Comma) {
                    self.advance();
                    let mut param_names = Vec::new();
                    let first_name = match &first.kind {
                        Expr::Var(n) => {
                            let p = Node::new(
                                Param {
                                    name: n.clone(),
                                    type_ann: None,
                                },
                                first.span,
                            );
                            param_names.push(p);
                            true
                        }
                        _ => false,
                    };
                    while !self.matches(&TokenKind::RParen) && !self.matches(&TokenKind::Eof) {
                        let pstart = self.current().clone();
                        let (name, _) = self.expect_identifier()?;
                        let type_ann = if self.matches(&TokenKind::Colon) {
                            self.advance();
                            Some(self.parse_type()?)
                        } else {
                            None
                        };
                        param_names.push(Node::new(Param { name, type_ann }, self.span_from(&pstart)));
                        if self.matches(&TokenKind::Comma) {
                            self.advance();
                        } else {
                            break;
                        }
                    }
                    self.expect(&TokenKind::RParen)?;
                    if self.matches(&TokenKind::Arrow) && first_name {
                        self.advance();
                        let body = self.parse_expr()?;
                        return Ok(Node::new(
                            Expr::Lambda {
                                params: param_names,
                                body: Box::new(body),
                            },
                            self.span_from(&start),
                        ));
                    }
                    return Ok(first);
                }
                self.expect(&TokenKind::RParen)?;
                if self.matches(&TokenKind::Arrow) {
                    let params = vec![Node::new(
                        Param {
                            name: match &first.kind {
                                Expr::Var(n) => n.clone(),
                                _ => "_".to_string(),
                            },
                            type_ann: None,
                        },
                        first.span,
                    )];
                    self.advance();
                    let body = self.parse_expr()?;
                    return Ok(Node::new(
                        Expr::Lambda {
                            params,
                            body: Box::new(body),
                        },
                        self.span_from(&start),
                    ));
                }
                Ok(first)
            }
            TokenKind::LBrace => self.parse_block_expr(),
            TokenKind::If => self.parse_if_expr(),
            TokenKind::Fix => self.parse_match_expr(),
            TokenKind::Spawn => {
                self.advance();
                let expr = self.parse_postfix_expr()?;
                Ok(Node::new(
                    Expr::Spawn {
                        expr: Box::new(expr),
                    },
                    self.span_from(&start),
                ))
            }
            TokenKind::Async => {
                self.advance();
                let expr = self.parse_postfix_expr()?;
                Ok(Node::new(
                    Expr::Async {
                        expr: Box::new(expr),
                    },
                    self.span_from(&start),
                ))
            }
            _ => {
                let span = self.current().span;
                Err(ParseError::InvalidExpression {
                    line: span.line,
                    col: span.col,
                    span,
                })
            }
        }
    }

    #[allow(dead_code)]
    fn parse_lambda_from_params(
        &mut self,
        mut params: Vec<Node<Param>>,
        start: &Token,
    ) -> Result<Node<Expr>, ParseError> {
        if self.matches(&TokenKind::Comma) {
            self.advance();
            while !self.matches(&TokenKind::RParen) && !self.matches(&TokenKind::Eof) {
                let pstart = self.current().clone();
                let (name, _) = self.expect_identifier()?;
                let type_ann = if self.matches(&TokenKind::Colon) {
                    self.advance();
                    Some(self.parse_type()?)
                } else {
                    None
                };
                params.push(Node::new(Param { name, type_ann }, self.span_from(&pstart)));
                if self.matches(&TokenKind::Comma) {
                    self.advance();
                } else {
                    break;
                }
            }
        }
        if self.matches(&TokenKind::Arrow) {
            self.advance();
        }
        self.expect(&TokenKind::RParen)?;
        self.expect(&TokenKind::Arrow)?;
        let body = self.parse_expr()?;
        Ok(Node::new(
            Expr::Lambda {
                params,
                body: Box::new(body),
            },
            self.span_from(start),
        ))
    }

    fn parse_struct_init_fields(&mut self) -> Result<Vec<(String, Node<Expr>)>, ParseError> {
        self.expect(&TokenKind::LBrace)?;
        let mut fields = Vec::new();
        while !self.matches(&TokenKind::RBrace) && !self.matches(&TokenKind::Eof) {
            let (name, _) = self.expect_identifier()?;
            let colon_present = if self.matches(&TokenKind::Colon) {
                self.advance();
                true
            } else {
                false
            };
            if colon_present {
                let value = self.parse_expr()?;
                fields.push((name, value));
            } else {
                let span = self.current().span;
                let value = Node::new(Expr::Var(name.clone()), span);
                fields.push((name, value));
            }
            if self.matches(&TokenKind::Comma) {
                self.advance();
            } else {
                break;
            }
        }
        self.expect(&TokenKind::RBrace)?;
        Ok(fields)
    }

    fn parse_block_expr(&mut self) -> Result<Node<Expr>, ParseError> {
        let start = self.current().clone();
        self.expect(&TokenKind::LBrace)?;
        let mut stmts = Vec::new();
        let mut expr = None;
        while !self.matches(&TokenKind::RBrace) && !self.matches(&TokenKind::Eof) {
            let parsed_stmt = self.parse_stmt();
            match parsed_stmt {
                Ok(s) => {
                    if let Stmt::ExprStmt(e) = &s.kind {
                        if self.matches(&TokenKind::RBrace) || self.matches(&TokenKind::Eof) {
                            expr = Some(Box::new((*e).clone()));
                            stmts.push(s);
                        } else {
                            stmts.push(s);
                        }
                    } else {
                        stmts.push(s);
                    }
                }
                Err(e) => {
                    self.errors.push(e);
                    self.synchronize();
                }
            }
        }
        self.expect(&TokenKind::RBrace)?;
        Ok(Node::new(
            Expr::Block { stmts, expr },
            self.span_from(&start),
        ))
    }

    fn parse_if_expr(&mut self) -> Result<Node<Expr>, ParseError> {
        let start = self.current().clone();
        self.expect(&TokenKind::If)?;
        let condition = self.parse_expr()?;
        let then_branch = self.parse_block_expr()?;
        let else_branch = if self.matches(&TokenKind::Else) {
            self.advance();
            if self.matches(&TokenKind::If) {
                Some(Box::new(self.parse_if_expr()?))
            } else {
                Some(Box::new(self.parse_block_expr()?))
            }
        } else {
            None
        };
        Ok(Node::new(
            Expr::If {
                condition: Box::new(condition),
                then_branch: Box::new(then_branch),
                else_branch,
            },
            self.span_from(&start),
        ))
    }

    fn parse_match_expr(&mut self) -> Result<Node<Expr>, ParseError> {
        let start = self.current().clone();
        self.expect(&TokenKind::Fix)?;
        let scrutinee = self.parse_expr()?;
        self.expect(&TokenKind::LBrace)?;
        let mut arms = Vec::new();
        while !self.matches(&TokenKind::RBrace) && !self.matches(&TokenKind::Eof) {
            let arm = self.parse_match_arm()?;
            arms.push(arm);
            if self.matches(&TokenKind::Comma) {
                self.advance();
            }
        }
        self.expect(&TokenKind::RBrace)?;
        Ok(Node::new(
            Expr::Match {
                scrutinee: Box::new(scrutinee),
                arms,
            },
            self.span_from(&start),
        ))
    }

    fn parse_match_arm(&mut self) -> Result<Node<MatchArm>, ParseError> {
        let start = self.current().clone();
        let pattern = self.parse_pattern()?;
        let guard = if self.matches(&TokenKind::If) {
            self.advance();
            Some(self.parse_expr()?)
        } else {
            None
        };
        self.expect(&TokenKind::FatArrow)?;
        let body = self.parse_expr()?;
        Ok(Node::new(
            MatchArm {
                pattern,
                guard,
                body,
            },
            self.span_from(&start),
        ))
    }

    fn parse_pattern(&mut self) -> Result<Node<Pattern>, ParseError> {
        let start = self.current().clone();
        let pat = self.parse_pattern_primary()?;
        if self.matches(&TokenKind::Pipe) {
            self.advance();
            let mut alternatives = vec![pat];
            alternatives.push(self.parse_pattern_primary()?);
            while self.matches(&TokenKind::Pipe) {
                self.advance();
                alternatives.push(self.parse_pattern_primary()?);
            }
            return Ok(Node::new(
                Pattern::Or(alternatives),
                self.span_from(&start),
            ));
        }
        Ok(pat)
    }

    fn parse_pattern_primary(&mut self) -> Result<Node<Pattern>, ParseError> {
        let start = self.current().clone();
        match self.peek().clone() {
            TokenKind::Underscore => {
                self.advance();
                Ok(Node::new(Pattern::Wildcard, self.span_from(&start)))
            }
            TokenKind::IntLiteral(v) => {
                self.advance();
                Ok(Node::new(
                    Pattern::Literal(Literal::Int(v)),
                    self.span_from(&start),
                ))
            }
            TokenKind::StringLiteral(ref s) => {
                let s = s.clone();
                self.advance();
                Ok(Node::new(
                    Pattern::Literal(Literal::String(s)),
                    self.span_from(&start),
                ))
            }
            TokenKind::BoolLiteral(b) => {
                self.advance();
                Ok(Node::new(
                    Pattern::Literal(Literal::Bool(b)),
                    self.span_from(&start),
                ))
            }
            TokenKind::Null => {
                self.advance();
                Ok(Node::new(
                    Pattern::Literal(Literal::Null),
                    self.span_from(&start),
                ))
            }
            TokenKind::Identifier(ref name) => {
                let name = name.clone();
                self.advance();
                if self.matches(&TokenKind::LParen) {
                    self.advance();
                    let mut field_pats = Vec::new();
                    while !self.matches(&TokenKind::RParen) && !self.matches(&TokenKind::Eof) {
                        let (fname, _) = self.expect_identifier()?;
                        self.expect(&TokenKind::Colon)?;
                        let fpat = self.parse_pattern()?;
                        field_pats.push((fname, fpat));
                        if self.matches(&TokenKind::Comma) {
                            self.advance();
                        } else {
                            break;
                        }
                    }
                    self.expect(&TokenKind::RParen)?;
                    return Ok(Node::new(
                        Pattern::Constructor {
                            name,
                            fields: field_pats,
                        },
                        self.span_from(&start),
                    ));
                }
                if self.matches(&TokenKind::LBrace) {
                    self.advance();
                    let mut field_pats = Vec::new();
                    while !self.matches(&TokenKind::RBrace) && !self.matches(&TokenKind::Eof) {
                        let (fname, _) = self.expect_identifier()?;
                        let fpat = if self.matches(&TokenKind::Colon) {
                            self.advance();
                            self.parse_pattern()?
                        } else {
                            Node::new(Pattern::Var(fname.clone()), self.span_from(&start))
                        };
                        field_pats.push((fname, fpat));
                        if self.matches(&TokenKind::Comma) {
                            self.advance();
                        } else {
                            break;
                        }
                    }
                    self.expect(&TokenKind::RBrace)?;
                    return Ok(Node::new(
                        Pattern::Constructor {
                            name,
                            fields: field_pats,
                        },
                        self.span_from(&start),
                    ));
                }
                if name == ".." {
                    Ok(Node::new(Pattern::Rest(None), self.span_from(&start)))
                } else {
                    Ok(Node::new(Pattern::Var(name), self.span_from(&start)))
                }
            }
            TokenKind::LParen => {
                self.advance();
                let mut elements = Vec::new();
                while !self.matches(&TokenKind::RParen) && !self.matches(&TokenKind::Eof) {
                    elements.push(self.parse_pattern()?);
                    if self.matches(&TokenKind::Comma) {
                        self.advance();
                    } else {
                        break;
                    }
                }
                self.expect(&TokenKind::RParen)?;
                Ok(Node::new(Pattern::Tuple(elements), self.span_from(&start)))
            }
            _ => {
                let span = self.current().span;
                Err(ParseError::UnexpectedToken {
                    found: format!("{}", self.peek()),
                    expected: "pattern".to_string(),
                    line: span.line,
                    col: span.col,
                    span,
                })
            }
        }
    }

    fn parse_stmt(&mut self) -> Result<Node<Stmt>, ParseError> {
        let start = self.current().clone();
        match self.peek() {
            TokenKind::Ret => {
                self.advance();
                let value = if !self.matches(&TokenKind::Semicolon)
                    && !self.matches(&TokenKind::RBrace)
                    && !self.matches(&TokenKind::Eof)
                {
                    Some(self.parse_expr()?)
                } else {
                    None
                };
                if self.matches(&TokenKind::Semicolon) {
                    self.advance();
                }
                Ok(Node::new(Stmt::Return(value), self.span_from(&start)))
            }
            TokenKind::Defer => {
                self.advance();
                let expr = self.parse_expr()?;
                if self.matches(&TokenKind::Semicolon) {
                    self.advance();
                }
                Ok(Node::new(Stmt::Defer(expr), self.span_from(&start)))
            }
            TokenKind::Mut => {
                self.advance();
                let (name, _) = self.expect_identifier()?;
                let type_ann = if self.matches(&TokenKind::Colon) {
                    self.advance();
                    Some(self.parse_type()?)
                } else {
                    None
                };
                self.expect(&TokenKind::Assign)?;
                let value = self.parse_expr()?;
                if self.matches(&TokenKind::Semicolon) {
                    self.advance();
                }
                Ok(Node::new(
                    Stmt::VarDecl {
                        name,
                        type_ann,
                        value,
                    },
                    self.span_from(&start),
                ))
            }
            TokenKind::Loop => {
                self.advance();
                let condition = if !self.matches(&TokenKind::LBrace) {
                    Some(self.parse_expr()?)
                } else {
                    None
                };
                self.expect(&TokenKind::LBrace)?;
                let mut body = Vec::new();
                while !self.matches(&TokenKind::RBrace) && !self.matches(&TokenKind::Eof) {
                    match self.parse_stmt() {
                        Ok(s) => body.push(s),
                        Err(e) => {
                            self.errors.push(e);
                            self.synchronize();
                        }
                    }
                }
                self.expect(&TokenKind::RBrace)?;
                let cond = condition.unwrap_or_else(|| {
                    Node::new(Expr::Literal(Literal::Bool(true)), Span::dummy())
                });
                Ok(Node::new(
                    Stmt::While { condition: cond, body },
                    self.span_from(&start),
                ))
            }
            _ => {
                let expr = self.parse_expr()?;
                if self.matches(&TokenKind::Assign) {
                    self.advance();
                    let value = self.parse_expr()?;
                    if self.matches(&TokenKind::Semicolon) {
                        self.advance();
                    }
                    return Ok(Node::new(
                        Stmt::Assign {
                            target: expr,
                            value,
                        },
                        self.span_from(&start),
                    ));
                }
                if self.matches(&TokenKind::Semicolon) {
                    self.advance();
                }
                Ok(Node::new(Stmt::ExprStmt(expr), self.span_from(&start)))
            }
        }
    }
}

pub fn parse(tokens: Vec<Token>) -> (Vec<Node<Item>>, Vec<ParseError>) {
    let mut parser = Parser::new(tokens);
    parser.parse_program()
}

pub fn parse_source(source: &str) -> Result<(Vec<Node<Item>>, Vec<crate::lexer::LexError>, Vec<ParseError>), ()> {
    let token_results = crate::lexer::Lexer::tokenize(source);
    let mut tokens = Vec::new();
    let mut lex_errors = Vec::new();
    for result in token_results {
        match result {
            Ok(t) => tokens.push(t),
            Err(e) => {
                lex_errors.push(e);
            }
        }
    }
    let (items, parse_errors) = parse(tokens);
    Ok((items, lex_errors, parse_errors))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn parse_expr_str(source: &str) -> Result<Node<Expr>, ParseError> {
        let tokens = crate::lexer::Lexer::tokenize(source)
            .into_iter()
            .filter_map(|r| r.ok())
            .collect();
        let mut parser = Parser::new(tokens);
        parser.parse_expr()
    }

    fn parse_program_str(source: &str) -> (Vec<Node<Item>>, Vec<ParseError>) {
        let tokens = crate::lexer::Lexer::tokenize(source)
            .into_iter()
            .filter_map(|r| r.ok())
            .collect();
        let mut parser = Parser::new(tokens);
        parser.parse_program()
    }

    #[test]
    fn test_parse_int_literal() {
        let expr = parse_expr_str("42").unwrap();
        assert!(matches!(expr.kind, Expr::Literal(Literal::Int(42))));
    }

    #[test]
    fn test_parse_string_literal() {
        let expr = parse_expr_str(r#""hello""#).unwrap();
        assert!(matches!(expr.kind, Expr::Literal(Literal::String(ref s)) if s == "hello"));
    }

    #[test]
    fn test_parse_bool_literal() {
        let expr = parse_expr_str("true").unwrap();
        assert!(matches!(expr.kind, Expr::Literal(Literal::Bool(true))));
        let expr = parse_expr_str("false").unwrap();
        assert!(matches!(expr.kind, Expr::Literal(Literal::Bool(false))));
    }

    #[test]
    fn test_parse_null() {
        let expr = parse_expr_str("null").unwrap();
        assert!(matches!(expr.kind, Expr::Literal(Literal::Null)));
    }

    #[test]
    fn test_parse_binary_add() {
        let expr = parse_expr_str("1 + 2").unwrap();
        match &expr.kind {
            Expr::BinaryOp { op, .. } => assert_eq!(*op, BinOp::Add),
            _ => panic!("expected binary op"),
        }
    }

    #[test]
    fn test_parse_binary_mul_precedence() {
        let expr = parse_expr_str("1 + 2 * 3").unwrap();
        match &expr.kind {
            Expr::BinaryOp {
                op: BinOp::Add,
                rhs,
                ..
            } => {
                assert!(matches!(
                    rhs.kind,
                    Expr::BinaryOp {
                        op: BinOp::Mul,
                        ..
                    }
                ));
            }
            _ => panic!("expected addition at top level"),
        }
    }

    #[test]
    fn test_parse_unary_neg() {
        let expr = parse_expr_str("-x").unwrap();
        assert!(matches!(expr.kind, Expr::UnaryOp { op: UnOp::Neg, .. }));
    }

    #[test]
    fn test_parse_unary_not() {
        let expr = parse_expr_str("!x").unwrap();
        assert!(matches!(expr.kind, Expr::UnaryOp { op: UnOp::Not, .. }));
    }

    #[test]
    fn test_parse_call() {
        let expr = parse_expr_str("foo(1, 2)").unwrap();
        match &expr.kind {
            Expr::Call { args, .. } => assert_eq!(args.len(), 2),
            _ => panic!("expected call"),
        }
    }

    #[test]
    fn test_parse_field_access() {
        let expr = parse_expr_str("foo.bar").unwrap();
        assert!(matches!(expr.kind, Expr::FieldAccess { ref field, .. } if field == "bar"));
    }

    #[test]
    fn test_parse_index() {
        let expr = parse_expr_str("arr[0]").unwrap();
        assert!(matches!(expr.kind, Expr::Index { .. }));
    }

    #[test]
    fn test_parse_pipe() {
        let expr = parse_expr_str("x |> f |> g").unwrap();
        match &expr.kind {
            Expr::Pipe { lhs, rhs } => {
                assert!(matches!(lhs.kind, Expr::Pipe { .. }));
                assert!(matches!(rhs.kind, Expr::Var(ref s) if s == "g"));
            }
            _ => panic!("expected pipe"),
        }
    }

    #[test]
    fn test_parse_error_propagate() {
        let expr = parse_expr_str("foo?").unwrap();
        assert!(matches!(expr.kind, Expr::ErrorPropagate { .. }));
    }

    #[test]
    fn test_parse_null_coalesce() {
        let expr = parse_expr_str("x ?? y").unwrap();
        assert!(matches!(expr.kind, Expr::NullCoalesce { .. }));
    }

    #[test]
    fn test_parse_walrus() {
        let expr = parse_expr_str("x := 5").unwrap();
        assert!(matches!(
            expr.kind,
            Expr::Walrus {
                ref name,
                ..
            } if name == "x"
        ));
    }

    #[test]
    fn test_parse_if_expr() {
        let expr = parse_expr_str("if x { 1 } else { 2 }").unwrap();
        match &expr.kind {
            Expr::If {
                else_branch: Some(..),
                ..
            } => {}
            _ => panic!("expected if with else"),
        }
    }

    #[test]
    fn test_parse_if_without_else() {
        let expr = parse_expr_str("if x { 1 }").unwrap();
        match &expr.kind {
            Expr::If {
                else_branch: None, ..
            } => {}
            _ => panic!("expected if without else"),
        }
    }

    #[test]
    fn test_parse_block_expr() {
        let expr = parse_expr_str("{ 1 }").unwrap();
        assert!(matches!(expr.kind, Expr::Block { .. }));
    }

    #[test]
    fn test_parse_match_expr() {
        let source = "fix x { 1 => a, 2 => b }";
        let expr = parse_expr_str(source).unwrap();
        match &expr.kind {
            Expr::Match { arms, .. } => assert_eq!(arms.len(), 2),
            _ => panic!("expected match"),
        }
    }

    #[test]
    fn test_parse_lambda() {
        let expr = parse_expr_str("(a) -> a + 1").unwrap();
        match &expr.kind {
            Expr::Lambda { params, .. } => assert_eq!(params.len(), 1),
            _ => panic!("expected lambda"),
        }
    }

    #[test]
    fn test_parse_lambda_multi_param() {
        let expr = parse_expr_str("(a, b) -> a + b").unwrap();
        match &expr.kind {
            Expr::Lambda { params, .. } => assert_eq!(params.len(), 2),
            _ => panic!("expected lambda"),
        }
    }

    #[test]
    fn test_parse_spawn() {
        let expr = parse_expr_str("spawn { 1 }").unwrap();
        assert!(matches!(expr.kind, Expr::Spawn { .. }));
    }

    #[test]
    fn test_parse_async() {
        let expr = parse_expr_str("async { 1 }").unwrap();
        assert!(matches!(expr.kind, Expr::Async { .. }));
    }

    #[test]
    fn test_parse_fn_decl() {
        let source = "fn add(a: i32, b: i32) -> i32 { ret a + b }";
        let (items, errors) = parse_program_str(source);
        assert!(errors.is_empty(), "parse errors: {:?}", errors);
        assert_eq!(items.len(), 1);
        match &items[0].kind {
            Item::FnDecl(f) => {
                assert_eq!(f.name, "add");
                assert_eq!(f.params.len(), 2);
            }
            _ => panic!("expected fn decl"),
        }
    }

    #[test]
    fn test_parse_fn_no_return() {
        let source = "fn foo() { 1 }";
        let (items, errors) = parse_program_str(source);
        assert!(errors.is_empty(), "parse errors: {:?}", errors);
        assert_eq!(items.len(), 1);
        match &items[0].kind {
            Item::FnDecl(f) => {
                assert_eq!(f.name, "foo");
                assert!(f.return_type.is_none());
            }
            _ => panic!("expected fn decl"),
        }
    }

    #[test]
    fn test_parse_use_decl() {
        let source = "use std::collections";
        let (items, errors) = parse_program_str(source);
        assert!(errors.is_empty(), "parse errors: {:?}", errors);
        match &items[0].kind {
            Item::UseDecl(u) => {
                assert_eq!(u.path, vec!["std", "collections"]);
            }
            _ => panic!("expected use decl"),
        }
    }

    #[test]
    fn test_parse_use_with_alias() {
        let source = "use std::collections as c";
        let (items, errors) = parse_program_str(source);
        assert!(errors.is_empty(), "parse errors: {:?}", errors);
        match &items[0].kind {
            Item::UseDecl(u) => {
                assert_eq!(u.alias, Some("c".to_string()));
            }
            _ => panic!("expected use decl"),
        }
    }

    #[test]
    fn test_parse_type_decl_struct() {
        let source = "type Point = { x: f64, y: f64 }";
        let (items, errors) = parse_program_str(source);
        assert!(errors.is_empty(), "parse errors: {:?}", errors);
        match &items[0].kind {
            Item::TypeDecl(t) => {
                assert_eq!(t.name, "Point");
                match &t.body {
                    TypeBody::Struct(fields) => assert_eq!(fields.len(), 2),
                    _ => panic!("expected struct"),
                }
            }
            _ => panic!("expected type decl"),
        }
    }

    #[test]
    fn test_parse_type_decl_alias() {
        let source = "type Age = i64";
        let (items, errors) = parse_program_str(source);
        assert!(errors.is_empty(), "parse errors: {:?}", errors);
        match &items[0].kind {
            Item::TypeDecl(t) => {
                assert_eq!(t.name, "Age");
                match &t.body {
                    TypeBody::Alias(a) => {
                        assert!(matches!(a.kind, Type::Named(ref s) if s == "i64"));
                    }
                    _ => panic!("expected alias"),
                }
            }
            _ => panic!("expected type decl"),
        }
    }

    #[test]
    fn test_parse_const_decl() {
        let source = "const MAX: i32 = 100";
        let (items, errors) = parse_program_str(source);
        assert!(errors.is_empty(), "parse errors: {:?}", errors);
        match &items[0].kind {
            Item::ConstDecl(c) => {
                assert_eq!(c.name, "MAX");
            }
            _ => panic!("expected const decl"),
        }
    }

    #[test]
    fn test_parse_actor_decl() {
        let source = r#"
            act Counter {
                state count: i32 = 0
                event Increment(by: i32)
                on Increment { ret 0 }
                fn get() -> i32 { ret 0 }
            }
        "#;
        let (items, errors) = parse_program_str(source);
        assert!(errors.is_empty(), "parse errors: {:?}", errors);
        match &items[0].kind {
            Item::ActorDecl(a) => {
                assert_eq!(a.name, "Counter");
                assert_eq!(a.members.len(), 4);
            }
            _ => panic!("expected actor decl"),
        }
    }

    #[test]
    fn test_parse_pub_fn() {
        let source = "pub fn hello() { 1 }";
        let (items, errors) = parse_program_str(source);
        assert!(errors.is_empty(), "parse errors: {:?}", errors);
        match &items[0].kind {
            Item::FnDecl(f) => {
                assert_eq!(f.visibility, Visibility::Public);
            }
            _ => panic!("expected fn decl"),
        }
    }

    #[test]
    fn test_parse_var_decl() {
        let source = "fn test() { mut x = 5 }";
        let (items, errors) = parse_program_str(source);
        assert!(errors.is_empty(), "parse errors: {:?}", errors);
        match &items[0].kind {
            Item::FnDecl(f) => match &f.body.kind {
                Expr::Block { stmts, .. } => {
                    assert_eq!(stmts.len(), 1);
                    assert!(matches!(stmts[0].kind, Stmt::VarDecl { .. }));
                }
                _ => panic!("expected block"),
            },
            _ => panic!("expected fn decl"),
        }
    }

    #[test]
    fn test_parse_assign() {
        let source = "fn test() { x = 5 }";
        let (items, errors) = parse_program_str(source);
        assert!(errors.is_empty(), "parse errors: {:?}", errors);
        match &items[0].kind {
            Item::FnDecl(f) => match &f.body.kind {
                Expr::Block { stmts, .. } => {
                    assert!(matches!(stmts[0].kind, Stmt::Assign { .. }));
                }
                _ => panic!("expected block"),
            },
            _ => panic!("expected fn decl"),
        }
    }

    #[test]
    fn test_parse_return() {
        let source = "fn test() { ret 42 }";
        let (items, errors) = parse_program_str(source);
        assert!(errors.is_empty(), "parse errors: {:?}", errors);
        match &items[0].kind {
            Item::FnDecl(f) => match &f.body.kind {
                Expr::Block { stmts, .. } => {
                    assert!(matches!(
                        stmts[0].kind,
                        Stmt::Return(Some(_))
                    ));
                }
                _ => panic!("expected block"),
            },
            _ => panic!("expected fn decl"),
        }
    }

    #[test]
    fn test_parse_defer() {
        let source = "fn test() { defer cleanup() }";
        let (items, errors) = parse_program_str(source);
        assert!(errors.is_empty(), "parse errors: {:?}", errors);
        match &items[0].kind {
            Item::FnDecl(f) => match &f.body.kind {
                Expr::Block { stmts, .. } => {
                    assert!(matches!(stmts[0].kind, Stmt::Defer(_)));
                }
                _ => panic!("expected block"),
            },
            _ => panic!("expected fn decl"),
        }
    }

    #[test]
    fn test_parse_loop() {
        let source = "fn test() { loop { 1 } }";
        let (items, errors) = parse_program_str(source);
        assert!(errors.is_empty(), "parse errors: {:?}", errors);
        match &items[0].kind {
            Item::FnDecl(f) => match &f.body.kind {
                Expr::Block { stmts, .. } => {
                    assert!(matches!(stmts[0].kind, Stmt::While { .. }));
                }
                _ => panic!("expected block"),
            },
            _ => panic!("expected fn decl"),
        }
    }

    #[test]
    fn test_parse_complex_expr() {
        let source = "fn test() { a + b * c - d / e }";
        let (items, errors) = parse_program_str(source);
        assert!(errors.is_empty(), "parse errors: {:?}", errors);
        assert_eq!(items.len(), 1);
    }

    #[test]
    fn test_parse_generic_type() {
        let source = "type R = Result<i64, str>";
        let (items, errors) = parse_program_str(source);
        assert!(errors.is_empty(), "parse errors: {:?}", errors);
        match &items[0].kind {
            Item::TypeDecl(t) => match &t.body {
                TypeBody::Alias(ty) => match &ty.kind {
                    Type::Generic { name, args } => {
                        assert_eq!(name, "Result");
                        assert_eq!(args.len(), 2);
                    }
                    _ => panic!("expected generic type"),
                },
                _ => panic!("expected alias"),
            },
            _ => panic!("expected type decl"),
        }
    }

    #[test]
    fn test_error_recovery() {
        let source = "fn () { } fn foo() { 1 }";
        let (items, errors) = parse_program_str(source);
        assert!(!errors.is_empty());
        let fn_items: Vec<_> = items
            .iter()
            .filter(|i| matches!(i.kind, Item::FnDecl(_)))
            .collect();
        assert!(fn_items.len() >= 1, "should recover and parse 'fn foo'");
    }
}
