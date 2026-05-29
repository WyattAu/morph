use std::path::Path;

use morph_compiler::ast::{Item, Node};
use morph_compiler::codegen::{CodeGen, MorphIRModule};
use morph_compiler::diagnostic::Diagnostic;
use morph_compiler::lexer::token::{Span, Token};
use morph_compiler::lexer::{LexError, Lexer};
use morph_compiler::parser::{self, ParseError};
use morph_compiler::typeck::{TypeCheckResult, TypeChecker};

#[derive(Debug, Clone, Default)]
pub enum Dialect {
    Min,
    #[default]
    Hum,
}

#[derive(Debug, Clone, Default)]
pub enum EmitTarget {
    #[default]
    MorphIR,
    Ast,
    Types,
    Run,
}

#[derive(Debug, Clone)]
pub struct Config {
    pub dialect: Dialect,
    pub debug: bool,
    pub emit: EmitTarget,
}

impl Default for Config {
    fn default() -> Self {
        Self {
            dialect: Dialect::Hum,
            debug: false,
            emit: EmitTarget::MorphIR,
        }
    }
}

pub struct CompilationResult {
    pub items: Vec<Node<Item>>,
    pub type_check: TypeCheckResult,
    pub module: MorphIRModule,
    pub lex_errors: Vec<LexError>,
    pub parse_errors: Vec<ParseError>,
}

pub struct Driver {
    source: String,
    filename: String,
    config: Config,
}

impl Driver {
    pub fn new(source: String, filename: String, config: Config) -> Self {
        Self {
            source,
            filename,
            config,
        }
    }

    pub fn from_file(path: &Path, config: Config) -> std::io::Result<Self> {
        let source = std::fs::read_to_string(path)?;
        let filename = path
            .file_name()
            .map(|f| f.to_string_lossy().to_string())
            .unwrap_or_else(|| "unknown".to_string());
        Ok(Self::new(source, filename, config))
    }

    pub fn source(&self) -> &str {
        &self.source
    }

    pub fn filename(&self) -> &str {
        &self.filename
    }

    pub fn config(&self) -> &Config {
        &self.config
    }

    pub fn lex(&self) -> Result<Vec<Token>, Vec<LexError>> {
        let results = Lexer::tokenize(&self.source);
        let mut tokens = Vec::new();
        let mut errors = Vec::new();
        for result in results {
            match result {
                Ok(t) => tokens.push(t),
                Err(e) => errors.push(e),
            }
        }
        if errors.is_empty() {
            Ok(tokens)
        } else {
            Err(errors)
        }
    }

    pub fn parse(&self) -> Result<Vec<Node<Item>>, Vec<ParseError>> {
        let tokens = match self.lex() {
            Ok(t) => t,
            Err(lex_errors) => {
                return Err(lex_errors
                    .into_iter()
                    .map(|e| ParseError::UnexpectedToken {
                        found: e.to_string(),
                        expected: "valid token".to_string(),
                        line: 0,
                        col: 0,
                        span: Span::dummy(),
                    })
                    .collect());
            }
        };
        let (items, errors) = parser::parse(tokens);
        if errors.is_empty() {
            Ok(items)
        } else {
            Err(errors)
        }
    }

    pub fn type_check(&self) -> Result<TypeCheckResult, Vec<Diagnostic>> {
        let tokens = self.lex().map_err(|errors| {
            errors
                .into_iter()
                .map(|e| Diagnostic::error("L001", e.to_string(), Span::dummy()))
                .collect::<Vec<_>>()
        })?;

        let (items, parse_errors) = parser::parse(tokens);

        if !parse_errors.is_empty() {
            return Err(parse_errors
                .into_iter()
                .map(|e| Diagnostic::error("P001", e.to_string(), Span::dummy()))
                .collect());
        }

        TypeChecker::check_program(&items)
    }

    pub fn compile(&self) -> Result<CompilationResult, Vec<Diagnostic>> {
        let lex_results = Lexer::tokenize(&self.source);
        let mut tokens = Vec::new();
        let mut lex_errors = Vec::new();

        for result in lex_results {
            match result {
                Ok(t) => tokens.push(t),
                Err(e) => lex_errors.push(e),
            }
        }

        if !lex_errors.is_empty() {
            return Err(lex_errors
                .into_iter()
                .map(|e| Diagnostic::error("L001", e.to_string(), Span::dummy()))
                .collect());
        }

        let (items, parse_errors) = parser::parse(tokens);

        if !parse_errors.is_empty() {
            return Err(parse_errors
                .into_iter()
                .map(|e| Diagnostic::error("P001", e.to_string(), Span::dummy()))
                .collect());
        }

        let type_check = TypeChecker::check_program(&items)?;

        let module = CodeGen::compile_with_effects(
            &items,
            type_check.type_map.clone(),
            type_check.effect_map.clone(),
        )
        .map_err(|codegen_errors| {
            codegen_errors
                .into_iter()
                .map(|e| Diagnostic::error("CG001", e.to_string(), Span::dummy()))
                .collect::<Vec<_>>()
        })?;

        Ok(CompilationResult {
            items,
            type_check,
            module,
            lex_errors,
            parse_errors,
        })
    }
}
