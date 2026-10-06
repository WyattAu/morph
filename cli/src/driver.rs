use std::path::Path;

use morph_compiler::ast::{Item, Node};
use morph_compiler::codegen::{CodeGen, MorphIRModule};
use morph_compiler::diagnostic::Diagnostic;
use morph_compiler::lexer::token::{Span, Token};
use morph_compiler::lexer::{LexError, Lexer};
use morph_compiler::parser::{self, ParseError};
use morph_compiler::typeck::{TypeCheckResult, TypeChecker};

/// Which surface syntax the compiler should accept.
#[derive(Debug, Clone, Default)]
pub enum Dialect {
    /// The minimal core language.
    Min,
    /// The human-friendly surface syntax; the default.
    #[default]
    Hum,
}

/// Which compiler artefact the CLI writes out.
#[derive(Debug, Clone, Default)]
pub enum EmitTarget {
    /// The lowered Morph IR; the default.
    #[default]
    MorphIR,
    /// The parsed abstract syntax tree.
    Ast,
    /// The inferred types and effects.
    Types,
    /// Execute the program.
    Run,
}

/// The options a [`Driver`] is configured with.
#[derive(Debug, Clone)]
pub struct Config {
    /// Which surface syntax to accept.
    pub dialect: Dialect,
    /// Whether to emit verbose debug output.
    pub debug: bool,
    /// Which artefact to produce.
    pub emit: EmitTarget,
}

impl Default for Config {
    /// Returns the default configuration: the [`Dialect::Hum`] surface syntax,
    /// debug output off, and [`EmitTarget::MorphIR`] output.
    fn default() -> Self {
        Self {
            dialect: Dialect::Hum,
            debug: false,
            emit: EmitTarget::MorphIR,
        }
    }
}

/// Everything a successful compilation produced.
///
/// The `lex_errors` and `parse_errors` fields are always empty when this value
/// is returned, since the driver reports them as errors instead; they are
/// present so callers can inspect them directly.
pub struct CompilationResult {
    /// The parsed top-level items.
    pub items: Vec<Node<Item>>,
    /// Inferred types and effects.
    pub type_check: TypeCheckResult,
    /// The lowered Morph IR.
    pub module: MorphIRModule,
    /// Lexical errors, empty on success.
    pub lex_errors: Vec<LexError>,
    /// Parse errors, empty on success.
    pub parse_errors: Vec<ParseError>,
}

/// Drives the compiler pipeline over one source file.
///
/// The driver owns the source text and exposes each stage — [`Driver::lex`],
/// [`Driver::parse`], [`Driver::type_check`], [`Driver::compile`] — separately
/// so the CLI can stop early and report the first failing stage.
pub struct Driver {
    source: String,
    filename: String,
    config: Config,
}

impl Driver {
    /// Creates a driver over `source`, displayed in diagnostics as `filename`.
    pub fn new(source: String, filename: String, config: Config) -> Self {
        Self {
            source,
            filename,
            config,
        }
    }

    /// Reads `path` and creates a driver for its contents.
    ///
    /// # Errors
    ///
    /// Returns the underlying I/O error if the file cannot be read.
    pub fn from_file(path: &Path, config: Config) -> std::io::Result<Self> {
        let source = std::fs::read_to_string(path)?;
        let filename = path
            .file_name()
            .map(|f| f.to_string_lossy().to_string())
            .unwrap_or_else(|| "unknown".to_string());
        Ok(Self::new(source, filename, config))
    }

    /// Borrows the source text being compiled.
    pub fn source(&self) -> &str {
        &self.source
    }

    /// Returns the name shown for this source in diagnostics.
    pub fn filename(&self) -> &str {
        &self.filename
    }

    /// Borrows the active configuration.
    pub fn config(&self) -> &Config {
        &self.config
    }

    /// Scans the source into tokens.
    ///
    /// # Errors
    ///
    /// Returns every [`LexError`] found; lexical errors are reported as a batch
    /// rather than stopping at the first.
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

    /// Lexes and parses the source into top-level items.
    ///
    /// # Errors
    ///
    /// Returns the [`ParseError`]s found. If lexing fails first, each lexical
    /// error is wrapped as an unexpected-token parse error so the caller sees a
    /// single error type.
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

    /// Runs the full front end and returns the inferred types and effects.
    ///
    /// Lexical and parse failures are converted to diagnostics so the caller
    /// always gets [`Diagnostic`]s back.
    ///
    /// # Errors
    ///
    /// Returns diagnostics for lexical, parse, or type errors, stopping at the
    /// first failing stage.
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

    /// Runs the full pipeline through to Morph IR.
    ///
    /// Stops at the first failing stage, converting that stage's errors to
    /// diagnostics with the codes `L001` (lex), `P001` (parse), and `CG001`
    /// (code generation).
    ///
    /// # Errors
    ///
    /// Returns diagnostics for whichever stage failed.
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
