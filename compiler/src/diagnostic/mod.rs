//! Diagnostics and human-readable error rendering.

/// Rendering of [`Diagnostic`]s in a rustc-style format.
pub mod emitter;

use crate::lexer::token::Span;

/// How serious a [`Diagnostic`] is.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DiagnosticLevel {
    /// A problem that prevents the program from compiling.
    Error,
    /// A suspicious but non-fatal observation.
    Warning,
    /// Supplementary information attached to another diagnostic.
    Note,
    /// A concrete suggested fix.
    Help,
}

impl std::fmt::Display for DiagnosticLevel {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            DiagnosticLevel::Error => write!(f, "error"),
            DiagnosticLevel::Warning => write!(f, "warning"),
            DiagnosticLevel::Note => write!(f, "note"),
            DiagnosticLevel::Help => write!(f, "help"),
        }
    }
}

/// A single compiler message, with the source location it refers to.
#[derive(Debug, Clone)]
pub struct Diagnostic {
    /// How serious the diagnostic is.
    pub level: DiagnosticLevel,
    /// A stable machine-readable code such as `ERR_TYPE_001`.
    pub code: String,
    /// The human-readable message body.
    pub message: String,
    /// Where in the source the problem is.
    pub span: Span,
    /// Suggested fixes, rendered as `help:` lines.
    pub suggestions: Vec<String>,
}

impl Diagnostic {
    /// Creates an [`DiagnosticLevel::Error`] diagnostic.
    pub fn error(code: impl Into<String>, message: impl Into<String>, span: Span) -> Self {
        Self {
            level: DiagnosticLevel::Error,
            code: code.into(),
            message: message.into(),
            span,
            suggestions: Vec::new(),
        }
    }

    /// Creates a [`DiagnosticLevel::Warning`] diagnostic.
    pub fn warning(code: impl Into<String>, message: impl Into<String>, span: Span) -> Self {
        Self {
            level: DiagnosticLevel::Warning,
            code: code.into(),
            message: message.into(),
            span,
            suggestions: Vec::new(),
        }
    }

    /// Creates a [`DiagnosticLevel::Note`] diagnostic.
    pub fn note(code: impl Into<String>, message: impl Into<String>, span: Span) -> Self {
        Self {
            level: DiagnosticLevel::Note,
            code: code.into(),
            message: message.into(),
            span,
            suggestions: Vec::new(),
        }
    }

    /// Appends a suggested fix and returns the diagnostic for chaining.
    pub fn with_suggestion(mut self, suggestion: impl Into<String>) -> Self {
        self.suggestions.push(suggestion.into());
        self
    }
}
