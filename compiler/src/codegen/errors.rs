use crate::lexer::token::Span;

/// Failures reported while lowering a typed AST to Morph IR.
///
/// Every variant carries the [`Span`] of the source construct that triggered it.
#[derive(Debug, Clone, thiserror::Error)]
pub enum CodeGenError {
    /// A call referenced a function that was never compiled.
    #[error("undefined function: {name}")]
    UndefinedFunction {
        /// The unresolved function name.
        name: String,
        /// Source location of the call.
        span: Span,
    },

    /// An expression referenced a local that is not in scope.
    #[error("undefined variable: {name}")]
    UndefinedVariable {
        /// The unresolved variable name.
        name: String,
        /// Source location of the reference.
        span: Span,
    },

    /// The lowering logic hit a state it does not handle.
    #[error("codegen error: {message}")]
    Internal {
        /// A description of the unexpected state.
        message: String,
        /// Source location being lowered.
        span: Span,
    },

    /// The construct is valid Morph but has no lowering yet.
    #[error("unsupported expression: {message}")]
    Unsupported {
        /// A description of what is unsupported.
        message: String,
        /// Source location of the unsupported construct.
        span: Span,
    },

    /// The type's size or alignment could not be computed.
    #[error("type layout error: {message}")]
    LayoutError {
        /// A description of the layout failure.
        message: String,
        /// Source location of the type.
        span: Span,
    },
}
