use crate::lexer::token::Span;

#[derive(Debug, Clone, thiserror::Error)]
pub enum CodeGenError {
    #[error("undefined function: {name}")]
    UndefinedFunction { name: String, span: Span },

    #[error("undefined variable: {name}")]
    UndefinedVariable { name: String, span: Span },

    #[error("codegen error: {message}")]
    Internal { message: String, span: Span },

    #[error("unsupported expression: {message}")]
    Unsupported { message: String, span: Span },

    #[error("type layout error: {message}")]
    LayoutError { message: String, span: Span },
}
