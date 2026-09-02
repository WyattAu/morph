//! Compiler crate for the Morph language.

#![deny(missing_docs)]

/// Abstract syntax tree definitions.
pub mod ast;
/// Code generation backend.
pub mod codegen;
/// Compiler diagnostics and error reporting.
pub mod diagnostic;
/// Lexical analysis and tokenization.
pub mod lexer;
/// Parser implementation.
pub mod parser;
/// Type checking and inference.
pub mod typeck;
