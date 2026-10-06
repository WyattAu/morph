//! CLI crate for the Morph language.

#![deny(missing_docs)]

/// Rendering of compiler diagnostics to the terminal.
pub mod diagnostic_printer;
/// The compilation pipeline driver used by the CLI front end.
pub mod driver;
