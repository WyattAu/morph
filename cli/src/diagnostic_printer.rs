use morph_compiler::diagnostic::emitter::Emitter;
use morph_compiler::diagnostic::{Diagnostic, DiagnosticLevel};

/// Writes [`Diagnostic`]s to the terminal in a rustc-like format.
///
/// Errors and warnings go to stderr, while notes and help go to stdout, so a
/// caller can capture messages without diagnostics noise mixed in.
pub struct DiagnosticPrinter<'a> {
    emitter: Emitter<'a>,
}

impl<'a> DiagnosticPrinter<'a> {
    /// Creates a printer that renders spans against `source`, labelled `filename`.
    pub fn new(source: &'a str, filename: &'a str) -> Self {
        Self {
            emitter: Emitter::new(source, filename),
        }
    }

    /// Renders one diagnostic to a string, including the source snippet.
    pub fn format_diagnostic(&self, diagnostic: &Diagnostic) -> String {
        self.emitter.emit(diagnostic)
    }

    /// Writes one diagnostic to stderr or stdout according to its level.
    pub fn print(&self, diagnostic: &Diagnostic) {
        let output = self.format_diagnostic(diagnostic);
        match diagnostic.level {
            DiagnosticLevel::Error | DiagnosticLevel::Warning => eprint!("{}", output),
            DiagnosticLevel::Note | DiagnosticLevel::Help => print!("{}", output),
        }
    }

    /// Writes every diagnostic, then a `N errors, M warnings found` summary.
    ///
    /// The summary is only printed when at least one error or warning is
    /// present.
    pub fn print_all(&self, diagnostics: &[Diagnostic]) {
        let mut error_count = 0usize;
        let mut warning_count = 0usize;

        for diagnostic in diagnostics {
            self.print(diagnostic);
            match diagnostic.level {
                DiagnosticLevel::Error => error_count += 1,
                DiagnosticLevel::Warning => warning_count += 1,
                DiagnosticLevel::Note | DiagnosticLevel::Help => {}
            }
        }

        if error_count > 0 || warning_count > 0 {
            eprintln!();
            let mut parts = Vec::new();
            if error_count > 0 {
                parts.push(format!(
                    "{} error{}",
                    error_count,
                    if error_count == 1 { "" } else { "s" }
                ));
            }
            if warning_count > 0 {
                parts.push(format!(
                    "{} warning{}",
                    warning_count,
                    if warning_count == 1 { "" } else { "s" }
                ));
            }
            eprintln!("{} found", parts.join(", "));
        }
    }
}
