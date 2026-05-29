use morph_compiler::diagnostic::{Diagnostic, DiagnosticLevel};
use morph_compiler::diagnostic::emitter::Emitter;

pub struct DiagnosticPrinter<'a> {
    emitter: Emitter<'a>,
}

impl<'a> DiagnosticPrinter<'a> {
    pub fn new(source: &'a str, filename: &'a str) -> Self {
        Self {
            emitter: Emitter::new(source, filename),
        }
    }

    pub fn format_diagnostic(&self, diagnostic: &Diagnostic) -> String {
        self.emitter.emit(diagnostic)
    }

    pub fn print(&self, diagnostic: &Diagnostic) {
        let output = self.format_diagnostic(diagnostic);
        match diagnostic.level {
            DiagnosticLevel::Error | DiagnosticLevel::Warning => eprint!("{}", output),
            DiagnosticLevel::Note | DiagnosticLevel::Help => print!("{}", output),
        }
    }

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
                parts.push(format!("{} error{}", error_count, if error_count == 1 { "" } else { "s" }));
            }
            if warning_count > 0 {
                parts.push(format!("{} warning{}", warning_count, if warning_count == 1 { "" } else { "s" }));
            }
            eprintln!("{} found", parts.join(", "));
        }
    }
}
