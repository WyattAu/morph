use crate::diagnostic::{Diagnostic, DiagnosticLevel};

pub struct Emitter<'a> {
    source: &'a str,
    source_name: &'a str,
}

impl<'a> Emitter<'a> {
    pub fn new(source: &'a str, source_name: &'a str) -> Self {
        Self {
            source,
            source_name,
        }
    }

    pub fn emit(&self, diag: &Diagnostic) -> String {
        let mut out = String::new();

        let level_str = match diag.level {
            DiagnosticLevel::Error => "error",
            DiagnosticLevel::Warning => "warning",
            DiagnosticLevel::Note => "note",
            DiagnosticLevel::Help => "help",
        };

        out.push_str(&format!("{}[{}]: {}\n", level_str, diag.code, diag.message));
        out.push_str(&format!(
            "  --> {}:{}:{}\n",
            self.source_name, diag.span.line, diag.span.col
        ));

        if let Some(line_text) = self.get_line(diag.span.line) {
            out.push_str("   |\n");
            let line_num = diag.span.line;
            out.push_str(&format!("{:3}| {}\n", line_num, line_text));
            out.push_str("   | ");
            let offset = diag.span.col.saturating_sub(1) as usize;
            for _ in 0..offset {
                out.push(' ');
            }
            let width = if diag.span.start < diag.span.end {
                (diag.span.end - diag.span.start).max(1)
            } else {
                1
            };
            for _ in 0..width {
                out.push('^');
            }
            out.push('\n');
        }

        for suggestion in &diag.suggestions {
            out.push_str(&format!("  help: {}\n", suggestion));
        }

        out
    }

    pub fn emit_all(&self, diagnostics: &[Diagnostic]) -> String {
        diagnostics
            .iter()
            .map(|d| self.emit(d))
            .collect::<Vec<_>>()
            .join("\n")
    }

    fn get_line(&self, line: u32) -> Option<&str> {
        self.source.lines().nth(line as usize - 1)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::diagnostic::Diagnostic;
    use crate::lexer::token::Span;

    #[test]
    fn test_emit_error() {
        let source = "fn foo() { }";
        let emitter = Emitter::new(source, "test.morph");
        let diag = Diagnostic::error("ERR_COMPILE_001", "unexpected token", Span::new(0, 2, 1, 1));
        let output = emitter.emit(&diag);
        assert!(output.contains("error"));
        assert!(output.contains("ERR_COMPILE_001"));
        assert!(output.contains("test.morph"));
        assert!(output.contains("unexpected token"));
    }

    #[test]
    fn test_emit_with_suggestion() {
        let source = "fn foo() { }";
        let emitter = Emitter::new(source, "test.morph");
        let diag = Diagnostic::error("ERR_COMPILE_001", "bad token", Span::new(0, 2, 1, 1))
            .with_suggestion("try using a valid token");
        let output = emitter.emit(&diag);
        assert!(output.contains("help: try using a valid token"));
    }

    #[test]
    fn test_emit_warning() {
        let source = "let x = 1;";
        let emitter = Emitter::new(source, "test.morph");
        let diag = Diagnostic::warning("WARN_001", "unused variable", Span::new(4, 5, 1, 5));
        let output = emitter.emit(&diag);
        assert!(output.contains("warning"));
    }
}
