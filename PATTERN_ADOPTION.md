# Pattern adoption

Morph is a Lean 4 formal specification with a Rust reference compiler.
The compiler crate is a pure pipeline; the CLI crate performs I/O.

| Pattern | Status | Evidence |
|---|---|---|
| T1 | adopted | compiler/src/parser/mod.rs:1596 (parse tokens into typed AST nodes with ParseError values; TypeCheckResult in compiler/src/typeck/mod.rs:18) |
| T13 | adopted | cli/src/driver.rs:103 (CLI shell reads sources and prints diagnostics; the compiler crate holds the pure lexer, parser, typeck, codegen pipeline) |
