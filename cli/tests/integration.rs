use std::path::Path;

use morph::driver::{Config, Driver, Dialect, EmitTarget};

fn fixture_path(name: &str) -> String {
    let base = env!("CARGO_MANIFEST_DIR");
    format!("{}/tests/fixtures/{}", base, name)
}

fn load_fixture(name: &str) -> Driver {
    let path_str = fixture_path(name);
    let path = Path::new(&path_str);
    Driver::from_file(path, Config::default()).expect("fixture should load")
}

fn invalid_driver(source: &str) -> Driver {
    Driver::new(source.to_string(), "invalid.morph".to_string(), Config::default())
}

#[test]
fn test_lex_hello() {
    let driver = load_fixture("hello.morph");
    let tokens = driver.lex().expect("lex should succeed");
    assert!(tokens.len() > 0, "should have tokens");
    assert!(tokens.iter().any(|t| matches!(&t.kind, morph_compiler::lexer::token::TokenKind::Fn)));
    assert!(tokens.iter().any(|t| matches!(&t.kind, morph_compiler::lexer::token::TokenKind::Identifier(ref s) if s == "main")));
}

#[test]
fn test_lex_types() {
    let driver = load_fixture("types.morph");
    let tokens = driver.lex().expect("lex should succeed");
    assert!(tokens.len() > 0);
    assert!(tokens.iter().any(|t| matches!(&t.kind, morph_compiler::lexer::token::TokenKind::Type)));
}

#[test]
fn test_lex_actor() {
    let driver = load_fixture("actor.morph");
    let tokens = driver.lex().expect("lex should succeed");
    assert!(tokens.len() > 0);
    assert!(tokens.iter().any(|t| matches!(&t.kind, morph_compiler::lexer::token::TokenKind::Act)));
}

#[test]
fn test_lex_match() {
    let driver = load_fixture("match.morph");
    let tokens = driver.lex().expect("lex should succeed");
    assert!(tokens.len() > 0);
    assert!(tokens.iter().any(|t| matches!(&t.kind, morph_compiler::lexer::token::TokenKind::Fix)));
}

#[test]
fn test_parse_hello() {
    let driver = load_fixture("hello.morph");
    let items = driver.parse().expect("parse should succeed");
    assert!(items.len() >= 3, "hello.morph should have at least 3 items");
    let fn_names: Vec<&str> = items
        .iter()
        .filter_map(|i| match &i.kind {
            morph_compiler::ast::Item::FnDecl(f) => Some(f.name.as_str()),
            _ => None,
        })
        .collect();
    assert!(fn_names.contains(&"main"));
    assert!(fn_names.contains(&"add"));
    assert!(fn_names.contains(&"greet"));
}

#[test]
fn test_parse_types() {
    let driver = load_fixture("types.morph");
    let items = driver.parse().expect("parse should succeed");
    assert!(items.len() >= 5, "types.morph should have at least 5 items");

    let type_names: Vec<&str> = items
        .iter()
        .filter_map(|i| match &i.kind {
            morph_compiler::ast::Item::TypeDecl(t) => Some(t.name.as_str()),
            _ => None,
        })
        .collect();
    assert!(type_names.contains(&"Point"));
    assert!(type_names.contains(&"Color"));
    assert!(type_names.contains(&"Age"));
}

#[test]
fn test_parse_actor() {
    let driver = load_fixture("actor.morph");
    let items = driver.parse().expect("parse should succeed");
    assert_eq!(items.len(), 1);
    match &items[0].kind {
        morph_compiler::ast::Item::ActorDecl(a) => {
            assert_eq!(a.name, "Counter");
            assert_eq!(a.members.len(), 5);
        }
        _ => panic!("expected actor decl"),
    }
}

#[test]
fn test_parse_match() {
    let driver = load_fixture("match.morph");
    let items = driver.parse().expect("parse should succeed");
    assert_eq!(items.len(), 2);
}

#[test]
fn test_type_check_hello() {
    let driver = load_fixture("hello.morph");
    let result = driver.type_check();
    assert!(result.is_ok(), "type check should pass for hello.morph: {:?}", result.err());
}

#[test]
fn test_type_check_types() {
    let driver = load_fixture("types.morph");
    let result = driver.type_check();
    assert!(result.is_ok(), "type check should pass for types.morph: {:?}", result.err());
}

#[test]
fn test_type_check_actor() {
    let driver = load_fixture("actor.morph");
    let result = driver.type_check();
    assert!(result.is_ok(), "type check should pass for actor.morph: {:?}", result.err());
}

#[test]
fn test_type_check_match() {
    let driver = load_fixture("match.morph");
    let result = driver.type_check();
    assert!(result.is_ok(), "type check should pass for match.morph: {:?}", result.err());
}

#[test]
fn test_compile_hello() {
    let driver = load_fixture("hello.morph");
    let result = driver.compile();
    assert!(result.is_ok(), "compile should succeed for hello.morph: {:?}", result.err());
    let compiled = result.unwrap();
    assert!(compiled.module.functions.len() >= 3, "should have at least 3 functions");
    let fn_names: Vec<&str> = compiled.module.functions.iter().map(|f| f.name.as_str()).collect();
    assert!(fn_names.contains(&"main"));
    assert!(fn_names.contains(&"add"));
    assert!(fn_names.contains(&"greet"));
}

#[test]
fn test_compile_types() {
    let driver = load_fixture("types.morph");
    let result = driver.compile();
    assert!(result.is_ok(), "compile should succeed for types.morph: {:?}", result.err());
    let compiled = result.unwrap();
    assert!(compiled.module.functions.len() >= 3, "should have at least 3 functions");
    assert!(compiled.module.type_info.len() >= 2, "should have at least 2 type infos");
}

#[test]
fn test_compile_actor() {
    let driver = load_fixture("actor.morph");
    let result = driver.compile();
    assert!(result.is_ok(), "compile should succeed for actor.morph: {:?}", result.err());
    let compiled = result.unwrap();
    assert!(compiled.module.functions.len() >= 1, "actor should have at least one compiled function");
}

#[test]
fn test_compile_match() {
    let driver = load_fixture("match.morph");
    let result = driver.compile();
    assert!(result.is_ok(), "compile should succeed for match.morph: {:?}", result.err());
    let compiled = result.unwrap();
    assert!(compiled.module.functions.len() >= 2, "should have at least 2 functions");
}

#[test]
fn test_lex_error_invalid_char() {
    let driver = invalid_driver("$ $ $");
    let result = driver.lex();
    assert!(result.is_err(), "should fail to lex invalid chars");
    let errors = result.unwrap_err();
    assert_eq!(errors.len(), 3);
}

#[test]
fn test_lex_error_unterminated_string() {
    let driver = invalid_driver("\"hello");
    let result = driver.lex();
    assert!(result.is_err(), "should fail on unterminated string");
}

#[test]
fn test_parse_error_unexpected_token() {
    let driver = invalid_driver("}}}");
    let result = driver.parse();
    assert!(result.is_err(), "should fail to parse unexpected tokens");
}

#[test]
fn test_type_check_error_undefined_var() {
    let driver = invalid_driver("fn foo() { undefined_var }");
    let result = driver.type_check();
    assert!(result.is_err(), "should fail on undefined variable");
    let diags = result.err().unwrap();
    assert!(diags.iter().any(|d| d.message.contains("undefined")));
}

#[test]
fn test_type_check_error_type_mismatch() {
    let driver = invalid_driver("fn foo() -> i64 { true }");
    let result = driver.type_check();
    assert!(result.is_err(), "should fail on type mismatch");
}

#[test]
fn test_compile_error_lex_failure() {
    let driver = invalid_driver("fn foo() { $ }");
    let result = driver.compile();
    assert!(result.is_err(), "should fail to compile with lex errors");
}

#[test]
fn test_compile_error_parse_failure() {
    let driver = invalid_driver("fn () { }");
    let result = driver.compile();
    assert!(result.is_err(), "should fail to compile with parse errors");
}

#[test]
fn test_missing_file() {
    let path = Path::new("/nonexistent/file.morph");
    let result = Driver::from_file(path, Config::default());
    assert!(result.is_err(), "should fail to load missing file");
}

#[test]
fn test_empty_source() {
    let driver = invalid_driver("");
    let result = driver.compile();
    assert!(result.is_ok(), "empty source should compile (empty module)");
}

#[test]
fn test_simple_arithmetic() {
    let driver = invalid_driver("fn add(a: i64, b: i64) -> i64 { a + b }");
    let result = driver.compile();
    assert!(result.is_ok(), "simple arithmetic should compile: {:?}", result.err());
    let compiled = result.unwrap();
    assert_eq!(compiled.module.functions.len(), 1);
    let func = &compiled.module.functions[0];
    use morph_compiler::codegen::Instruction;
    assert!(func.instructions.iter().any(|i| matches!(i, Instruction::Add)));
}

#[test]
fn test_string_literal() {
    let driver = invalid_driver("fn greet() -> str { \"hello world\" }");
    let result = driver.compile();
    assert!(result.is_ok(), "string literal should compile: {:?}", result.err());
    let compiled = result.unwrap();
    assert!(compiled.module.strings.contains(&"hello world".to_string()));
}

#[test]
fn test_if_else_compilation() {
    let driver = invalid_driver("fn abs(x: i64) -> i64 { if x < 0 { -x } else { x } }");
    let result = driver.compile();
    assert!(result.is_ok(), "if-else should compile: {:?}", result.err());
    let compiled = result.unwrap();
    use morph_compiler::codegen::Instruction;
    let func = &compiled.module.functions[0];
    assert!(func.instructions.iter().any(|i| matches!(i, Instruction::JumpIfNot(_))));
}

#[test]
fn test_struct_type_compilation() {
    let source = r#"
        type Point = { x: f64, y: f64 }
        fn origin() -> Point { Point { x: 0.0, y: 0.0 } }
    "#;
    let driver = invalid_driver(source);
    let result = driver.compile();
    assert!(result.is_ok(), "struct should compile: {:?}", result.err());
    let compiled = result.unwrap();
    assert!(compiled.module.type_info.iter().any(|t| t.name == "Point"));
}

#[test]
fn test_dialect_config() {
    let config = Config {
        dialect: Dialect::Min,
        debug: true,
        emit: EmitTarget::Ast,
    };
    let driver = Driver::new("fn main() { 1 }".to_string(), "test.morph".to_string(), config);
    let result = driver.compile();
    assert!(result.is_ok());
}
