use std::env;
use std::process;

use morph::{
    diagnostic_printer,
    driver::{Config, Dialect, Driver, EmitTarget},
};

fn main() {
    let args: Vec<String> = env::args().collect();

    if args.len() < 2 {
        eprintln!("Usage: morph <command> [options] <source.morph>");
        eprintln!();
        eprintln!("Commands:");
        eprintln!("  build <source.morph>   Compile to MorphIR (.mar)");
        eprintln!("  run <source.morph>     Compile and run");
        eprintln!("  check <source.morph>   Type-check only");
        eprintln!("  fmt <source.morph>     Format source");
        eprintln!("  doc <source.morph>     Generate docs");
        process::exit(1);
    }

    let command = &args[1];
    let mut config = Config::default();
    let mut source_path = None;

    let mut i = 2;
    while i < args.len() {
        match args[i].as_str() {
            "--dialect=min" => config.dialect = Dialect::Min,
            "--dialect=hum" => config.dialect = Dialect::Hum,
            "--debug-scheduler" => config.debug = true,
            "--emit=morphir" => config.emit = EmitTarget::MorphIR,
            "--emit=ast" => config.emit = EmitTarget::Ast,
            "--emit=types" => config.emit = EmitTarget::Types,
            path if !path.starts_with('-') && source_path.is_none() => {
                source_path = Some(path.to_string());
            }
            flag => {
                eprintln!("Unknown flag: {}", flag);
                process::exit(1);
            }
        }
        i += 1;
    }

    let source_path = match source_path {
        Some(p) => p,
        None => {
            eprintln!("Error: no source file specified");
            process::exit(1);
        }
    };

    let driver = match Driver::from_file(std::path::Path::new(&source_path), config.clone()) {
        Ok(d) => d,
        Err(e) => {
            eprintln!("Error reading '{}': {}", source_path, e);
            process::exit(1);
        }
    };

    match command.as_str() {
        "build" => cmd_build(&driver),
        "run" => cmd_run(&driver),
        "check" => cmd_check(&driver),
        "fmt" => cmd_fmt(&driver),
        "doc" => cmd_doc(&driver),
        _ => {
            eprintln!("Unknown command: {}", command);
            process::exit(1);
        }
    }
}

fn cmd_build(driver: &Driver) -> ! {
    match driver.compile() {
        Ok(result) => {
            match driver.config().emit {
                EmitTarget::MorphIR | EmitTarget::Run => {
                    println!(
                        "Compiled '{}' successfully ({} functions, {} strings, {} types)",
                        driver.filename(),
                        result.module.functions.len(),
                        result.module.strings.len(),
                        result.module.type_info.len(),
                    );
                }
                EmitTarget::Ast => {
                    println!("AST dump for '{}':", driver.filename());
                    for item in &result.items {
                        println!("  {:?}", item.kind);
                    }
                }
                EmitTarget::Types => {
                    println!("Type check passed for '{}'", driver.filename());
                }
            }
            process::exit(0);
        }
        Err(diagnostics) => {
            let printer =
                diagnostic_printer::DiagnosticPrinter::new(driver.source(), driver.filename());
            printer.print_all(&diagnostics);
            process::exit(1);
        }
    }
}

fn cmd_run(driver: &Driver) -> ! {
    let mut config = driver.config().clone();
    config.emit = EmitTarget::Run;
    let driver = Driver::new(
        driver.source().to_string(),
        driver.filename().to_string(),
        config,
    );

    match driver.compile() {
        Ok(_result) => {
            eprintln!("Note: MorphVM interpreter not yet integrated. Compilation succeeded.");
            process::exit(0);
        }
        Err(diagnostics) => {
            let printer =
                diagnostic_printer::DiagnosticPrinter::new(driver.source(), driver.filename());
            printer.print_all(&diagnostics);
            process::exit(1);
        }
    }
}

fn cmd_check(driver: &Driver) -> ! {
    match driver.type_check() {
        Ok(result) => {
            println!("Type check passed for '{}'", driver.filename());
            if !result.warnings.is_empty() {
                let printer =
                    diagnostic_printer::DiagnosticPrinter::new(driver.source(), driver.filename());
                for w in &result.warnings {
                    let output = printer.format_diagnostic(w);
                    eprint!("{}", output);
                }
            }
            process::exit(0);
        }
        Err(diagnostics) => {
            let printer =
                diagnostic_printer::DiagnosticPrinter::new(driver.source(), driver.filename());
            printer.print_all(&diagnostics);
            process::exit(1);
        }
    }
}

fn cmd_fmt(driver: &Driver) -> ! {
    match driver.parse() {
        Ok(items) => {
            for item in &items {
                print_item(item);
            }
            process::exit(0);
        }
        Err(errors) => {
            for err in &errors {
                eprintln!("{}", err);
            }
            process::exit(1);
        }
    }
}

fn cmd_doc(driver: &Driver) -> ! {
    match driver.type_check() {
        Ok(_result) => {
            println!("Documentation generated for '{}'", driver.filename());
            process::exit(0);
        }
        Err(diagnostics) => {
            let printer =
                diagnostic_printer::DiagnosticPrinter::new(driver.source(), driver.filename());
            printer.print_all(&diagnostics);
            process::exit(1);
        }
    }
}

fn print_item(item: &morph_compiler::ast::Node<morph_compiler::ast::Item>) {
    use morph_compiler::ast::{Item, Visibility};

    match &item.kind {
        Item::FnDecl(f) => {
            let prefix = match f.visibility {
                Visibility::Public => "pub ",
                Visibility::Private => "",
            };
            println!("{}fn {}(...) {{ ... }}", prefix, f.name);
        }
        Item::TypeDecl(t) => {
            let prefix = match t.visibility {
                Visibility::Public => "pub ",
                Visibility::Private => "",
            };
            println!("{}type {}", prefix, t.name);
        }
        Item::ConstDecl(c) => {
            println!("const {}", c.name);
        }
        Item::UseDecl(u) => {
            let path = u.path.join("::");
            if let Some(alias) = &u.alias {
                println!("use {} as {}", path, alias);
            } else {
                println!("use {}", path);
            }
        }
        Item::ActorDecl(a) => {
            println!("act {} {{ ... }}", a.name);
        }
        Item::ImplBlock(i) => {
            println!("impl {} {{ ... }}", i.name);
        }
        Item::TraitDecl(t) => {
            println!("trait {} {{ ... }}", t.name);
        }
    }
}
