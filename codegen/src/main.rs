// Copyright 2024-2025 The Morph Project Authors
// SPDX-License-Identifier: Apache-2.0

//! The stage B Cranelift driver (item B7).
//!
//! Reads the CLIF that `morph build --codegen=cranelift` writes, compiles it with
//! `cranelift-codegen`, emits an object, links it against a two-line C runner,
//! and prints the paths. It runs nothing itself: the corpus harness
//! (`tests/codegen/native.sh`) runs the produced executable and compares its
//! stdout to the value `morph run` printed, which is B8's differential.
//!
//! Two deliberate choices:
//!
//! - The CLIF function is exported as `morph_main`, not under its own name. The
//!   artifact names it `%main`, and a C `main` cannot coexist with the runner's;
//!   the symbol is ours to choose at `declare_function`, so the text stays a
//!   plain CLIF module and no name rewriting happens before the reader.
//! - The runner is embedded as a string rather than tracked as a `.c` file, so
//!   the driver is a single reviewable unit and has no path assumptions.
//!
//! This crate is trusted code in the Stage B sense (ADR-032 §3): the proof stops
//! at the text, and the differential corpus is the evidence for everything after
//! it.

use std::env;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, ExitCode};

use cranelift_codegen::ir::{types, AbiParam};
use cranelift_codegen::settings::{self, Configurable};
use cranelift_codegen::Context;
use cranelift_module::{default_libcall_names, Linkage, Module};
use cranelift_object::{ObjectBuilder, ObjectModule};

/// The symbol the artifact is exported under, and what the runner calls.
const ENTRY_SYMBOL: &str = "morph_main";

/// The runner for integer-valued programs: prints the function's i64 result
/// as decimal, the same shape as `morph run`'s output.
const RUNNER_SOURCE_I64: &str = "\
#include <stdio.h>
extern long morph_main(void);
int main(void) {
    printf(\"%ld\\n\", morph_main());
    return 0;
}
";

/// The runner for boolean-valued programs: `icmp` results are i8 in this
/// dialect, and `morph run` prints them as true/false.
const RUNNER_SOURCE_I8: &str = "\
#include <stdio.h>
extern signed char morph_main(void);
int main(void) {
    printf(\"%s\\n\", morph_main() ? \"true\" : \"false\");
    return 0;
}
";

/// The result kinds the stage B subset emits: integers (i64) and booleans
/// (i8 — Cranelift's `icmp` result type).
#[derive(Clone, Copy, PartialEq, Eq)]
enum RetKind {
    I64,
    I8,
}

fn usage() -> String {
    "usage: morph-clif <input.clif> [-o <executable>]\n".to_string()
        + "  compiles the CLIF `morph build --codegen=cranelift` emits\n"
        + "  writes <input>.o next to it and links the executable\n"
}

/// A path with its extension replaced: `main.clif` -> `main.o`.
fn with_extension(path: &Path, ext: &str) -> PathBuf {
    path.with_extension(ext)
}

fn main() -> ExitCode {
    match run() {
        Ok(()) => ExitCode::SUCCESS,
        Err(e) => {
            eprintln!("morph-clif: {e}");
            ExitCode::FAILURE
        }
    }
}

fn run() -> Result<(), String> {
    let args: Vec<String> = env::args().skip(1).collect();
    let (input, output) = match args.as_slice() {
        [input] => (PathBuf::from(input), None),
        [input, flag, out] if flag == "-o" => (PathBuf::from(input), Some(PathBuf::from(out))),
        _ => return Err(usage()),
    };

    let text = fs::read_to_string(&input).map_err(|e| format!("{}: {e}", input.display()))?;

    // Morph artifacts open with ABI documentation lines (`function %name(sig)
    // -> ret` with no body). The reader's grammar has no form for them — a bare
    // header would swallow the next `function` keyword as a calling convention —
    // so the trusted driver drops them before the reader sees the text. What
    // remains is exactly the definitions, and each definition's own header is
    // the signature truth the reader checks.
    // Function names in file order — the declaration order below makes each
    // function's position its `FuncId`, which is what a `u0:<n>` reference
    // encodes.
    let names: Vec<&str> = text
        .lines()
        .filter_map(|l| {
            let t = l.trim_start();
            // Definitions only: decl-only lines are dropped below and must not
            // shift the positions the references encode.
            if !(t.starts_with("function ") && t.contains('{')) {
                return None;
            }
            let rest = t.strip_prefix("function ")?.trim_start_matches('%');
            let end = rest.find('(').unwrap_or(rest.len());
            Some(&rest[..end])
        })
        .collect();

    let program_text: String = text
        .lines()
        .filter_map(|l| {
            let t = l.trim_start();
            if t.starts_with("function ") && !t.contains('{') {
                return None; // ABI documentation line, not a definition
            }
            // The artifact references callees symbolically (`fn0 = %add sig0`),
            // but cranelift-module can only relocate `ExternalName::user`
            // targets — a user name encodes the callee's FuncId as `u0:<n>`,
            // and testcase (`%name`) targets panic in the relocation path (they
            // exist for filetests only). Rewrite each symbolic reference to the
            // numeric encoding of the position the callee will be declared at.
            if t.starts_with("fn") && t.contains(" = %") {
                if let Some((lhs, rest)) = t.split_once(" = %") {
                    let mut parts = rest.split_whitespace();
                    let name = parts.next().unwrap_or("");
                    let sig = parts.next().unwrap_or("");
                    if let Some(idx) = names.iter().position(|n| *n == name) {
                        return Some(format!("{lhs} = u0:{idx} {sig}"));
                    }
                }
            }
            Some(l.to_string())
        })
        .collect::<Vec<_>>()
        .join("\n");
    let program_text = format!("{program_text}\n");

    // The reader is the trusted entry point: whatever the filtered text says,
    // this is where it becomes a `Function`. A rejection here is a bug in the
    // printer, not in the driver, so the message is passed through unhidden.
    let mut funcs = cranelift_reader::parse_functions(&program_text)
        .map_err(|e| format!("CLIF reader rejected the artifact: {e}"))?;
    if funcs.is_empty() {
        return Err("artifact contains no function definitions".to_string());
    }
    // The entry is `%main`; every other function is a callee it calls. The
    // reader's Display for a symbolic name carries the `%`, so strip it before
    // comparing (and keep the raw form for declarations — that is exactly the
    // string cranelift-module uses when it resolves the call references).
    let main_idx = funcs
        .iter()
        .position(|f| {
            let n = f.name.to_string();
            n.trim_start_matches('%') == "main"
        })
        .ok_or("artifact has no %main entry function")?;
    if !funcs[main_idx].signature.params.is_empty() {
        return Err(
            "the entry function %main takes parameters; the runner calls it with none".to_string(),
        );
    }
    let ret_ty = match funcs[main_idx].signature.returns.as_slice() {
        [t] if t.value_type == types::I64 => RetKind::I64,
        [t] if t.value_type == types::I8 => RetKind::I8,
        _ => {
            return Err(format!(
                "expected signature `() -> i64` or `() -> i8` on %main, found {:?}",
                funcs[main_idx].signature
            ))
        }
    };

    let mut flag_builder = settings::builder();
    // The subset is straight-line integer arithmetic; a faster opt level changes
    // nothing about its results and keeps compile time irrelevant.
    flag_builder
        .set("opt_level", "speed")
        .map_err(|e| format!("setting opt_level: {e}"))?;
    let isa_builder =
        cranelift_native::builder().map_err(|e| format!("no native ISA for this host: {e}"))?;
    let isa = isa_builder
        .finish(settings::Flags::new(flag_builder))
        .map_err(|e| format!("building the ISA: {e}"))?;

    let obj_builder = ObjectBuilder::new(isa, "morph_module", default_libcall_names())
        .map_err(|e| format!("object builder: {e}"))?;
    let mut module = ObjectModule::new(obj_builder);

    // Declare everything before defining anything, so the `sig`/`fn` references
    // in a call-bearing body bind inside this module. The entry exports under
    // `morph_main` (a name that cannot collide with C's `main`); callees keep
    // their artifact names, local to the object.
    let mut func_ids = Vec::with_capacity(funcs.len());
    for (i, f) in funcs.iter().enumerate() {
        let (symbol, linkage) = if i == main_idx {
            (ENTRY_SYMBOL.to_string(), Linkage::Export)
        } else {
            (f.name.to_string(), Linkage::Local)
        };
        let id = module
            .declare_function(&symbol, linkage, &f.signature)
            .map_err(|e| format!("declaring {symbol}: {e}"))?;
        func_ids.push(id);
    }

    for (i, f) in funcs.into_iter().enumerate() {
        let mut ctx = Context::for_function(f);
        module
            .define_function(func_ids[i], &mut ctx)
            .map_err(|e| format!("compiling function {}: {e}", func_ids[i]))?;
    }

    let product = module.finish();
    let bytes = product
        .emit()
        .map_err(|e| format!("emitting the object: {e}"))?;

    let obj_path = with_extension(&input, "o");
    fs::write(&obj_path, &bytes).map_err(|e| format!("{}: {e}", obj_path.display()))?;

    let exe_path = output.unwrap_or_else(|| {
        let mut p = with_extension(&input, "");
        p.set_extension("");
        let name = p
            .file_name()
            .map(|n| n.to_string_lossy().to_string())
            .unwrap_or_else(|| "a".to_string());
        p.with_file_name(format!("{name}-native"))
    });

    let runner_source = match ret_ty {
        RetKind::I64 => RUNNER_SOURCE_I64,
        RetKind::I8 => RUNNER_SOURCE_I8,
    };
    let runner_path = obj_path.with_extension("runner.c");
    fs::write(&runner_path, runner_source)
        .map_err(|e| format!("{}: {e}", runner_path.display()))?;

    let status = Command::new("cc")
        .arg(&runner_path)
        .arg(&obj_path)
        .arg("-o")
        .arg(&exe_path)
        .status()
        .map_err(|e| format!("running cc: {e}"))?;
    if !status.success() {
        return Err(format!("cc failed linking {}", exe_path.display()));
    }

    println!("wrote {}", obj_path.display());
    println!("wrote {}", exe_path.display());
    Ok(())
}
