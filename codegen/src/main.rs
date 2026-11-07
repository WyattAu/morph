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

/// The runner: prints the function's i64 result as decimal, the same shape as
/// `morph run`'s output for the corresponding program.
const RUNNER_SOURCE: &str = "\
#include <stdio.h>
extern long morph_main(void);
int main(void) {
    printf(\"%ld\\n\", morph_main());
    return 0;
}
";

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

    // The reader is the trusted entry point: whatever the artifact says, this is
    // where it becomes a `Function`. A rejection here is a bug in the printer,
    // not in the driver, so the message is passed through unhidden.
    let mut funcs = cranelift_reader::parse_functions(&text)
        .map_err(|e| format!("CLIF reader rejected the artifact: {e}"))?;
    if funcs.len() != 1 {
        return Err(format!(
            "expected exactly one function, found {} (stage B emits single-function modules)",
            funcs.len()
        ));
    }
    let func = funcs.remove(0);

    let want_ret = [AbiParam::new(types::I64)];
    if !func.signature.params.is_empty() || func.signature.returns != want_ret {
        return Err(format!(
            "expected signature `() -> i64`, found {:?}",
            func.signature
        ));
    }

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

    let func_id = module
        .declare_function(ENTRY_SYMBOL, Linkage::Export, &func.signature)
        .map_err(|e| format!("declaring {ENTRY_SYMBOL}: {e}"))?;

    // The text's own name (`%main`) never reaches the object: the symbol comes
    // from `declare_function`, so the artifact stays a plain CLIF module while the
    // runner gets a name that cannot collide with C's `main`.
    let mut ctx = Context::for_function(func);
    module
        .define_function(func_id, &mut ctx)
        .map_err(|e| format!("compiling {ENTRY_SYMBOL}: {e}"))?;

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

    let runner_path = obj_path.with_extension("runner.c");
    fs::write(&runner_path, RUNNER_SOURCE)
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
