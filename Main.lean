/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Driver
import Morph.Version

/-!
# The `morph` executable

A thin IO shell over `Morph.Driver`, which contains all of the logic.
Values exit 0; parse failures, stuck evaluations and codegen rejections exit 1.
`build --codegen=cranelift` is the one command that writes a file: it puts the
artifact next to its input (`main.hum` → `main.clif`) and prints the path.
-/

open Morph.Driver

private def finish (out : Outcome) : IO UInt32 := do
  match out with
  | .value s => IO.println s; return 0
  | .parseFailed s => IO.eprintln s; return 1
  | .stuck => IO.eprintln (report .stuck); return 1
  | .typeError s => IO.eprintln s; return 1
  | .unsupported s => IO.eprintln s; return 1

def main (args : List String) : IO UInt32 := do
  match args with
  | ["eval", src] => finish (runSource src)
  | ["parse", src] => finish (parseSource src)
  | ["check", src] => finish (checkSource src)
  | ["run", "--hir", path] => finish (runProgramHIR (← IO.FS.readFile path))
  | ["run", path] => finish (runProgram (← IO.FS.readFile path))
  | ["build", "--codegen=cranelift", path] =>
      match buildClif (← IO.FS.readFile path) with
      | .value text =>
          let out := clifArtifactPath path
          IO.FS.writeFile out text
          IO.println s!"wrote {out}"
          return 0
      | out => finish out
  | ["fmt", path] => finish (formatProgram (← IO.FS.readFile path))
  | ["doc", path] => finish (docSource (← IO.FS.readFile path))
  | ["version"] => IO.println Morph.versionString; return 0
  | _ => IO.println usage; return 1
