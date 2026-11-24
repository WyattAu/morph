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
  | ["test", path] => do
      let targets : List String ← try
        do let entries ← System.FilePath.readDir path
           let files := (entries.toList.map fun e => e.path.toString).filter
             (·.endsWith ".hum")
           pure (files.mergeSort (· ≤ ·))
        catch _ => pure [path]
      if targets.isEmpty then
        IO.eprintln s!"no .hum test files found under {path}"
        return 1
      else
        let mut results : List (String × Bool × String) := []
        for t in targets do
          let content ← try IO.FS.readFile t catch _ => pure ""
          let (passed, detail) := runTestCase content
          results := results ++ [(t, passed, detail)]
        IO.println (formatTestReport results)
        return if results.all fun (_, p, _) => p then 0 else 1
  | ["version"] => IO.println Morph.versionString; return 0
  | _ => IO.println usage; return 1
