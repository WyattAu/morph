/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Driver

/-!
# The `morph` executable

A thin IO shell over `Morph.Driver`, which contains all of the logic.
Values exit 0; parse failures and stuck evaluations exit 1.
-/

open Morph.Driver

private def finish (out : Outcome) : IO UInt32 := do
  match out with
  | .value s => IO.println s; return 0
  | .parseFailed s => IO.eprintln s; return 1
  | .stuck => IO.eprintln (report .stuck); return 1

def main (args : List String) : IO UInt32 := do
  match args with
  | ["eval", src] => finish (runSource src)
  | ["parse", src] => finish (parseSource src)
  | ["run", path] => finish (runProgram (← IO.FS.readFile path))
  | _ => IO.println usage; return 1
