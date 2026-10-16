/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Specs.TaintFlow.Lemmas

namespace Morph.Specs.TaintFlow

/-! ## Worked examples

Two variables: `pubOut` is observable, `secret` is not. Everything here is
closed and computable, so `decide` / `rfl` do the work; the content is in
`Lemmas.lean`.
-/

/-- `secret` is secret; everything else defaults to public. -/
def ρ₀ : TEnv := fun x => if x = "secret" then .sec else .pub

/-- A program that reads a secret and writes it into a public sink. -/
def leakyProg : List (String × TExpr) :=
  [("pubOut", .var "secret")]

/-- The same program with an explicit declassification. -/
def gatedProg : List (String × TExpr) :=
  [("pubOut", .decl (.var "secret"))]

example : taint ρ₀ (.var "secret") = .sec := by
  decide

example : taint ρ₀ (.decl (.var "secret")) = .pub := by
  decide

/-- The sink check is what rejects the leaky program: writing a secret into a
public variable is not allowed. -/
example : ¬ AllowedAssign ρ₀ "pubOut" (.var "secret") := by
  unfold AllowedAssign
  decide

/-- The declassifying program passes the sink check (the `decl` erased the
label). -/
example : AllowedAssign ρ₀ "pubOut" (.decl (.var "secret")) := by
  unfold AllowedAssign
  decide

/-- An implicit flow is caught by the sink check too: branching on a secret
is already an implicit flow even though neither branch is a secret. -/
example : ¬ AllowedAssign ρ₀ "pubOut" (.ite (.var "secret") (.lit) (.lit)) := by
  unfold AllowedAssign
  decide

/-- ... and the same expression is fine for a secret sink. -/
example : AllowedAssign (fun _ => .sec) "s" (.ite (.var "secret") (.lit) (.lit)) := by
  unfold AllowedAssign
  decide

/-- Crossing the dialect boundary changes nothing about the label: translation
either returns the same expression or rejects it — it never silently
downgrades. -/
example : ∀ e', translate .strict .pub (.var "secret") = some e' →
    taint ρ₀ e' = taint ρ₀ (.var "secret") :=
  fun e' h => taint_preserved ρ₀ .strict .pub _ _ h

/-- **Robust declassification.** An untrusted program counter cannot carry a
declassification into the strict dialect. -/
example : translate .strict .pub (.decl (.var "secret")) = none := by
  decide

example : translateProg .strict .pub gatedProg = none := by
  rfl

/-- With a trusted pc it crosses unchanged, labels included. -/
example : translateProg .strict .sec gatedProg = some gatedProg := by
  rfl

example : taint ρ₀ (.decl (.var "secret")) = taint ρ₀ (.decl (.var "secret")) := rfl

end Morph.Specs.TaintFlow