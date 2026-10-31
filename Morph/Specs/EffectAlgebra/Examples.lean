/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Specs.EffectAlgebra.Lemmas

/-!
# Worked examples: one model per effect class

The point of the algebraic treatment is that `IO`, `Net` and `Time` differ only
in *which answers a model allows*, not in the shape of the computation. These
examples make that concrete: the same computation syntax denotes a singleton
under a deterministic model and a two-element set under a nondeterministic one.
-/

namespace Morph.Specs.EffectAlgebra

/-- A deterministic model: every operation answers with exactly one value, the
way `IO` behaves for a fixed filesystem. `raise` answers nothing, so failure is
modelled as absence rather than a distinguished form. -/
def ioModel : Model String := { answer := fun o => match o with
  | .read _ => ["contents"]
  | .write _ _ => ["ok"]
  | .now _ => ["noon"]
  | .sleep _ => ["done"]
  | .connect _ => ["connected"]
  | .send _ _ => ["sent"]
  | .exec _ => ["ran"]
  | .raise _ => [] }

/-- A nondeterministic model: `Time.now` may answer with any instant. `Net.connect`
may fail, and its answer set may be empty. -/
def nondetModel : Model String := { answer := fun o => match o with
  | .now _ => ["t0", "t1"]
  | .connect _ => []
  | .read _ => ["contents"]
  | _ => ["ok"] }

/-- `read "cfg"`, then log it, then return it. -/
def prog : Eff String :=
  .op (.read "cfg") (fun v => .op (.write "log" v) (fun _ => .pure v))

/-- Under a deterministic model the computation denotes a single answer. -/
example : denote ioModel prog = ["contents"] := rfl

/-- The same computation under a model with a failing `Net.connect`… -/
def netProg : Eff String :=
  .op (.connect "example.com") (fun _ => .pure "body")

/-- …denotes *nothing at all*. Failure is the empty answer set, not a special
case: this is what makes `Net` a partial effect without a second effect type. -/
example : denote nondetModel netProg = [] :=
  denote_unanswered nondetModel (.connect "example.com") (fun _ => .pure "body") rfl

/-- `Time.now` is nondeterministic: one syntax, two answers. -/
def tick : Eff String := .op (.now "utc") (fun t => .pure t)

example : denote ioModel tick = ["noon"] := rfl

example : denote nondetModel tick = ["t0", "t1"] := rfl

example : (denote nondetModel tick).length = 2 := rfl

/-- The effect set of `prog` is exactly the two `IO` operations it performs. -/
example : Eff.classes prog = [.io, .io] := rfl

/-- A handler that covers `IO` and `Time` — the classes `prog` performs. -/
def ioTimeHandler : Handler String := { model := ioModel, covers := [.io, .time] }

/-- **Handling discharges the effects.** Nothing is left outstanding, even though
`prog` performs two effects: this is Bauer & Pretnar's non-monotone step. -/
example : ioTimeHandler.residual prog = [] :=
  covered_residual_empty ioTimeHandler prog (by
    intro k hk
    have hk' : k = .io := by simpa [Eff.classes, prog, Op.class] using hk
    simp [ioTimeHandler, hk'])

/-- A handler that does *not* cover `Net` leaves the `Net` effect outstanding.
A handler removes effects; it never adds them. -/
def ioOnlyHandler : Handler String := { model := ioModel, covers := [.io] }

example : ioOnlyHandler.residual netProg = [.net] := rfl

/-- Loop 93 pins for the named-row chain (spec v2.1.0 §2.3). -/
example : classLE .io .net := classLE_io_net
example : ¬ classLE .time .net := by simp only [classLE, classRank]; omega
example : EffectClass.time ∈ namedRow .system := by simp [namedRow]
example : ¬ (EffectClass.time ∈ namedRow .net) := by simp [namedRow]

end Morph.Specs.EffectAlgebra
