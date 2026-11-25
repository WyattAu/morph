/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.ClifTarget
import Morph.MIR

/-!
# Stage B items B2/B3: the MIR→CLIF encoder and per-operator agreement

`docs/STAGEB-SCOPE.md` §3. The encoder is **partial on purpose**: it returns
`none` for every MIR construct whose CLIF semantics this model does not yet
have, so an unencodable program fails loudly instead of compiling to something
whose meaning differs. What it accepts, it proves correct one operator at a
time — each `agree_*` lemma below is one instruction's worth of the eventual
`clif_correct`.

## What the fragment contains, and why the rest is out

| MIR | CLIF | condition |
|-----|------|-----------|
| `.const dst (.int n)` | `iconst` | `n` in i64 range |
| `.binop .add/.sub/.mul` | `iadd`/`isub`/`imul` | result in i64 range |
| `.binop .eq/…/geq` on ints | `icmp` | none — exact |
| `.binop .and/.or` on bools | `band`/`bor` | none — exact |
| `.binop .shl` | `ishl` | amount in `[0,64)`, result in range |
| `.binop .shr` | `sshr` | amount in `[0,64)` |
| `.unop .notb` | `bnot` | result in i64 range |

Rejected, each for a measured reason rather than caution:

- `.div`/`.mod` — Euclidean against truncating, and `x/0 = 0` against a trap.
- `.andb`/`.orb`/`.xorb` — the oracle defines these by **parity**
  (`n % 2 = 1 && …`), not bitwise; they coincide with `band`/`bor` only on
  `{0,1}` operands.
- `.not` — boolean negation, which is not `bnot` (the i64 complement). It needs
  an `icmp`/`bxor` idiom the model does not have yet.
- `.copy` — CLIF has no copy; it needs either a rename pass or a materialised
  zero register (`iadd dst src 0`), both encoder plumbing rather than semantics.
- `.const` with a non-integer payload, and every memory, call and `phi`
  instruction — no encoding in this subset.

## Register numbering

`MIR.ValId` and `Clif.Reg` are both `Nat`, and the encoder keeps the number, so
a CLIF environment *is* a MIR environment and agreement is pointwise equality
rather than a relation over a renaming. That is a modelling convenience, not a
claim about real CLIF: value numbering in emitted text is the renderer's
business (B5), and `clif_correct` composes with it only through
`render_parse_id`.
-/

open Morph.Core

namespace Morph.Clif

/-- The two register files coincide: `MIR.Env.update` and `Clif.Env.set` are the
same functional update. MIR writes the test as `x == dst`, the model as
`x = dst`; on `Nat` those agree because `Nat`'s `BEq` is lawful. -/
theorem update_eq_set (m : Morph.MIR.Env) (d : Nat) (v : Value) :
    Morph.MIR.Env.update m d v = Env.set m d v := by
  funext x
  by_cases h : x = d <;> simp [Morph.MIR.Env.update, Env.set, h]

/-! ## The encoder -/

/-- MIR binop → CLIF instruction, `none` for everything outside the fragment. -/
def binopInstr (op : Morph.MIR.BinOp) (dst l r : Nat) : Option Instr :=
  match op with
  | .add => some (.iadd dst l r)
  | .sub => some (.isub dst l r)
  | .mul => some (.imul dst l r)
  | .eq => some (.icmp dst .eq l r)
  | .neq => some (.icmp dst .ne l r)
  | .lt => some (.icmp dst .slt l r)
  | .leq => some (.icmp dst .sle l r)
  | .gt => some (.icmp dst .sgt l r)
  | .geq => some (.icmp dst .sge l r)
  | .shl => some (.ishl dst l r)
  | .shr => some (.sshr dst l r)
  | .and => some (.band dst l r)
  | .or => some (.bor dst l r)
  | .div | .mod | .andb | .orb | .xorb | .not => none

/-- MIR unop → CLIF instruction. `.not` (boolean negation) is rejected: `bnot`
is the i64 complement, which is `.notb`'s meaning. -/
def unopInstr : Morph.MIR.UnOp → Nat → Nat → Option Instr
  | .notb, dst, src => some (.bnot dst src)
  | .not, _, _ => none

/-- Encode one MIR instruction. -/
def instrEncode : Morph.MIR.Instr → Option Instr
  | .const dst (.int n) => some (.iconst dst n)
  | .binop dst op l r _τ => binopInstr op dst l r
  | .unop dst op src _τ => unopInstr op dst src
  | _ => none

/-- Encode a straight-line instruction list. Written as an explicit two-way
match rather than a `do` block so `instrEncodes_cons` below is invertible. -/
def instrEncodes : List Morph.MIR.Instr → Option (List Instr)
  | [] => some []
  | i :: is =>
    match instrEncode i, instrEncodes is with
    | some c, some cs => some (c :: cs)
    | _, _ => none

/-- The cons case of the encoder, in the direction the simulation needs. -/
theorem instrEncodes_cons {i : Morph.MIR.Instr} {is : List Morph.MIR.Instr}
    {cs : List Instr} :
    instrEncodes (i :: is) = some cs ↔
      ∃ c cs', instrEncode i = some c ∧ instrEncodes is = some cs' ∧ cs = c :: cs' := by
  cases hc : instrEncode i <;> cases hs : instrEncodes is <;>
    simp [instrEncodes, hc, hs, eq_comm]

/-- Encode a single-block function: its `return` register becomes the model's
return register. Multi-block bodies are rejected — the Stage B fragment is
`StraightStmts`-shaped, and control flow is a separate obligation. -/
def blockEncode (b : Morph.MIR.Block) : Option Func :=
  match b.terminator with
  | .return_ src => (instrEncodes b.instrs).map fun is => { instrs := is, retSrc := src }
  | _ => none

/-! Rejections, stated so that later case analysis can discharge them by `simp`. -/

@[simp] theorem binopInstr_div (dst l r : Nat) : binopInstr .div dst l r = none := rfl

@[simp] theorem binopInstr_mod (dst l r : Nat) : binopInstr .mod dst l r = none := rfl

@[simp] theorem binopInstr_andb (dst l r : Nat) : binopInstr .andb dst l r = none := rfl

@[simp] theorem binopInstr_orb (dst l r : Nat) : binopInstr .orb dst l r = none := rfl

@[simp] theorem binopInstr_xorb (dst l r : Nat) : binopInstr .xorb dst l r = none := rfl

@[simp] theorem unopInstr_not (dst src : Nat) : unopInstr .not dst src = none := rfl

@[simp] theorem instrEncode_const_bool (dst : Nat) (b : Bool) :
    instrEncode (.const dst (.bool b)) = none := rfl

@[simp] theorem instrEncode_copy (dst src : Nat) : instrEncode (.copy dst src) = none := rfl

@[simp] theorem instrEncode_load (dst loc : Nat) (cap : Capability) :
    instrEncode (.load dst loc cap) = none := rfl

/-- Stage C item C8b: `call` has no CLIF encoding in this subset. The target
cannot name a call (there is no `Instr.call`, by design — it would break every
Stage B match), so the encoder refuses it and no call-bearing block reaches
the target. The call/sig model itself lives additively in `Morph.ClifTarget`
(`Sig`/`CFunc`/`bindCArgs`/`runCallee`), with the value-passing bridge below. -/
@[simp] theorem instrEncode_call (dst : Option Nat) (fn : String)
    (args : List Nat) : instrEncode (.call dst fn args) = none := rfl

/-- Encoder success implies the list is call-free. -/
theorem instrEncodes_some_noCall {is : List Morph.MIR.Instr}
    {cs : List Instr} (h : instrEncodes is = some cs) :
    ∀ dst fn args, Morph.MIR.Instr.call dst fn args ∉ is := by
  induction is generalizing cs with
  | nil =>
      intro dst fn args hmem
      exact absurd hmem (by simp)
  | cons i rest ih =>
      intro dst fn args hmem
      rw [instrEncodes_cons] at h
      obtain ⟨c, cs', henc, hrest, rfl⟩ := h
      simp only [List.mem_cons] at hmem
      rcases hmem with rfl | hmem
      · simp [instrEncode_call] at henc
      · exact ih hrest dst fn args hmem

/-- Any instruction list containing a `call` is refused by the encoder. -/
theorem instrEncodes_of_hasCall {is : List Morph.MIR.Instr}
    (h : ∃ dst fn args, Morph.MIR.Instr.call dst fn args ∈ is) :
    instrEncodes is = none := by
  cases henc : instrEncodes is with
  | none => rfl
  | some cs =>
      obtain ⟨dst, fn, args, hmem⟩ := h
      exact absurd hmem
        (instrEncodes_some_noCall henc dst fn args)

/-! ## Value-passing bridge (Stage C, item C8 remainder)

`MIR.bindCallArgs` binds actuals to `(register, type)` formals with
`MIR.Env.update`; `bindCArgs` binds the same values to the signature's
registers with `Clif.Env.set`. When the formal registers are the signature
(`ps.map Prod.fst = rs`), both succeed on the same arguments to the same
environment — the ABI/layout correspondence the call simulation is stated
over. The two register files are definitionally one (`Nat → Option Value`),
so the conclusion is function equality, via `update_eq_set`. -/

/-- The MIR and CLIF binders agree when the formals name the signature. -/
theorem bindCallArgs_bindCArgs_agree {ps : List (Morph.MIR.ValId × Typ)}
    {rs : List Reg} {ws : List Value} (hregs : ps.map Prod.fst = rs)
    {menv : Morph.MIR.Env} {cenv : Env}
    (hm : Morph.MIR.bindCallArgs ps ws = some menv)
    (hc : bindCArgs rs ws = some cenv) :
    menv = cenv := by
  induction ps generalizing rs ws menv cenv with
  | nil =>
      cases rs with
      | nil =>
          cases ws with
          | nil =>
              simp only [Morph.MIR.bindCallArgs] at hm
              simp only [bindCArgs] at hc
              obtain rfl := Option.some.inj hm
              obtain rfl := Option.some.inj hc
              rfl
          | cons w ws => simp [Morph.MIR.bindCallArgs] at hm
      | cons r rs => simp at hregs
  | cons p ps ih =>
      obtain ⟨v, τ⟩ := p
      cases rs with
      | nil => simp at hregs
      | cons r rs =>
          simp at hregs
          obtain ⟨rfl, hrest⟩ := hregs
          cases ws with
          | nil => simp [Morph.MIR.bindCallArgs] at hm
          | cons w ws =>
              simp only [Morph.MIR.bindCallArgs] at hm
              simp only [bindCArgs] at hc
              cases hbindM : Morph.MIR.bindCallArgs ps ws with
              | none => rw [hbindM] at hm; simp at hm
              | some envM' =>
                  cases hbindC : bindCArgs rs ws with
                  | none => rw [hbindC] at hc; simp at hc
                  | some envC' =>
                      rw [hbindM] at hm; rw [hbindC] at hc
                      obtain rfl := Option.some.inj hm
                      obtain rfl := Option.some.inj hc
                      have ihe := ih hrest hbindM hbindC
                      rw [update_eq_set, ihe]

/-- The MIR and typed CLIF binders agree when the formals are the
signature. Same shape as `bindCallArgs_bindCArgs_agree`, with the
registers and the types both named by the hypothesis (`ValId` and `Reg
are both `Nat`, so one equality says both). The extra `typMatches` case
is the typed layer's content: a successful typed bind has already
checked every actual, so the check discharges without new hypotheses. -/
theorem bindCallArgs_bindTArgs_agree {ps : List (Morph.MIR.ValId × Typ)}
    {ts : TSig} {ws : List Value} (h : ps = ts)
    {menv : Morph.MIR.Env} {cenv : Env}
    (hm : Morph.MIR.bindCallArgs ps ws = some menv)
    (hc : bindTArgs ts ws = some cenv) :
    menv = cenv := by
  induction ps generalizing ts ws menv cenv with
  | nil =>
      cases ts with
      | nil =>
          cases ws with
          | nil =>
              simp only [Morph.MIR.bindCallArgs] at hm
              simp only [bindTArgs] at hc
              obtain rfl := Option.some.inj hm
              obtain rfl := Option.some.inj hc
              rfl
          | cons w ws => simp [Morph.MIR.bindCallArgs] at hm
      | cons t ts => simp at h
  | cons p ps ih =>
      obtain ⟨v, τ⟩ := p
      cases ts with
      | nil => simp at h
      | cons t ts =>
          simp at h
          obtain ⟨rfl, hrest⟩ := h
          cases ws with
          | nil => simp [Morph.MIR.bindCallArgs] at hm
          | cons w ws =>
              simp only [Morph.MIR.bindCallArgs] at hm
              simp only [bindTArgs] at hc
              cases he : typMatches w τ with
              | false => simp [he] at hc
              | true =>
                  simp only [he] at hc
                  cases hbindM : Morph.MIR.bindCallArgs ps ws with
                  | none => rw [hbindM] at hm; simp at hm
                  | some envM' =>
                      cases hbindC : bindTArgs ts ws with
                      | none => rw [hbindC] at hc; simp at hc
                      | some envC' =>
                          rw [hbindM] at hm; rw [hbindC] at hc
                          obtain rfl := Option.some.inj hm
                          obtain rfl := Option.some.inj hc
                          have ihe := ih hrest hbindM hbindC
                          rw [update_eq_set, ihe]

/-! ## Per-operator agreement (B3)

Each lemma states: under the fragment's hypotheses, the CLIF step produces
exactly the environment MIR's `evalInstr` produces. The `wrap` hypotheses are
discharged by `wrap_eq_self` from a bound on the *result* value, which is what
B4's range invariant supplies; comparisons and boolean operators need no
hypothesis at all, so they are exact for all inputs. -/

/-- `.const` with an integer payload. -/
theorem agree_const {m : Morph.MIR.Env} {dst : Nat} {n : Int}
    (hlo : -(2 : Int) ^ 63 ≤ n) (hhi : n < (2 : Int) ^ 63) :
    Morph.MIR.evalInstr m (.const dst (.int n)) = step m (.iconst dst n) := by
  have hw : wrap n = n := wrap_eq_self hlo hhi
  have hmir : Morph.MIR.evalInstr m (.const dst (.int n))
      = some (Morph.MIR.Env.update m dst (.int n)) := by
    simp [Morph.MIR.evalInstr]
  have hclif : step m (.iconst dst n) = some (Env.set m dst (.int n)) := by
    simp [step, hw]
  rw [hmir, hclif, update_eq_set]

/-- `.add`. -/
theorem agree_add {m : Morph.MIR.Env} {dst l r : Nat} {a b : Int} {τ : Typ}
    (hl : m l = some (.int a)) (hr : m r = some (.int b))
    (hlo : -(2 : Int) ^ 63 ≤ a + b) (hhi : a + b < (2 : Int) ^ 63) :
    Morph.MIR.evalInstr m (.binop dst .add l r τ) = step m (.iadd dst l r) := by
  have hw : wrap (a + b) = a + b := wrap_eq_self hlo hhi
  have hmir : Morph.MIR.evalInstr m (.binop dst .add l r τ)
      = some (Morph.MIR.Env.update m dst (.int (a + b))) := by
    simp [Morph.MIR.evalInstr, Morph.MIR.evalBinOp, Morph.Executable.evalBinop,
      Morph.MIR.BinOp.toOperator, hl, hr]
  have hclif : step m (.iadd dst l r) = some (Env.set m dst (.int (a + b))) := by
    simp [step, asInt, hl, hr, hw]
  rw [hmir, hclif, update_eq_set]

/-- `.sub`. -/
theorem agree_sub {m : Morph.MIR.Env} {dst l r : Nat} {a b : Int} {τ : Typ}
    (hl : m l = some (.int a)) (hr : m r = some (.int b))
    (hlo : -(2 : Int) ^ 63 ≤ a - b) (hhi : a - b < (2 : Int) ^ 63) :
    Morph.MIR.evalInstr m (.binop dst .sub l r τ) = step m (.isub dst l r) := by
  have hw : wrap (a - b) = a - b := wrap_eq_self hlo hhi
  have hmir : Morph.MIR.evalInstr m (.binop dst .sub l r τ)
      = some (Morph.MIR.Env.update m dst (.int (a - b))) := by
    simp [Morph.MIR.evalInstr, Morph.MIR.evalBinOp, Morph.Executable.evalBinop,
      Morph.MIR.BinOp.toOperator, hl, hr]
  have hclif : step m (.isub dst l r) = some (Env.set m dst (.int (a - b))) := by
    simp [step, asInt, hl, hr, hw]
  rw [hmir, hclif, update_eq_set]

/-- `.mul`. -/
theorem agree_mul {m : Morph.MIR.Env} {dst l r : Nat} {a b : Int} {τ : Typ}
    (hl : m l = some (.int a)) (hr : m r = some (.int b))
    (hlo : -(2 : Int) ^ 63 ≤ a * b) (hhi : a * b < (2 : Int) ^ 63) :
    Morph.MIR.evalInstr m (.binop dst .mul l r τ) = step m (.imul dst l r) := by
  have hw : wrap (a * b) = a * b := wrap_eq_self hlo hhi
  have hmir : Morph.MIR.evalInstr m (.binop dst .mul l r τ)
      = some (Morph.MIR.Env.update m dst (.int (a * b))) := by
    simp [Morph.MIR.evalInstr, Morph.MIR.evalBinOp, Morph.Executable.evalBinop,
      Morph.MIR.BinOp.toOperator, hl, hr]
  have hclif : step m (.imul dst l r) = some (Env.set m dst (.int (a * b))) := by
    simp [step, asInt, hl, hr, hw]
  rw [hmir, hclif, update_eq_set]

/-- `.eq` — exact for all inputs. -/
theorem agree_eq {m : Morph.MIR.Env} {dst l r : Nat} {a b : Int} {τ : Typ}
    (hl : m l = some (.int a)) (hr : m r = some (.int b)) :
    Morph.MIR.evalInstr m (.binop dst .eq l r τ) = step m (.icmp dst .eq l r) := by
  have hmir : Morph.MIR.evalInstr m (.binop dst .eq l r τ)
      = some (Morph.MIR.Env.update m dst (.bool (a == b))) := by
    simp [Morph.MIR.evalInstr, Morph.MIR.evalBinOp, Morph.Executable.evalBinop,
      Morph.MIR.BinOp.toOperator, hl, hr]
  have hclif : step m (.icmp dst .eq l r) = some (Env.set m dst (.bool (a == b))) := by
    simp [step, evalCond, hl, hr]
  rw [hmir, hclif, update_eq_set]

/-- `.neq` — exact for all inputs. -/
theorem agree_neq {m : Morph.MIR.Env} {dst l r : Nat} {a b : Int} {τ : Typ}
    (hl : m l = some (.int a)) (hr : m r = some (.int b)) :
    Morph.MIR.evalInstr m (.binop dst .neq l r τ) = step m (.icmp dst .ne l r) := by
  have hmir : Morph.MIR.evalInstr m (.binop dst .neq l r τ)
      = some (Morph.MIR.Env.update m dst (.bool !(a == b))) := by
    simp [Morph.MIR.evalInstr, Morph.MIR.evalBinOp, Morph.Executable.evalBinop,
      Morph.MIR.BinOp.toOperator, hl, hr]
  have hclif : step m (.icmp dst .ne l r) = some (Env.set m dst (.bool !(a == b))) := by
    simp [step, evalCond, hl, hr]
  rw [hmir, hclif, update_eq_set]

/-- `.lt` — exact for all inputs. -/
theorem agree_lt {m : Morph.MIR.Env} {dst l r : Nat} {a b : Int} {τ : Typ}
    (hl : m l = some (.int a)) (hr : m r = some (.int b)) :
    Morph.MIR.evalInstr m (.binop dst .lt l r τ) = step m (.icmp dst .slt l r) := by
  have hmir : Morph.MIR.evalInstr m (.binop dst .lt l r τ)
      = some (Morph.MIR.Env.update m dst (.bool (a < b))) := by
    simp [Morph.MIR.evalInstr, Morph.MIR.evalBinOp, Morph.Executable.evalBinop,
      Morph.MIR.BinOp.toOperator, hl, hr]
  have hclif : step m (.icmp dst .slt l r) = some (Env.set m dst (.bool (a < b))) := by
    simp [step, evalCond, hl, hr]
  rw [hmir, hclif, update_eq_set]

/-- `.leq` — exact for all inputs. -/
theorem agree_leq {m : Morph.MIR.Env} {dst l r : Nat} {a b : Int} {τ : Typ}
    (hl : m l = some (.int a)) (hr : m r = some (.int b)) :
    Morph.MIR.evalInstr m (.binop dst .leq l r τ) = step m (.icmp dst .sle l r) := by
  have hmir : Morph.MIR.evalInstr m (.binop dst .leq l r τ)
      = some (Morph.MIR.Env.update m dst (.bool (a ≤ b))) := by
    simp [Morph.MIR.evalInstr, Morph.MIR.evalBinOp, Morph.Executable.evalBinop,
      Morph.MIR.BinOp.toOperator, hl, hr]
  have hclif : step m (.icmp dst .sle l r) = some (Env.set m dst (.bool (a ≤ b))) := by
    simp [step, evalCond, hl, hr]
  rw [hmir, hclif, update_eq_set]

/-- `.gt` — exact for all inputs. -/
theorem agree_gt {m : Morph.MIR.Env} {dst l r : Nat} {a b : Int} {τ : Typ}
    (hl : m l = some (.int a)) (hr : m r = some (.int b)) :
    Morph.MIR.evalInstr m (.binop dst .gt l r τ) = step m (.icmp dst .sgt l r) := by
  have hmir : Morph.MIR.evalInstr m (.binop dst .gt l r τ)
      = some (Morph.MIR.Env.update m dst (.bool (a > b))) := by
    simp [Morph.MIR.evalInstr, Morph.MIR.evalBinOp, Morph.Executable.evalBinop,
      Morph.MIR.BinOp.toOperator, hl, hr]
  have hclif : step m (.icmp dst .sgt l r) = some (Env.set m dst (.bool (a > b))) := by
    simp [step, evalCond, hl, hr]
  rw [hmir, hclif, update_eq_set]

/-- `.geq` — exact for all inputs. -/
theorem agree_geq {m : Morph.MIR.Env} {dst l r : Nat} {a b : Int} {τ : Typ}
    (hl : m l = some (.int a)) (hr : m r = some (.int b)) :
    Morph.MIR.evalInstr m (.binop dst .geq l r τ) = step m (.icmp dst .sge l r) := by
  have hmir : Morph.MIR.evalInstr m (.binop dst .geq l r τ)
      = some (Morph.MIR.Env.update m dst (.bool (a ≥ b))) := by
    simp [Morph.MIR.evalInstr, Morph.MIR.evalBinOp, Morph.Executable.evalBinop,
      Morph.MIR.BinOp.toOperator, hl, hr]
  have hclif : step m (.icmp dst .sge l r) = some (Env.set m dst (.bool (a ≥ b))) := by
    simp [step, evalCond, hl, hr]
  rw [hmir, hclif, update_eq_set]

/-- `.and` on booleans — exact for all inputs. -/
theorem agree_and {m : Morph.MIR.Env} {dst l r : Nat} {a b : Bool} {τ : Typ}
    (hl : m l = some (.bool a)) (hr : m r = some (.bool b)) :
    Morph.MIR.evalInstr m (.binop dst .and l r τ) = step m (.band dst l r) := by
  have hmir : Morph.MIR.evalInstr m (.binop dst .and l r τ)
      = some (Morph.MIR.Env.update m dst (.bool (a && b))) := by
    simp [Morph.MIR.evalInstr, Morph.MIR.evalBinOp, Morph.Executable.evalBinop,
      Morph.MIR.BinOp.toOperator, hl, hr]
  have hclif : step m (.band dst l r) = some (Env.set m dst (.bool (a && b))) := by
    simp [step, asBool, hl, hr]
  rw [hmir, hclif, update_eq_set]

/-- `.or` on booleans — exact for all inputs. -/
theorem agree_or {m : Morph.MIR.Env} {dst l r : Nat} {a b : Bool} {τ : Typ}
    (hl : m l = some (.bool a)) (hr : m r = some (.bool b)) :
    Morph.MIR.evalInstr m (.binop dst .or l r τ) = step m (.bor dst l r) := by
  have hmir : Morph.MIR.evalInstr m (.binop dst .or l r τ)
      = some (Morph.MIR.Env.update m dst (.bool (a || b))) := by
    simp [Morph.MIR.evalInstr, Morph.MIR.evalBinOp, Morph.Executable.evalBinop,
      Morph.MIR.BinOp.toOperator, hl, hr]
  have hclif : step m (.bor dst l r) = some (Env.set m dst (.bool (a || b))) := by
    simp [step, asBool, hl, hr]
  rw [hmir, hclif, update_eq_set]

/-- `.shl`: needs the amount in CLIF's shift range and the product in i64 range. -/
theorem agree_shl {m : Morph.MIR.Env} {dst l r : Nat} {a b : Int} {τ : Typ}
    (hl : m l = some (.int a)) (hr : m r = some (.int b))
    (hb : 0 ≤ b ∧ b < 64)
    (hlo : -(2 : Int) ^ 63 ≤ a * Int.pow 2 b.toNat)
    (hhi : a * Int.pow 2 b.toNat < (2 : Int) ^ 63) :
    Morph.MIR.evalInstr m (.binop dst .shl l r τ) = step m (.ishl dst l r) := by
  have hw : wrap (a * Int.pow 2 b.toNat) = a * Int.pow 2 b.toNat := wrap_eq_self hlo hhi
  have hmir : Morph.MIR.evalInstr m (.binop dst .shl l r τ)
      = some (Morph.MIR.Env.update m dst (.int (a * Int.pow 2 b.toNat))) := by
    simp [Morph.MIR.evalInstr, Morph.MIR.evalBinOp, Morph.Executable.evalBinop,
      Morph.MIR.BinOp.toOperator, hl, hr]
  have hclif : step m (.ishl dst l r)
      = some (Env.set m dst (.int (a * Int.pow 2 b.toNat))) := by
    simp [step, asInt, shiftAmount, hl, hr, hb, hw]
  rw [hmir, hclif, update_eq_set]

/-- `.shr`: the amount must be in CLIF's shift range, but the result needs no
range hypothesis — an arithmetic shift right cannot overflow. -/
theorem agree_shr {m : Morph.MIR.Env} {dst l r : Nat} {a b : Int} {τ : Typ}
    (hl : m l = some (.int a)) (hr : m r = some (.int b))
    (hb : 0 ≤ b ∧ b < 64) :
    Morph.MIR.evalInstr m (.binop dst .shr l r τ) = step m (.sshr dst l r) := by
  have hmir : Morph.MIR.evalInstr m (.binop dst .shr l r τ)
      = some (Morph.MIR.Env.update m dst (.int (Int.shiftRight a b.toNat))) := by
    simp [Morph.MIR.evalInstr, Morph.MIR.evalBinOp, Morph.Executable.evalBinop,
      Morph.MIR.BinOp.toOperator, hl, hr]
  have hclif : step m (.sshr dst l r)
      = some (Env.set m dst (.int (Int.shiftRight a b.toNat))) := by
    simp [step, asInt, shiftAmount, hl, hr, hb]
  rw [hmir, hclif, update_eq_set]

/-- `.notb`: the i64 complement agrees with the oracle's `-n - 1` exactly, given
the result is representable. -/
theorem agree_notb {m : Morph.MIR.Env} {dst src : Nat} {a : Int} {τ : Typ}
    (hs : m src = some (.int a))
    (hlo : -(2 : Int) ^ 63 ≤ -a - 1) (hhi : -a - 1 < (2 : Int) ^ 63) :
    Morph.MIR.evalInstr m (.unop dst .notb src τ) = step m (.bnot dst src) := by
  have hw : wrap (-a - 1) = -a - 1 := wrap_eq_self hlo hhi
  have hmir : Morph.MIR.evalInstr m (.unop dst .notb src τ)
      = some (Morph.MIR.Env.update m dst (.int (-a - 1))) := by
    simp [Morph.MIR.evalInstr, Morph.MIR.evalUnOp, Morph.Executable.evalUnop,
      Morph.MIR.UnOp.toOperator, hs]
  have hclif : step m (.bnot dst src) = some (Env.set m dst (.int (-a - 1))) := by
    simp [step, asInt, hs, hw]
  rw [hmir, hclif, update_eq_set]

end Morph.Clif
