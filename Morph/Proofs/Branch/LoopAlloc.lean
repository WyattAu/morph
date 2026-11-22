/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.HIRToMIRCore
import Morph.HIRToMIRTotal

/-!
# Proof crate `LoopAlloc` (L0 leaf): loop-carried register allocation

Estate-style leaf: depends on `Core`/`Total` only, never on
`Morph.HIRToMIRBranch` or another leaf. `Morph.HIRToMIRBranch` imports this
module back; the tree stays green between cuts.

Provenance (statements unchanged, proofs verbatim): `assignedIds`,
`dedupIds`, `LoopInfo`, `carryCopies`, `mkCarried`,
`mkCarried_growth_fresh`, `mkCarried_le`, `mkHeaderPhis` — extracted from
`Morph/HIRToMIRBranch.lean` § "Loop helpers (C7a)" and the header-phis
definition beside it.

A `while` header merges one phi per register the body may assign. The
carried set is syntactic (`assignedIds`, through nested `if` arms and nested
loops); ids missing from `ρ` need no phi (assignment there is a no-op on both
sides — `updAssoc`/`updateHEnv` both drop it). `continue` snapshots the current
env into the carried registers (`carryCopies`); the copies are sequential but
sound, because a body evaluation's fresh result always lies at or above the
current supply while every carried register predates the body — a source can
never be another carried destination.

Nesting is refused for now: a `while` under `loop = some _` lowers to `none`.
-/

namespace Morph.HIRToMIRCorrect

open Morph.Core
open Morph.HIRToMIR
open Morph.MIR
open Morph.Frontend.HIREval
open Morph.Frontend.HIRInterp

/-- Registers assigned anywhere in a statement list. -/
def assignedIds : List HIR.Stmt → List HIR.Id
  | [] => []
  | .assign id _ :: rest => id :: assignedIds rest
  | .ifStmt _ th el :: rest => assignedIds th ++ assignedIds el ++ assignedIds rest
  | .whileLoop _ body :: rest => assignedIds body ++ assignedIds rest
  | _ :: rest => assignedIds rest

/-- Duplicate-free assigned ids (order of first occurrence). `List.eraseDup`
is absent from this toolchain, so fold it locally. -/
def dedupIds (ids : List HIR.Id) : List HIR.Id :=
  ids.foldl (fun acc id => if acc.contains id then acc else acc ++ [id]) []

/-- Loop context for body lowering: `header`/`exit` are the `continue`/`break`
targets, and `carried` pairs each loop-carried id with the register the next
iteration reads. `none` outside any loop body. -/
structure LoopInfo where
  header : MIR.BlockId
  exit : MIR.BlockId
  carried : List (HIR.Id × ValId)

/-- Snapshot every carried register into itself. `none` when a carried id is
unmapped (cannot happen for lowering-produced `carried`, which is filtered by
`rhoLookup`-presence — the `none` branch keeps the definition total). -/
def carryCopies (ρ : List (HIR.Id × ValId)) : List (HIR.Id × ValId) →
    Option (List Instr)
  | [] => some []
  | (id, r) :: rest =>
      match rhoLookup ρ id with
      | none => none
      | some s => (carryCopies ρ rest).map (.copy r s :: ·)

/-- Allocate loop-carried registers: one fresh `r` per assigned id present in
`ρ`, starting at `s`. Returns the carried pairs, the bumped supply, and the
body-entry env. `none` when an id is unmapped (the call site filters those
out, so the `none` branch is dead there — but the definition stays total). -/
def mkCarried (ρ : List (HIR.Id × ValId)) (s : Nat) : List HIR.Id →
    Option (List (HIR.Id × ValId) × Nat × List (HIR.Id × ValId))
  | [] => some ([], s, ρ)
  | id :: ids =>
      match rhoLookup ρ id with
      | none => none
      | some _ =>
          match mkCarried (updAssoc ρ id s) (s + 1) ids with
          | none => none
          | some (cs, s', ρ') => some ((id, s) :: cs, s', ρ')

/-- Allocation only bumps the supply, and the resulting env is fresh above
it: `updAssoc` replaces in place, so every member is either an old mapping
(below `s`) or a carried pair (below `s'`). -/
theorem mkCarried_growth_fresh {ρ : List (HIR.Id × ValId)} {s : Nat}
    {ids : List HIR.Id} {cs : List (HIR.Id × ValId)} {s' : Nat}
    {ρ' : List (HIR.Id × ValId)} (hf : FreshAbove ρ s)
    (h : mkCarried ρ s ids = some (cs, s', ρ')) :
    s ≤ s' ∧ FreshAbove ρ' s' := by
  have hmem_upd : ∀ (σ : List (HIR.Id × ValId)) (id : HIR.Id) (sv : Nat)
      (j : HIR.Id) (v : Nat),
      (j, v) ∈ updAssoc σ id sv → (j, v) ∈ σ ∨ (j = id ∧ v = sv) := by
    intro σ
    induction σ with
    | nil =>
        intro id sv j v hmem
        simp [updAssoc] at hmem
    | cons p rest ih =>
        obtain ⟨j', w⟩ := p
        intro id sv j v hmem
        by_cases heq : j' = id
        · rw [updAssoc, if_pos heq, List.mem_cons] at hmem
          rcases hmem with h0 | h0
          · exact Or.inr ⟨heq ▸ congrArg Prod.fst h0, congrArg Prod.snd h0⟩
          · exact Or.inl (List.mem_cons_of_mem _ h0)
        · rw [updAssoc, if_neg heq, List.mem_cons] at hmem
          rcases hmem with h0 | h0
          · exact Or.inl (List.mem_cons.mpr (Or.inl h0))
          · rcases ih id sv j v h0 with h' | h'
            · exact Or.inl (List.mem_cons_of_mem _ h')
            · exact Or.inr h'
  induction ids generalizing ρ s cs s' ρ' with
  | nil =>
      simp only [mkCarried] at h
      obtain ⟨rfl, rfl, rfl⟩ := Option.some.inj h
      exact ⟨Nat.le_refl _, hf⟩
  | cons id ids ih =>
      simp only [mkCarried] at h
      cases hρ : rhoLookup ρ id with
      | none => rw [hρ] at h; simp at h
      | some _ =>
          rw [hρ] at h
          cases hrec : mkCarried (updAssoc ρ id s) (s + 1) ids with
          | none => rw [hrec] at h; simp at h
          | some q =>
              obtain ⟨cs', s'', ρ''⟩ := q
              rw [hrec] at h
              obtain ⟨rfl, rfl, rfl⟩ := Option.some.inj h
              have hf' : FreshAbove (updAssoc ρ id s) (s + 1) := by
                intro j v hmem
                rcases hmem_upd _ _ _ _ _ hmem with hmem | ⟨rfl, rfl⟩
                · exact Nat.lt_of_lt_of_le (hf _ _ hmem) (Nat.le_succ _)
                · exact Nat.lt_succ_self _
              obtain ⟨hle, hfr⟩ := ih hf' hrec
              exact ⟨Nat.le_trans (Nat.le_succ _) hle, hfr⟩

/-- Supply growth alone needs no freshness hypothesis (the static invariant
`branch_inv` cites this; the executors cite `mkCarried_growth_fresh`). -/
theorem mkCarried_le {ρ : List (HIR.Id × ValId)} {s : Nat}
    {ids : List HIR.Id} {cs : List (HIR.Id × ValId)} {s' : Nat}
    {ρ' : List (HIR.Id × ValId)}
    (h : mkCarried ρ s ids = some (cs, s', ρ')) : s ≤ s' := by
  induction ids generalizing ρ s cs s' ρ' with
  | nil =>
      simp only [mkCarried] at h
      obtain ⟨rfl, rfl, rfl⟩ := Option.some.inj h
      exact Nat.le_refl _
  | cons id ids ih =>
      simp only [mkCarried] at h
      cases hρ : rhoLookup ρ id with
      | none => rw [hρ] at h; simp at h
      | some _ =>
          rw [hρ] at h
          cases hrec : mkCarried (updAssoc ρ id s) (s + 1) ids with
          | none => rw [hrec] at h; simp at h
          | some q =>
              obtain ⟨cs', s'', ρ''⟩ := q
              rw [hrec] at h
              obtain ⟨rfl, rfl, rfl⟩ := Option.some.inj h
              exact Nat.le_trans (Nat.le_succ _) (ih hrec)

/-- Header phis for the carried registers: one entry edge plus one edge per
back-predecessor. The fall-through end reads its sources from the body's exit
env; every trampoline (`continue`) edge reads the carried registers
themselves, which that block's copies just snapshotted. -/
def mkHeaderPhis (ρ : List (HIR.Id × ValId)) (entryPred : MIR.BlockId)
    (carried : List (HIR.Id × ValId)) (fallEnd : MIR.BlockId)
    (ρout : List (HIR.Id × ValId)) (tramps : List MIR.BlockId) :
    Option (List Instr) :=
  carried.foldl (fun acc p =>
    match acc with
    | none => none
    | some phis =>
        match rhoLookup ρ p.1, rhoLookup ρout p.1 with
        | some entrySrc, some backSrc =>
            some (phis ++ [.phi p.2 entryPred entrySrc, .phi p.2 fallEnd backSrc]
              ++ tramps.map (.phi p.2 · p.2))
        | _, _ => none)
    (some [])

end Morph.HIRToMIRCorrect
