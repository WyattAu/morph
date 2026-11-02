/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Specs.AuthIdentity.Examples

/-!
# Authentication and identity kernel — validation (E-1361–E-1370)

Status: In Progress (loop 104).

Second, independent pass over the ten cores. `Examples.lean` demonstrates the
definitions; this file replays them as *checks*: each theorem is applied to a
fresh instance, negative cases are asserted, and the multi-step laws
(delegation chains, share rotation, proof checking, replay rejection) are
exercised where a single example could pass by accident.

Run: `lake build Morph.Tests.AuthIdentity`.
-/

namespace Morph.Tests.AuthIdentity

open Morph.Specs.AuthIdentity

/-! ## E-1361: fresh chain, fresh binding -/

example : findCap [⟨5, 1⟩, ⟨8, 4⟩] 8 3 = some ⟨[8], 3⟩ := by decide

example : findCap [⟨5, 1⟩, ⟨8, 4⟩] 5 4 = none := by decide

example : Holds ⟨[8], 3⟩ ⟨8, 3⟩ :=
  findCap_sound (caps := [⟨5, 1⟩, ⟨8, 4⟩]) (by decide)

/-- Translation of the binding: different requests never collide. -/
example : bind 100 9 ≠ bind 101 9 := by decide

example : bind 7 3 = 7003 := rfl

/-! ## E-1362: fresh accumulator -/

example : acc [3, 7] = 21 := rfl

example : Verify (acc [3, 7]) 7 (witness [3, 7] 7) :=
  witness_verifies (by decide)

example : acc (remove [3, 7] 3) * 3 = acc [3, 7] :=
  acc_delete (by decide)

example : acc (remove [3, 7] 11) = acc [3, 7] :=
  acc_remove_not_mem (by decide)

/-! ## E-1363: monotone lattice on fresh policies -/

/-- A writer needs level 2 on index 1. -/
def writePolicy : Policy := [⟨1, 2⟩]

example : allows writePolicy ⟨0, 2, 0⟩ = true := by decide

example : allows writePolicy ⟨0, 1, 0⟩ = false := by decide

/-- Raising attributes keeps the grant. -/
example : Satisfies writePolicy ⟨0, 5, 9⟩ := by
  have base : Satisfies writePolicy ⟨0, 2, 0⟩ := by
    rw [← allows_iff]; decide
  apply raising_never_loses base
  intro i
  cases i with
  | zero => decide
  | succ n =>
    cases n with
    | zero => decide
    | succ m => simp [Attrs.get]

/-- A ceiling below the bar blocks every principal under it. -/
example : ¬ Satisfies writePolicy ⟨0, 1, 0⟩ := by
  intro h
  have h2 := h ⟨1, 2⟩ (by simp [writePolicy])
  simp only [Constraint.ok, Attrs.get] at h2
  omega

/-! ## E-1364: revocation episode -/

/-- Revoke 5 in a fresh state, then check the whole algebra. -/
example : ¬ (revoke ⟨1, []⟩ 5).valid 5 2 :=
  revoke_invalidates ⟨1, []⟩ 5

example : (revoke ⟨1, []⟩ 5).epoch = 2 := rfl

example : (revoke ⟨1, []⟩ 5).valid 9 2 :=
  revoke_preserves (s := ⟨1, []⟩) (id := 5) (y := 9) (by decide) (by decide)

example : ¬ (revoke ⟨1, []⟩ 5).valid 5 1 :=
  stale_witness_rejected (s := ⟨1, []⟩) (id := 5) (y := 5) (wEpoch := 1)
    (by decide)

/-! ## E-1365: delegation chain -/

/-- Two successive delegations verify against the locally derived root. -/
example : Verifies
    ((delegate ((delegate 0 [] 11).1) ((delegate 0 [] 11).2) 13).1)
    ((delegate ((delegate 0 [] 11).1) ((delegate 0 [] 11).2) 13).2) := by
  exact delegate_preserves
    (delegate_preserves (show Verifies 0 [] from rfl) 11) 13

/-- A change in the tail changes the digest. -/
example : digest [11, 13] ≠ digest [11, 12] := by decide

/-- Chain length tracks delegations. -/
example : (delegate 0 [11, 13] 5).2.length = 3 :=
  delegate_length 0 5 [11, 13]

/-! ## E-1366: tags and double-spend -/

example : issue 5 1 200 9 = ⟨1, 9, 5001200⟩ := by decide

/-- Double-spend: the second use of the same nonce is refused. -/
example : spend [7] 7 = none := by decide

example : (spend [] 7).isSome = true := by decide

example : 9 ∈ [9, 7] ∧ ∀ m ∈ [7], m ∈ [9, 7] :=
  spend_sound (show spend [7] 9 = some [9, 7] from by decide)

/-! ## E-1367: proof checking on fresh contexts -/

/-- An and-elimination proof checks. -/
example : check [(.and (.atom 3) (.atom 4))] (.andElimL (.atom 4) (.hyp 0))
    (.atom 3) = true := by decide

example : Derives [(.and (.atom 3) (.atom 4))] (.atom 3) :=
  check_sound (show check [(.and (.atom 3) (.atom 4))]
    (.andElimL (.atom 4) (.hyp 0)) (.atom 3) = true from by decide)

/-- A mismatched right component does not check. -/
example : check [(.and (.atom 3) (.atom 4))] (.andElimL (.atom 9) (.hyp 0))
    (.atom 3) = false := by decide

/-- Modus ponens derives. -/
example : Derives [(.imp (.atom 1) (.atom 2)), (.atom 1)] (.atom 2) :=
  check_sound (show check [(.imp (.atom 1) (.atom 2)), (.atom 1)]
    (.impElim (.atom 1) (.hyp 0) (.hyp 1)) (.atom 2) = true from by decide)

/-! ## E-1368: sharing round-trips on fresh secrets -/

example : combine (share 7 [1, 2, 3]) = 7 :=
  combine_share [1, 2, 3] 7

example : share 7 [1, 2, 3] = [1, 2, 3, 1] := rfl

/-- Rotation on a fresh secret keeps reconstruction. -/
example : combine (9 :: (7 - 9 - combine [4, 1]) :: [4, 1]) = 7 :=
  rotate_preserves 9 7 [4, 1]

/-- The missing share is forced. -/
example : combine [4, 8, 30] = 42 := by decide

example : (4 : Int) = 42 - combine [8, 30] :=
  last_share_determined (show combine [4, 8, 30] = 42 from by decide)

/-! ## E-1369: blinding on fresh values -/

example : unblind (signMsg (blind 11 50) 3) 50 = signMsg 11 3 :=
  unblind_sign 11 50 3

example : ∃ b, blind 11 b = 61 := view_consistent 61 11

example : blind 11 50 ≠ blind 11 51 := by decide

/-! ## E-1370: PUF checks on fresh words -/

example : mismatches [true, true, false] [true, false, false] = 1 := rfl

example : mismatches [true, true, false] [true, false, false] =
    mismatches [true, false, false] [true, true, false] :=
  mismatches_comm _ _

example : accept 2 [true, true, false] [true, false, false] = true := by decide

example : accept 0 [true, true, false] [true, false, false] = false := by decide

example : ctSteps 3 = 3 := rfl

example : earlySteps [true, true, true] [true, false, true] = 2 := rfl

end Morph.Tests.AuthIdentity
