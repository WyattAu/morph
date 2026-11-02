/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Specs.AuthIdentity.Lemmas

/-!
# Authentication and Identity Kernel — examples (E-1361–E-1370)

Status: In Progress (loop 104, batch CC first cycle).

Concrete instances of the ten cores. Every example is `decide`-checked; the
law witnesses apply the lemmas of `Lemmas.lean` to fresh instances.
-/

namespace Morph.Specs.AuthIdentity

/-! ## E-1361: attestation -/

/-- The chain covers resource 7 at level 2. -/
example : findCap [⟨7, 2⟩, ⟨3, 9⟩] 7 2 = some ⟨[7], 2⟩ := by decide

/-- The chain cannot cover level 3. -/
example : findCap [⟨7, 2⟩, ⟨3, 9⟩] 7 3 = none := by decide

/-- The witness really holds. -/
example : Holds ⟨[7], 2⟩ ⟨7, 2⟩ :=
  findCap_sound (caps := [⟨7, 2⟩, ⟨3, 9⟩]) (by decide)

/-- Request-bound challenges are injective in the request. -/
example : bind 42 7 = 42007 := rfl

example : bind 42 7 ≠ bind 43 7 := by decide

/-! ## E-1362: accumulator -/

/-- The accumulator of 2, 3, 5. -/
example : acc [2, 3, 5] = 30 := rfl

/-- The witness for 3 is the product of the rest. -/
example : witness [2, 3, 5] 3 = 10 := rfl

/-- Witness verification for a member. -/
example : Verify (acc [2, 3, 5]) 3 (witness [2, 3, 5] 3) :=
  witness_verifies (by decide)

/-- Deleting a member divides the accumulator. -/
example : acc (remove [2, 3, 5] 3) * 3 = acc [2, 3, 5] :=
  acc_delete (by decide)

/-- Deleting a non-member changes nothing. -/
example : acc (remove [2, 3, 5] 7) = acc [2, 3, 5] :=
  acc_remove_not_mem (by decide)

/-! ## E-1363: attribute policies -/

/-- A read policy: read at least 1. -/
def readPolicy : Policy := [⟨0, 1⟩]

/-- A reader passes. -/
example : allows readPolicy ⟨1, 0, 0⟩ = true := by decide

/-- A guest does not. -/
example : allows readPolicy ⟨0, 0, 0⟩ = false := by decide

/-- A high-clearance admin policy. -/
def adminPolicy : Policy := [⟨2, 5⟩]

/-- The ceiling blocks the escalation: no capped principal satisfies it. -/
example : ¬ Satisfies adminPolicy ⟨3, 0, 4⟩ := by
  intro h
  have h2 := h ⟨2, 5⟩ (by simp [adminPolicy])
  simp only [Constraint.ok, Attrs.get] at h2
  omega

/-! ## E-1364: revocation -/

/-- Revoking invalidates the witness. -/
example : ¬ (revoke ⟨4, [7]⟩ 22).valid 22 5 :=
  revoke_invalidates ⟨4, [7]⟩ 22

/-- The epoch advances. -/
example : (revoke ⟨4, [7]⟩ 22).epoch = 5 := rfl

/-- An unaffected identifier stays valid at the new epoch. -/
example : (revoke ⟨4, [7]⟩ 22).valid 99 5 :=
  revoke_preserves (s := ⟨4, [7]⟩) (id := 22) (y := 99) (by decide) (by decide)

/-- A stale witness is rejected. -/
example : ¬ (revoke ⟨4, [7]⟩ 22).valid 99 4 :=
  stale_witness_rejected (s := ⟨4, [7]⟩) (id := 22) (y := 99) (wEpoch := 4)
    (by decide)

/-! ## E-1365: signature chains -/

/-- A digest from the empty accumulator. -/
example : foldSig 0 [7, 9] = 226 := by decide

/-- Delegating re-signs locally. -/
example : Verifies ((delegate 226 [7, 9] 3).1) ((delegate 226 [7, 9] 3).2) :=
  delegate_preserves (show digest [7, 9] = 226 from by simp [digest, foldSig]) 3

/-- A tampered hop changes the digest. -/
example : digest [10, 9] ≠ digest [7, 9] :=
  tamper_detected (h := 10) (h' := 7) (hs := [9]) (by decide)

/-- Chains grow by one per delegation. -/
example : (delegate 226 [7, 9] 3).2.length = 3 :=
  delegate_length 226 3 [7, 9]

/-! ## E-1366: tokens and nonces -/

/-- Tags separate origins for the same user. -/
example : issueTag 5 1 200 ≠ issueTag 5 2 200 :=
  issueTag_origin_separates (by decide) (by decide) (by decide)

/-- The tag packs key, origin and user. -/
example : issueTag 5 1 200 = 5001200 := by decide

/-- A fresh nonce is consumed and replayed once. -/
example : spend [1] 2 = some [2, 1] := by decide

/-- Replays are refused. -/
example : spend [1, 2] 2 = none := by decide

/-! ## E-1367: proof-carrying tokens -/

/-- The policy context says token A is an admin token. -/
def ctxA : List Form := [.atom 1]

/-- A hypothesis proof checks. -/
example : check ctxA (.hyp 0) (.atom 1) = true := by decide

/-- Soundness: the accepted proof really derives the claim. -/
example : Derives ctxA (.atom 1) :=
  check_sound (p := .hyp 0) (show check ctxA (.hyp 0) (.atom 1) = true from by decide)

/-- Conjunction introduction checks. -/
example : check ctxA (.andIntro (.hyp 0) (.hyp 0))
    (.and (.atom 1) (.atom 1)) = true := by decide

/-- A claim about a different token does not check. -/
example : check ctxA (.hyp 0) (.atom 2) = false := by decide

/-- Modus ponens through a token policy. -/
def ctxB : List Form := [.imp (.atom 1) (.atom 2), .atom 1]

example : check ctxB (.impElim (.atom 1) (.hyp 0) (.hyp 1)) (.atom 2) = true :=
  by decide

example : Derives ctxB (.atom 2) :=
  check_sound (show check ctxB (.impElim (.atom 1) (.hyp 0) (.hyp 1)) (.atom 2)
    = true from by decide)

/-! ## E-1368: sharing -/

/-- Splitting 42 between two participants. -/
example : share 42 [10, 5] = [10, 5, 27] := rfl

/-- Reconstruction recovers the secret. -/
example : combine (share 42 [10, 5]) = 42 :=
  combine_share [10, 5] 42

/-- Two shares are not enough for free: the third is determined as 30. -/
example : combine [4, 8, 30] = 42 := by decide

/-- Any two shares are consistent with any secret: 12 and 8 hide both 42 and 7. -/
example : combine ((42 - combine [12, 8]) :: [12, 8]) = 42 :=
  remaining_hides [12, 8] 42

example : combine ((7 - combine [12, 8]) :: [12, 8]) = 7 :=
  remaining_hides [12, 8] 7

/-- A lost device is replaced with a rotated share. -/
example : combine (3 :: (42 - 3 - combine [12, 8]) :: [12, 8]) = 42 :=
  rotate_preserves 3 42 [12, 8]

/-! ## E-1369: blinding -/

/-- Blinding with 100 and signing with key 7, then unblinding. -/
example : unblind (signMsg (blind 5 100) 7) 100 = signMsg 5 7 :=
  unblind_sign 5 100 7

/-- The signer's view of blinded 5 is consistent with every plaintext. -/
example : ∃ b, blind 9 b = 105 := view_consistent 105 9

/-- Distinct blinders blind the same message differently. -/
example : blind 5 100 ≠ blind 5 101 := by decide

/-! ## E-1370: PUF comparison -/

/-- One error in four bits. -/
example : mismatches [true, false, true, true] [true, true, true, true] = 1 :=
  rfl

/-- Exact responses are accepted at threshold zero. -/
example : accept 0 [true, false] [true, false] = true := by decide

/-- One error is accepted at threshold one. -/
example : accept 1 [true, false] [false, false] = true := by decide

/-- One error is rejected at threshold zero. -/
example : accept 0 [true, false] [false, false] = false := by decide

/-- The constant-time scan costs the length, always. -/
example : ctSteps 4 = 4 := rfl

/-- The early exit does not: it stops at the first mismatch on a secret. -/
example : earlySteps [true, false] [false, false] = 1 := rfl

example : earlySteps [false, false] [false, false] = 2 := rfl

end Morph.Specs.AuthIdentity
