/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Specs.BatchP5.Lemmas

/-!
# Feasible-50 kernels — P5 examples

Status: first cycle complete (loop 110).

Concrete instances of the ten cores. Every example is `decide`/`rfl`-checked;
the law witnesses apply the lemmas of `Lemmas.lean` to fresh instances.
-/

namespace Morph.Specs.BatchP5

/-! ## E-1455: invoking once -/

/-- A fresh token executes. -/
example : invoke [1] 2 = some [2, 1] :=
  invoke_fresh [1] 2 (by decide)

/-- A consumed token is refused. -/
example : invoke [1] 1 = none :=
  invoke_dup [1] 1 (by decide)

/-- Execution records the token. -/
example : 2 ∈ [2, 1] :=
  invoke_records [1] 2 [2, 1] rfl

/-! ## E-1460: meeting rules -/

/-- In-window requests pass. -/
example : admitR ⟨2, 8⟩ 5 = true := by decide

/-- Out-of-window requests fail. -/
example : admitR ⟨2, 8⟩ 9 = false := by decide

/-- The meet admits the joint window. -/
example : admitR ⟨2, 8⟩ 5 = true ∧ admitR ⟨4, 9⟩ 5 = true :=
  meet_sound ⟨2, 8⟩ ⟨4, 9⟩ 5 (by decide)

/-! ## E-1463: matching ends -/

/-- Dualizing twice returns. -/
example : dualOf (dualOf ⟨1, 2⟩) = ⟨1, 2⟩ :=
  dual_invol _

/-- An end matches its dual. -/
example : matchC ⟨1, 2⟩ ⟨2, 1⟩ = true :=
  match_self _

/-- The match names the duality. -/
example : (⟨2, 1⟩ : ChanEnd).id = (⟨1, 2⟩ : ChanEnd).dual ∧
    (⟨2, 1⟩ : ChanEnd).dual = (⟨1, 2⟩ : ChanEnd).id :=
  match_sound _ _ (by decide)

/-! ## E-1468: receiving in order -/

/-- The expected message advances. -/
example : receive ⟨4, 5⟩ 5 = some ⟨5, 6⟩ :=
  receive_ok ⟨4, 5⟩

/-- Anything else is rejected. -/
example : receive ⟨4, 5⟩ 7 = none :=
  receive_reject ⟨4, 5⟩ 7 (by decide)

/-- The advance increments. -/
example : (⟨5, 6⟩ : Mbox).expect = (⟨4, 5⟩ : Mbox).expect + 1 :=
  receive_seq ⟨4, 5⟩ ⟨5, 6⟩ rfl

/-! ## E-1469: counting buffered items -/

/-- Producing buffers one more. -/
example : used (push ⟨2, 5⟩) = used ⟨2, 5⟩ + 1 :=
  push_used ⟨2, 5⟩ (by decide)

/-- Consuming frees one. -/
example : used (pop ⟨2, 5⟩) + 1 = used ⟨2, 5⟩ :=
  pop_used ⟨2, 5⟩ (by decide)

/-- Push then pop nets zero. -/
example : used (pop (push ⟨2, 5⟩)) = used ⟨2, 5⟩ :=
  push_pop ⟨2, 5⟩ (by decide)

/-! ## E-1470: combining signals -/

/-- Values add. -/
example : (combine ⟨3, 1⟩ ⟨4, 2⟩).val = 7 :=
  combine_val _ _

/-- Combination commutes. -/
example : combine ⟨3, 1⟩ ⟨4, 2⟩ = combine ⟨4, 2⟩ ⟨3, 1⟩ :=
  combine_comm _ _

/-- Evaluation splits. -/
example : evalOnce ([⟨3, 1⟩] ++ [⟨4, 2⟩]) = evalOnce [⟨3, 1⟩] + evalOnce [⟨4, 2⟩] :=
  evalOnce_append _ _

/-! ## E-1484: checking the list -/

/-- A denied permission is refused. -/
example : denyCheck [7, 9] 7 = false :=
  deny_banned [7, 9] 7 (by decide)

/-- Anything else passes. -/
example : denyCheck [7, 9] 3 = true :=
  deny_ok [7, 9] 3 (by decide)

/-! ## E-1487: gating use -/

/-- Grants start live. -/
example : useC (grant 4) = true := use_grant 4

/-- Revocation kills. -/
example : useC (revoke ⟨4, true⟩) = false :=
  revoke_dead _

/-- The label survives revocation. -/
example : (revoke ⟨4, true⟩).perm = 4 :=
  revoke_perm _

/-! ## E-1489: restoring -/

/-- Restore installs the snapshot. -/
example : restoreA ⟨0, 0⟩ ⟨2, 9⟩ = ⟨2, 9⟩ :=
  restore_snap _ _

/-- Snapshots keep data. -/
example : (snapA ⟨2, 9⟩).dat = 9 := snap_data _

/-- Rotation keeps data. -/
example : (rotate ⟨2, 9⟩).dat = 9 := rotate_data _

/-! ## E-1490: driving the link -/

/-- Advertising starts. -/
example : bstep .idle .startAdv = some .advertising := bstep_adv

/-- The link connects. -/
example : bstep .advertising .connect = some .connected := bstep_conn

/-- Drops return to idle. -/
example : bstep .connected .drop = some .idle := bstep_drop

/-- Connected timeouts hold. -/
example : bstep .connected .timeout = some .connected :=
  bstep_timeout_conn

/-- Idle never connects directly. -/
example : bstep .idle .connect = none := bstep_idle_conn

end Morph.Specs.BatchP5
