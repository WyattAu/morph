/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Specs.BatchP5.Examples

/-!
# Feasible-50 kernels — P5 validation

Status: first cycle complete (loop 110).

Second, independent pass over the ten cores. `Examples.lean` demonstrates the
definitions; this file replays them as *checks*: each theorem is applied to a
fresh instance, negative cases are asserted, and the multi-step laws
(single execution, meet admission, cursor accounting) are exercised where a
single example could pass by accident.

Run: `lake build Morph.Tests.BatchP5`.
-/

namespace Morph.Tests.BatchP5

open Morph.Specs.BatchP5

/-! ## E-1455: tokens on fresh ledgers -/

/-- A fresh token executes. -/
example : invoke [3] 4 = some [4, 3] :=
  invoke_fresh [3] 4 (by decide)

/-- A fresh redelivery is refused. -/
example : invoke [3, 4] 3 = none :=
  invoke_dup [3, 4] 3 (by decide)

/-- A fresh execution records. -/
example : 4 ∈ [4, 3] :=
  invoke_records [3] 4 [4, 3] rfl

/-! ## E-1460: rules on fresh windows -/

/-- A fresh in-bounds request passes. -/
example : admitR ⟨0, 10⟩ 7 = true :=
  admitR_complete ⟨0, 10⟩ 7 (by decide)

/-- A fresh meet admits jointly. -/
example : admitR ⟨0, 10⟩ 7 = true ∧ admitR ⟨5, 12⟩ 7 = true :=
  meet_sound ⟨0, 10⟩ ⟨5, 12⟩ 7 (by decide)

/-- A fresh out-of-bounds request fails. -/
example : admitR ⟨0, 10⟩ 11 = false := by decide

/-! ## E-1463: duality on fresh ends -/

/-- A fresh end matches its dual. -/
example : matchC ⟨3, 8⟩ ⟨8, 3⟩ = true :=
  match_self ⟨3, 8⟩

/-- A fresh mismatch fails. -/
example : matchC ⟨3, 8⟩ ⟨8, 4⟩ = false := by decide

/-- A fresh match names the duality. -/
example : (⟨8, 3⟩ : ChanEnd).id = (⟨3, 8⟩ : ChanEnd).dual :=
  (match_sound _ _ (by decide)).1

/-! ## E-1468: order on fresh boxes -/

/-- A fresh expected message advances. -/
example : receive ⟨9, 10⟩ 10 = some ⟨10, 11⟩ :=
  receive_ok ⟨9, 10⟩

/-- A fresh replay is rejected. -/
example : receive ⟨9, 10⟩ 9 = none :=
  receive_reject ⟨9, 10⟩ 9 (by decide)

/-! ## E-1469: cursors on fresh rings -/

/-- A fresh produce buffers one more. -/
example : used (push ⟨1, 4⟩) = used ⟨1, 4⟩ + 1 :=
  push_used ⟨1, 4⟩ (by decide)

/-- A fresh consume frees one. -/
example : used (pop ⟨1, 4⟩) + 1 = used ⟨1, 4⟩ :=
  pop_used ⟨1, 4⟩ (by decide)

/-- A fresh push-pop nets zero. -/
example : used (pop (push ⟨1, 4⟩)) = used ⟨1, 4⟩ :=
  push_pop ⟨1, 4⟩ (by decide)

/-! ## E-1470: signals on fresh nodes -/

/-- A fresh combination covers the stamp. -/
example : (⟨1, 2⟩ : Sig).stamp ≤ (combine ⟨1, 2⟩ ⟨3, 4⟩).stamp :=
  combine_stamp_l _ _

/-- A fresh evaluation splits. -/
example : evalOnce ([⟨1, 2⟩, ⟨3, 4⟩] ++ [⟨5, 6⟩]) =
    evalOnce [⟨1, 2⟩, ⟨3, 4⟩] + evalOnce [⟨5, 6⟩] :=
  evalOnce_append _ _

/-! ## E-1484: lists on fresh permissions -/

/-- A fresh denied permission is refused. -/
example : denyCheck [11] 11 = false :=
  deny_banned [11] 11 (by decide)

/-- A fresh clear permission passes. -/
example : denyCheck [11] 2 = true :=
  deny_ok [11] 2 (by decide)

/-! ## E-1487: capabilities on fresh perms -/

/-- A fresh grant is live. -/
example : useC (grant 9) = true := use_grant 9

/-- A fresh revocation kills. -/
example : useC (revoke (grant 9)) = false :=
  revoke_dead _

/-- A fresh label survives. -/
example : (revoke (grant 9)).perm = 9 :=
  revoke_perm _

/-! ## E-1489: restore on fresh states -/

/-- A fresh restore installs. -/
example : restoreA ⟨0, 0⟩ ⟨5, 6⟩ = ⟨5, 6⟩ :=
  restore_snap _ _

/-- A fresh rotation keeps data. -/
example : (rotate ⟨5, 6⟩).dat = 6 :=
  rotate_data _

/-! ## E-1490: links on fresh states -/

/-- A fresh advertising timeout falls back. -/
example : bstep .advertising .timeout = some .idle :=
  bstep_timeout_adv

/-- A fresh drop returns to idle. -/
example : bstep .connected .drop = some .idle :=
  bstep_drop

/-- A fresh connected timeout holds. -/
example : bstep .connected .timeout = some .connected :=
  bstep_timeout_conn

end Morph.Tests.BatchP5
