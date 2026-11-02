/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Morph.Specs.AuthIdentity.Spec

/-!
# Authentication and Identity Kernel — lemmas (E-1361–E-1370)

Status: In Progress (loop 104, batch CC first cycle).

Every theorem here is about the computable core in `Spec.lean`. Where a row
depends on a hardness assumption the docstring says so and only the algebra
is proved; see the module header of `Spec.lean`.
-/

namespace Morph.Specs.AuthIdentity

/-! ## E-1361: attestation soundness, completeness, and request binding -/

/-- Any witness returned by the search really establishes the capability. -/
theorem findCap_sound {caps : List Capability} {res lvl : Nat} {w : Witness}
    (h : findCap caps res lvl = some w) : Holds w ⟨res, lvl⟩ := by
  induction caps generalizing w with
  | nil => simp [findCap] at h
  | cons c cs ih =>
    simp only [findCap] at h
    split at h
    · rename_i hcond
      injection h with hw
      subst hw
      exact ⟨Nat.le_refl _, by simp⟩
    · exact ih h

/-- If the chain contains a covering capability, the search finds a witness. -/
theorem findCap_complete {caps : List Capability} {res lvl : Nat}
    (h : ∃ c ∈ caps, c.resource = res ∧ lvl ≤ c.level) :
    ∃ w, findCap caps res lvl = some w := by
  induction caps with
  | nil => simp at h
  | cons c cs ih =>
    simp only [findCap]
    split
    · exact ⟨_, rfl⟩
    · rename_i hno
      rcases h with ⟨d, hd, hres, hlev⟩
      simp only [List.mem_cons] at hd
      rcases hd with rfl | hd
      · exact absurd ⟨hres, hlev⟩ hno
      · exact ih ⟨d, hd, hres, hlev⟩

/-- An attestation is bound to the request: the transcript cannot be replayed
against a different request. -/
theorem bind_req_injective {com r r' : Nat} (h : bind r com = bind r' com) :
    r = r' := by
  unfold bind at h
  omega

/-! ## E-1362: accumulator algebra and revocation -/

/-- Delation of a member divides the accumulator by it. -/
theorem acc_delete {s : List Nat} {x : Nat} (h : x ∈ s) :
    acc (remove s x) * x = acc s := by
  induction s with
  | nil => simp at h
  | cons a as ih =>
    unfold remove
    split
    · rename_i heq
      subst heq
      simp only [acc]
      exact Nat.mul_comm _ _
    · rename_i hne
      have hmem : x ∈ as := by
        simp only [List.mem_cons] at h
        exact h.resolve_left (by intro he; exact hne he.symm)
      simp only [acc]
      rw [Nat.mul_assoc, ih hmem]

/-- Witness verification for a member. -/
theorem witness_verifies {s : List Nat} {x : Nat} (h : x ∈ s) :
    Verify (acc s) x (witness s x) :=
  acc_delete h

/-- Deleting a non-member is a no-op on the accumulator. -/
theorem acc_remove_not_mem {s : List Nat} {x : Nat} (h : x ∉ s) :
    acc (remove s x) = acc s := by
  induction s with
  | nil => simp [remove, acc]
  | cons a as ih =>
    have hmem : x ∉ as := by
      intro hin; exact h (by simp [hin])
    unfold remove
    split
    · rename_i heq
      exact absurd (by simp [heq]) h
    · rename_i hne
      simp only [acc]
      rw [ih hmem]

/-! ## E-1363: attribute lattice monotonicity and escalation blocking -/

/-- The executable check agrees with the semantic policy. -/
theorem allows_iff {p : Policy} {a : Attrs} : allows p a = true ↔ Satisfies p a := by
  unfold allows Satisfies Constraint.ok
  rw [List.all_eq_true]
  constructor
  · intro h c hc
    have := h c hc
    simpa using this
  · intro h c hc
    simpa using h c hc

/-- Raising an attribute can never lose a permission: the lattice order is
monotone in the grant direction. -/
theorem raising_never_loses {p : Policy} {a b : Attrs} (ha : Satisfies p a)
    (hle : ∀ i, a.get i ≤ b.get i) : Satisfies p b := by
  intro c hc
  have h2 := ha c hc
  have h3 := hle c.idx
  unfold Constraint.ok at h2 ⊢
  omega

/-- A principal confined by a ceiling can never satisfy a policy clause above
that ceiling: this is the escalation case an IDOR/IAM bug gets wrong. -/
theorem ceiling_blocks_escalation {p : Policy} {cap : Ceiling} {a : Attrs}
    (hbad : ∃ c ∈ p, cap.limit c.idx < c.min) (hw : Within cap a) :
    ¬ Satisfies p a := by
  rintro hs
  obtain ⟨c, hc, hgt⟩ := hbad
  have h1 := hs c hc
  have h2 := hw c.idx
  unfold Constraint.ok at h1
  omega

/-! ## E-1364: revocation algebra -/

/-- A revoked identifier fails verification at the new epoch. -/
theorem revoke_invalidates (s : RevState) (id : Nat) :
    ¬ (revoke s id).valid id (s.epoch + 1) := by
  intro h
  exact h.2 (List.mem_cons_self ..)

/-- Revocation strictly advances the epoch. -/
theorem revoke_epoch_increases (s : RevState) (id : Nat) :
    s.epoch < (revoke s id).epoch :=
  Nat.lt_succ_self _

/-- Every other witness remains valid at the new epoch. -/
theorem revoke_preserves (s : RevState) {id y : Nat}
    (hne : id ≠ y) (hok : y ∉ s.revoked) :
    (revoke s id).valid y (s.epoch + 1) := by
  refine ⟨rfl, ?_⟩
  intro hmem
  rcases List.mem_cons.mp hmem with heq | hin
  · exact hne heq.symm
  · exact hok hin

/-- A witness carrying an old epoch is rejected without consulting the list. -/
theorem stale_witness_rejected (s : RevState) {id y wEpoch : Nat}
    (hstale : wEpoch ≠ (revoke s id).epoch) :
    ¬ (revoke s id).valid y wEpoch := by
  intro h
  exact hstale h.1

/-! ## E-1365: signature-chain delegation -/

/-- The digest fold is injective in its starting accumulator. -/
theorem foldSig_inj : ∀ (l : List Nat) {a a' : Nat},
    foldSig a l = foldSig a' l → a = a' := by
  intro l
  induction l with
  | nil =>
    intro a a' h
    simpa [foldSig] using h
  | cons hd tl ih =>
    intro a a' h
    simp only [foldSig] at h
    have := ih h
    omega

/-- The fold over a concatenation. -/
theorem foldSig_append : ∀ (l₁ l₂ : List Nat) (a : Nat),
    foldSig a (l₁ ++ l₂) = foldSig (foldSig a l₁) l₂ := by
  intro l₁
  induction l₁ with
  | nil => intro l₂ a; simp [foldSig]
  | cons hd tl ih =>
    intro l₂ a
    simp only [List.cons_append, foldSig]
    exact ih l₂ (a * 31 + hd)

/-- Digest of a concatenation. -/
theorem digest_append (l₁ l₂ : List Nat) :
    digest (l₁ ++ l₂) = foldSig (digest l₁) l₂ :=
  foldSig_append l₁ l₂ 0

/-- Delegating a hop keeps the chain verifiable against the locally derived
root, with no round-trip to the original signer. -/
theorem delegate_preserves {root : Nat} {c : List Nat} (h : Verifies root c)
    (hop : Nat) : Verifies (delegate root c hop).1 (delegate root c hop).2 := by
  unfold Verifies at h ⊢
  simp only [delegate, extendRoot]
  rw [digest_append, h]
  simp [foldSig]

/-- Changing a hop changes the digest: the chain commits to every hop. -/
theorem tamper_detected {h h' : Nat} {hs : List Nat} (hne : h ≠ h') :
    digest (h :: hs) ≠ digest (h' :: hs) := by
  intro heq
  unfold digest at heq
  have := foldSig_inj hs heq
  omega

/-- Delegation increases the chain length by exactly one. -/
theorem delegate_length (root hop : Nat) (c : List Nat) :
    (delegate root c hop).2.length = c.length + 1 := by
  simp [delegate]

/-! ## E-1366: token tags and nonce spending -/

/-- The keyed tag is injective on a small origin/user domain: a key holder
can identify a user, which is exactly the recovery requirement. -/
theorem issueTag_injective {key o o' u u' : Nat}
    (hu : u < 1000) (hu' : u' < 1000)
    (h : issueTag key o u = issueTag key o' u') : o = o' ∧ u = u' := by
  unfold issueTag at h
  omega

/-- Origins are separated: the same user at two origins gets distinct tags, so
an authenticator without the key cannot link the sessions. -/
theorem issueTag_origin_separates {key o o' u u' : Nat}
    (hu : u < 1000) (hu' : u' < 1000) (hne : o ≠ o') :
    issueTag key o u ≠ issueTag key o' u' := by
  intro h
  exact hne (issueTag_injective hu hu' h).1

/-- A fresh nonce is consumed. -/
theorem spend_fresh {used : List Nat} {nonce : Nat} (h : nonce ∉ used) :
    spend used nonce = some (nonce :: used) := by
  simp [spend, h]

/-- A replayed nonce is refused. -/
theorem spend_replay {used : List Nat} {nonce : Nat} (h : nonce ∈ used) :
    spend used nonce = none := by
  simp [spend, h]

/-- Spending records the nonce and drops nothing. -/
theorem spend_sound {used : List Nat} {nonce : Nat} {rest : List Nat}
    (h : spend used nonce = some rest) :
    nonce ∈ rest ∧ ∀ m ∈ used, m ∈ rest := by
  unfold spend at h
  split at h
  · exact absurd h (by simp)
  · rename_i hfresh
    injection h with hrest
    subst hrest
    exact ⟨by simp, by intro m hm; simp [hm]⟩

/-! ## E-1367: proof-checker soundness -/

/-- The Boolean checker only accepts derivable claims: a policy decision made
by `check` is backed by a derivation. -/
theorem check_sound {Γ : List Form} {f : Form} {p : Proof}
    (h : check Γ p f = true) : Derives Γ f := by
  induction p generalizing f with
  | hyp n =>
    simp only [check] at h
    exact Derives.hyp Γ n f (of_decide_eq_true h)
  | andIntro a b iha ihb =>
    simp only [check] at h
    split at h
    · rename_i fa fb
      rw [Bool.and_eq_true] at h
      exact Derives.andIntro Γ _ _ (iha h.1) (ihb h.2)
    · exact absurd h (by simp)
  | andElimL b p ih =>
    simp only [check] at h
    exact Derives.andElimL Γ _ b (ih h)
  | andElimR a p ih =>
    simp only [check] at h
    exact Derives.andElimR Γ a _ (ih h)
  | impElim a p q ihp ihq =>
    simp only [check] at h
    rw [Bool.and_eq_true] at h
    exact Derives.impElim Γ a _ (ihp h.1) (ihq h.2)

/-! ## E-1368: additive secret sharing -/

/-- Reconstruction from all shares recovers the secret. -/
theorem combine_share : ∀ (rs : List Int) (s : Int), combine (share s rs) = s
  | [], s => by simp [share, combine]
  | r :: rs, s => by
    have ih := combine_share rs (s - r)
    simp only [share, combine] at ih ⊢
    omega

/-- With all but one share, the remaining share is determined: it is the
difference between the secret and the sum of the others. -/
theorem last_share_determined {r s : Int} {rs : List Int}
    (h : combine (r :: rs) = s) : r = s - combine rs := by
  simp only [combine] at h
  omega

/-- Conversely, any `n − 1` shares are consistent with *every* secret: they
determine nothing. This is the information-theoretic statement in algebraic
form, and it is why the threshold is `n`. -/
theorem remaining_hides (rs : List Int) (s' : Int) :
    combine ((s' - combine rs) :: rs) = s' := by
  simp only [combine]
  omega

/-- A lost device can be replaced: rotating one share to a new value keeps the
secret reconstructible, as long as the replacement is derived from the target
secret and the other shares. -/
theorem rotate_preserves (r' s : Int) (rs : List Int) :
    combine (r' :: (s - r' - combine rs) :: rs) = s := by
  simp only [combine]
  omega

/-! ## E-1369: blinding -/

/-- Unblinding a blinded signature yields the signature on the plaintext. -/
theorem unblind_sign (m b k : Int) :
    unblind (signMsg (blind m b) k) b = signMsg m k := by
  simp [unblind, signMsg, blind]
  omega

/-- Blinding then unblinding is the identity. -/
theorem unblind_blind (m b : Int) : unblind (blind m b) b = m := by
  simp [unblind, blind]

/-- The signer's view is consistent with every message: for any observed
blinded value and any candidate plaintext there is a blinder explaining it.
The authenticator therefore learns nothing about which tenant or identity it
signed. -/
theorem view_consistent (v m : Int) : ∃ b, blind m b = v :=
  ⟨v - m, by simp [blind]; omega⟩

/-- Distinct blinders give distinct views: the client's randomness is what
hides the message. -/
theorem blind_injective {m b b' : Int} (h : b ≠ b') : blind m b ≠ blind m b' := by
  intro heq
  simp [blind] at heq
  omega

/-! ## E-1370: PUF response comparison -/

/-- An exact response has zero mismatches. -/
theorem mismatches_refl : ∀ l : List Bool, mismatches l l = 0
  | [] => rfl
  | _ :: as => by simp [mismatches, mismatches_refl as]

/-- Mismatch counting is symmetric. -/
theorem mismatches_comm : ∀ (a b : List Bool), mismatches a b = mismatches b a := by
  intro a
  induction a with
  | nil =>
    intro b
    cases b <;> rfl
  | cons x xs ih =>
    intro b
    cases b with
    | nil => rfl
    | cons y ys =>
      simp only [mismatches]
      rw [ih ys]
      by_cases hxy : x = y
      · subst hxy; simp
      · simp [hxy, Ne.symm hxy]

/-- Mismatches never exceed the word length. -/
theorem mismatches_le : ∀ (a b : List Bool), mismatches a b ≤ a.length := by
  intro a
  induction a with
  | nil => intro b; cases b <;> simp [mismatches]
  | cons x xs ih =>
    intro b
    cases b with
    | nil => simp [mismatches]
    | cons y ys =>
      have hih := ih ys
      simp only [mismatches, List.length_cons]
      split <;> omega

/-- The constant-time comparison scans the whole word whatever the content. -/
theorem ctSteps_constant (n : Nat) : ctSteps n = n := rfl

/-- The early-exit comparison does not: two secrets of the same length cost
different amounts, so its timing leaks the first mismatch position. -/
theorem earlySteps_leaks :
    earlySteps [true, true] [true, true] ≠ earlySteps [false, true] [true, true] := by
  decide

end Morph.Specs.AuthIdentity
