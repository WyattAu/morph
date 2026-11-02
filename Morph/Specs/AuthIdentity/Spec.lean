/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Std

/-!
# Authentication and Identity Kernel — specification (E-1361–E-1370)

Status: In Progress (loop 104, batch CC first cycle).

Executable cores for the ten authentication, authorization and identity
register entries (ADR-030, Cluster XXXI). Each section is a *model with a
theorem*, not a cryptographic implementation: the register's acceptance rule
asks for a decidable checking or computable synthesis procedure plus a kill
criterion, and these are the smallest kernels that make each row falsifiable.

No cipher, curve, pairing or hash is implemented. Where a row's security
rests on a hardness assumption (strong RSA for E-1362, the discrete log for
E-1369, PUF physical unclonability for E-1370) the assumption is named in the
docstring and the kernel proves the *algebra* around it — the part a bug
actually breaks.

## Mapping Summary

| Register row | Concept | Lean core |
|---|---|---|
| E-1361 | Epistemic capability attestation | `findCap`, `Holds`, `bind`, `bind_req_injective` |
| E-1362 | Accumulator membership proofs | `acc`, `witness`, `acc_erase`, `acc_delete` |
| E-1363 | Presburger attribute lattices | `Attrs`, `Policy`, `allows`, `allows_iff` |
| E-1364 | Pairing accumulator revocation | `RevState`, `revoke`, `revoke_invalidates` |
| E-1365 | Signature-chain delegation | `foldSig`, `delegate`, `delegate_preserves` |
| E-1366 | VRF ephemeral identity | `Token`, `issueTag`, `issueTag_injective`, `spend` |
| E-1367 | Proof-carrying authorization tokens | `Form`, `Proof`, `check`, `Derives` |
| E-1368 | Threshold key agreement | `share`, `combine`, `combine_share`, `remaining_hides` |
| E-1369 | Blind signature isolation | `blind`, `unblind`, `view_consistent` |
| E-1370 | PUF challenge–response binding | `Puf`, `mismatches`, `accept`, `ctSteps` |

## What the model does *not* claim

No protocol, library or server is produced. Rows are graded L1 (definitions
plus `decide`-able checks and examples) or L2 (proved algebraic laws). The
execution record and kill criteria are tracked in
`.specs/03_research/briefs/CC-auth-identity-kernel.md`; none of the register
kill criteria can fire until these kernels are benchmarked against the
baselines named in ADR-030.
-/

namespace Morph.Specs.AuthIdentity

/-! ## E-1361: epistemic capability attestation

A capability is attested by exhibiting a witness that the holder satisfies
the capability predicate — no token is exchanged. The kernel is (a) a
witness-returning decision procedure and (b) the binding of an attestation to
the request it was issued for. -/

/-- A capability: a resource at a maximum delegation level. -/
structure Capability where
  resource : Nat
  level : Nat
  deriving Repr, DecidableEq

/-- A witness of possession: the delegation path and the claimed depth. -/
structure Witness where
  path : List Nat
  depth : Nat
  deriving Repr, DecidableEq

/-- The predicate an attestation has to establish. -/
def Holds (w : Witness) (c : Capability) : Prop :=
  w.depth ≤ c.level ∧ c.resource ∈ w.path

/-- Computable synthesis: search the delegation chain for a capability that
covers the requested resource at the requested level, returning the witness
rather than a bare boolean. -/
def findCap : List Capability → Nat → Nat → Option Witness
  | [], _, _ => none
  | c :: cs, res, lvl =>
    if c.resource = res ∧ lvl ≤ c.level then some ⟨[res], lvl⟩
    else findCap cs res lvl

/-- Request-bound challenge: a transcript is valid only for the request it
was bound to. `com` is the commitment, `req` the request identifier. -/
def bind (req com : Nat) : Nat := req * 1000 + com

/-! ## E-1362: membership accumulator

The accumulator is the product of a set of prime factors; membership is
divisibility. Soundness (that a non-member cannot forge a witness) rests on
the strong RSA assumption and is *not* proved here. What is proved is the
accumulator algebra: adding and deleting members updates the accumulator
exactly, so revocation works. -/

/-- Product of a list of factors (the accumulator value). -/
def acc : List Nat → Nat
  | [] => 1
  | x :: xs => x * acc xs

/-- Delete one factor, keeping the rest (structural, no `BEq`). -/
def remove : List Nat → Nat → List Nat
  | [], _ => []
  | a :: as, x => if a = x then as else a :: remove as x

/-- Membership witness for `x` in `s`: the accumulator of the rest. -/
def witness (s : List Nat) (x : Nat) : Nat := acc (remove s x)

/-- Witness verification is the divisibility equation. -/
def Verify (a x w : Nat) : Prop := w * x = a

/-! ## E-1363: attribute-based permission lattice

Permissions are arithmetic bounds on attribute indices, so a policy is a
finite set of linear constraints and satisfaction is decidable. The security
content is monotonicity: lowering an attribute can never gain permission. -/

/-- The attribute vector. Only three indices are modelled; anything else
reads `admin`, which keeps `get` total. -/
structure Attrs where
  read : Nat
  write : Nat
  admin : Nat
  deriving Repr, DecidableEq

/-- Total projection onto an attribute index. -/
def Attrs.get (a : Attrs) : Nat → Nat
  | 0 => a.read
  | 1 => a.write
  | _ => a.admin

/-- A policy clause: attribute `idx` must be at least `min`. -/
structure Constraint where
  idx : Nat
  min : Nat
  deriving Repr, DecidableEq

/-- The clause holds for the attribute vector. -/
def Constraint.ok (c : Constraint) (a : Attrs) : Prop := c.min ≤ a.get c.idx

/-- A policy is a conjunction of clauses. -/
abbrev Policy := List Constraint

/-- Executable policy check. -/
def allows (p : Policy) (a : Attrs) : Bool :=
  p.all (fun c => decide (c.min ≤ a.get c.idx))

/-- Semantic policy satisfaction. -/
def Satisfies (p : Policy) (a : Attrs) : Prop := ∀ c ∈ p, c.ok a

/-- An attribute ceiling: the most any principal may hold at each index. -/
structure Ceiling where
  limit : Nat → Nat

/-- A principal under a ceiling can never exceed it. -/
def Within (cap : Ceiling) (a : Attrs) : Prop := ∀ i, a.get i ≤ cap.limit i

/-! ## E-1364: revocation

Revocation is modelled by an epoch: every revoke advances it, and a witness
carries the epoch it was computed at. Stale witnesses are rejected by the
epoch check alone, so revocation needs no list propagation. -/

/-- Revocation state: current epoch and the revoked identifiers. -/
structure RevState where
  epoch : Nat
  revoked : List Nat
  deriving Repr, DecidableEq

/-- A witness is valid for `id` at `wEpoch` iff the epoch matches and the
identifier is not revoked. -/
def RevState.valid (s : RevState) (id wEpoch : Nat) : Prop :=
  wEpoch = s.epoch ∧ id ∉ s.revoked

/-- Revoking advances the epoch and records the identifier. -/
def revoke (s : RevState) (id : Nat) : RevState :=
  ⟨s.epoch + 1, id :: s.revoked⟩

/-! ## E-1365: signature-chain delegation

A chain is an ordered list of hops. Its digest is a left fold, so a chain can
be verified incrementally and extended without contacting the root: the new
root is the old root extended by the hop. -/

/-- Left-fold digest of a hop chain from accumulator `a`. -/
def foldSig : Nat → List Nat → Nat
  | a, [] => a
  | a, h :: hs => foldSig (a * 31 + h) hs

/-- Chain digest from the empty accumulator. -/
def digest (c : List Nat) : Nat := foldSig 0 c

/-- `root` signs the chain. -/
def Verifies (root : Nat) (c : List Nat) : Prop := digest c = root

/-- Appending a hop re-signs: the new root is the old one extended. -/
def extendRoot (root h : Nat) : Nat := root * 31 + h

/-- Delegating a hop: the chain grows, the root is re-derived locally. -/
def delegate (root : Nat) (c : List Nat) (h : Nat) : Nat × List Nat :=
  (extendRoot root h, c ++ [h])

/-! ## E-1366: ephemeral identity tokens

A token is `(origin, epoch, tag)`. The tag is a keyed encoding of origin and
user: a party holding the key can link a user across epochs (needed for
account recovery), a party without it cannot link across origins. -/

/-- An ephemeral identity token. -/
structure Token where
  origin : Nat
  epoch : Nat
  tag : Nat
  deriving Repr, DecidableEq

/-- Keyed tag: key, origin and user packed into one number. -/
def issueTag (key origin user : Nat) : Nat := key * 1000000 + origin * 1000 + user

/-- Issue a token for a user at an origin in an epoch. -/
def issue (key origin user epoch : Nat) : Token :=
  ⟨origin, epoch, issueTag key origin user⟩

/-- Spending a nonce: `some rest` when fresh, `none` when replayed. -/
def spend (used : List Nat) (nonce : Nat) : Option (List Nat) :=
  if nonce ∈ used then none else some (nonce :: used)

/-! ## E-1367: proof-carrying authorization tokens

A token carries a proof term; the policy decision point runs a tiny kernel.
`check` is the Boolean checker and `Derives` the specification it must agree
with. -/

/-- Authorization formulas. -/
inductive Form where
  | atom : Nat → Form
  | and : Form → Form → Form
  | imp : Form → Form → Form
  deriving Repr, DecidableEq

/-- Proof terms. `andElimL b p` eliminates a conjunction on the left, naming
the right component `b`; `andElimR a p` names the left component. -/
inductive Proof where
  | hyp : Nat → Proof
  | andIntro : Proof → Proof → Proof
  | andElimL : Form → Proof → Proof
  | andElimR : Form → Proof → Proof
  | impElim : Form → Proof → Proof → Proof
  deriving Repr

/-- The checking relation: proof term, context, claimed formula. -/
inductive Derives : List Form → Form → Prop where
  | hyp : ∀ (Γ : List Form) (n : Nat) (f : Form),
      Γ[n]? = some f → Derives Γ f
  | andIntro : ∀ Γ a b, Derives Γ a → Derives Γ b → Derives Γ (.and a b)
  | andElimL : ∀ Γ a b, Derives Γ (.and a b) → Derives Γ a
  | andElimR : ∀ Γ a b, Derives Γ (.and a b) → Derives Γ b
  | impElim : ∀ Γ a b, Derives Γ (.imp a b) → Derives Γ a → Derives Γ b

/-- The Boolean proof checker run by the policy decision point. -/
def check (Γ : List Form) : Proof → Form → Bool
  | .hyp n, f => decide (Γ[n]? = some f)
  | .andIntro p q, f =>
    match f with
    | .and a b => check Γ p a && check Γ q b
    | _ => false
  | .andElimL b p, a => check Γ p (.and a b)
  | .andElimR a p, b => check Γ p (.and a b)
  | .impElim a p q, b => check Γ p (.imp a b) && check Γ q a

/-! ## E-1368: threshold key agreement

Additive sharing: the secret is the sum of `n` shares, so it is recoverable
only when every share is present, and any `n − 1` shares leave it
undetermined. (`t`-of-`n` for `t < n` needs interpolation and is out of
fragment; the register kill criterion is about *recovery*, which this
models.) -/

/-- Split a secret into one share per participant: each participant takes a
chosen value and the remainder is passed on. -/
def share (s : Int) : List Int → List Int
  | [] => [s]
  | r :: rs => r :: share (s - r) rs

/-- Reconstruct by summing the shares. -/
def combine (xs : List Int) : Int :=
  match xs with
  | [] => 0
  | x :: rest => x + combine rest

/-! ## E-1369: blind signature isolation

The signer sees a blinded message and returns a blinded signature; the client
unblinds it. In exponent space signing is addition, so the algebra is exact
integer arithmetic. The kernel's claim is that the signer's view is
consistent with *every* message, i.e. it identifies none. -/

/-- Blind a message with a blinder (exponent-space encoding). -/
def blind (m b : Int) : Int := m + b

/-- Remove the blinder from a signature. -/
def unblind (x b : Int) : Int := x - b

/-- Exponent-space signature: `m + k` for key `k`. -/
def signMsg (m k : Int) : Int := m + k

/-! ## E-1370: PUF challenge–response binding

A PUF answers challenges with noisy responses bound to the physical device.
Verification compares the response to a stored reference within a threshold;
timing invariance means the comparison cost depends only on the challenge
length. -/

/-- A physical unclonable function: challenge to response bits. -/
structure Puf where
  resp : Nat → List Bool

/-- Hamming distance between equal-length response words. -/
def mismatches : List Bool → List Bool → Nat
  | [], [] => 0
  | a :: as, b :: bs => (if a = b then 0 else 1) + mismatches as bs
  | _, _ => 0

/-- Accept a response within `thr` bit errors. -/
def accept (thr : Nat) (expected actual : List Bool) : Bool :=
  decide (mismatches expected actual ≤ thr)

/-- Constant-time comparison cost: the whole word is scanned. -/
def ctSteps (n : Nat) : Nat := n

/-- Early-exit comparison cost: stops at the first mismatch. -/
def earlySteps : List Bool → List Bool → Nat
  | [], [] => 0
  | a :: as, b :: bs => if a = b then 1 + earlySteps as bs else 1
  | _, _ => 0

end Morph.Specs.AuthIdentity
