# Experiment Brief — Batch CC, first cycle (E-1361–E-1370)

**Status:** first cycle complete (loop 104, 2026-11-01).
**Register rows:** ADR-030, batch CC (Cluster XXXI: authentication,
authorization, identity).
**Artifact:** `Morph/Specs/AuthIdentity/{Spec,Lemmas,Examples}.lean`,
`Morph/Tests/AuthIdentity.lean`.
**Grade now:** model L3 (no `sorry`, axiom footprint is Lean's standard
`propext`/`Quot.sound` only, warning-free build) for the formal kernel;
**claim L1** for the register row, because no baseline was benchmarked. The
two grades are deliberately separate — see §5.

---

## 1. What was built, and what was not

The ten rows are protocol/crypto claims ("Sigma-protocol attestation beats
OAuth2", "SNARK membership beats passwords"). Building protocols is out of
scope for one cycle and would be dishonest to claim. What was built is the
*computable core* each row needs to be falsifiable, in the register's own
terms (ADR-019 §1: a decidable checking algorithm or computable synthesis
procedure, plus a kill criterion):

| Row | Kernel built | Key result |
|---|---|---|
| E-1361 | `findCap`, `Holds`, `bind` | witnesses returned by the search establish the capability; attestations are request-bound |
| E-1362 | `acc`, `remove`, `witness`, `Verify` | deletion divides the accumulator, so revocation works algebraically |
| E-1363 | `Attrs`, `Policy`, `allows`, `Satisfies` | executable check matches the semantics; raising never loses; ceilings block escalation |
| E-1364 | `RevState`, `revoke`, `valid` | revoke invalidates the witness and advances the epoch; stale witnesses rejected |
| E-1365 | `foldSig`, `delegate` | delegating re-signs locally against the derived root; chains commit to every hop |
| E-1366 | `Token`, `issueTag`, `spend` | tags separate origins for the same user; nonces cannot be replayed |
| E-1367 | `Form`, `Proof`, `check`, `Derives` | the Boolean checker only accepts derivable claims |
| E-1368 | `share`, `combine` | all-shares reconstruction recovers the secret; any `n − 1` shares fit every secret |
| E-1369 | `blind`, `unblind`, `signMsg` | unblinding recovers the plaintext signature; the signer's view fits every message |
| E-1370 | `Puf`, `mismatches`, `accept`, `ctSteps`, `earlySteps` | exact responses accepted at threshold 0; constant-time cost is content-free |

Not built: no Sigma protocol, no accumulator library, no policy engine, no
token service, no threshold scheme, no blind-signature library, no PUF
hardware. No cryptography was implemented beyond exact integer arithmetic.
Every row remains an experiment whose *external* claim is untested.

## 2. Research basis (per row)

- **E-1361.** Sigma protocols (Schnorr 1991; Cramer, Damgård, Schoenmakers,
  "Proofs of Partial Knowledge", 1994): completeness, special soundness, and
  the Fiat–Shamir binding of the transcript to the statement. The kernel
  models the two falsifiable halves that do not need a group: (a) the
  witness-returning synthesis procedure with soundness/completeness, and (b)
  the request binding (`bind_req_injective`), which is the non-token-exchange
  property replayed against a different request.
- **E-1362.** Dynamic accumulators (Camenisch–Lysyanskaya, CRYPTO 2002):
  quasi-commutative hashing, `acc' = acc · x`, witnesses for the rest, and
  deletion as division. Membership soundness rests on the strong RSA
  assumption and is named, not proved; the revocation algebra — the kill
  criterion's target — is exact.
- **E-1363.** Presburger arithmetic is decidable (Presburger 1929; Cooper's
  algorithm, 1972), so permission predicates compile to a decision procedure.
  The kernel is the lattice direction that matters: monotonicity, and the
  ceiling theorem that blocks the IDOR/IAM escalation the kill criterion
  names.
- **E-1364.** Revocation in pairing-based accumulators (Nguyen 2005) is epoch
  or list propagation. The kernel abstracts the epoch half: monotone epochs,
  validity as an epoch equation plus a list check, and the stale-witness
  rejection that makes list propagation unnecessary.
- **E-1365.** Homomorphic signatures (Boneh–Freeman, PKC 2011) let an edge
  verifier combine without the root. The kernel is the `foldSig` digest with
  `foldSig_append` (appending re-signs locally) and the per-hop commitment
  (`tamper_detected`), which is what an edge check actually relies on.
- **E-1366.** VRFs (Micali–Rabin–Vadhan, FOCS 1999) give unlinkable,
  server-verifiable tokens. Unlinkability in the information-theoretic sense
  needs distributions and is out of fragment; the kernel states the algebraic
  half exactly: origin separation without the key (`issueTag_origin_separates`),
  per-key identification with it (`issueTag_injective`), and replay safety.
- **E-1367.** Proof-carrying authorization (Appel–Felten, "Proof-Carrying
  Authentication", CCS 1999): the PDP runs a kernel that checks a proof term.
  The kernel is the reflection theorem `check_sound` — every acceptance is
  backed by a `Derives` derivation.
- **E-1368.** Additive (XOR) secret sharing: `n`-of-`n` with exact algebraic
  laws. `remaining_hides` is the information-theoretic statement in algebraic
  form (any `n − 1` shares are consistent with every secret), which is also
  why the threshold is `n` and why Shamir interpolation is the honest
  next iteration for `t < n`. The kill criterion names device-loss recovery;
  `rotate_preserves` is its kernel.
- **E-1369.** Blind signatures (Chaum 1983; blind Schnorr, Pointcheval–Stern
  1996). In exponent space the algebra is exact integer arithmetic, so the
  unlinkability theorem is a theorem, not a claim: `view_consistent` shows
  the authenticator's view is consistent with every message.
- **E-1370.** PUF challenge–response binding and timing side channels
  (Kocher 1996 and the constant-time discipline). The kernel proves the
  unavoidable trade (threshold acceptance admits impostors), the exact-match
  guarantee, and the timing statement: constant-time cost depends only on
  length while early-exit cost depends on secret content.

## 3. Design decisions

1. **One module family, ten sections.** ADR-019 allows a brief to cover a
   coherent row family; the three-file pattern (ADR-004) forbids extra files
   per domain. `AuthIdentity` holds all ten cores, with a mapping table in
   the `Spec.lean` docstring. Rows are separable into their own modules later
   without changing definitions.
2. **No `List.erase`.** The core `erase` is `BEq`-based and its rewrite
   lemmas did not fire under `simp` in this toolchain, so the accumulator
   uses its own structural `remove` (`if a = x then …`) with a `split`-based
   proof style. Same algebra, tractable proofs. Recorded because it is a
   toolchain datum for the "decidable core" claim.
3. **Proof terms carry their contexts.** `andElimL`/`andElimR`/`impElim` name
   the sibling/antecedent formula so `check` is structurally recursive on the
   proof and needs no guessing; `check_sound` is then a direct induction.
4. **Tags are arithmetic, not hashes.** `issueTag` packs key/origin/user into
   one number so injectivity and separation are `omega` facts, not hash
   conjectures. The 1000-bound is a domain bound on user ids, stated in the
   lemma hypotheses; real user spaces would need the hash indirection.
5. **Additive sharing, not Shamir.** The kernel proves what `n`-of-`n`
   additive sharing actually gives (reconstruction, hiding, rotation) and
   does not pretend at `t`-of-`n`. Interpolation is listed as the next
   iteration's target, with the field arithmetic it needs.
6. **PUF responses are bit lists.** Hamming distance, threshold acceptance
   and both timing models are structural on `List Bool`, so every timing and
   trade-off claim is `decide`-checkable. Physical noise modelling is out of
   fragment and stated as such.

## 4. Implementation map and proof burden

| File | Lines | Content |
|---|---|---|
| `Morph/Specs/AuthIdentity/Spec.lean` | 335 | 10 cores, mapping table, scope statement |
| `Morph/Specs/AuthIdentity/Lemmas.lean` | 395 | 38 theorems, no `sorry`, no axioms beyond Lean core |
| `Morph/Specs/AuthIdentity/Examples.lean` | 213 | 47 concrete instances, incl. law witnesses |
| `Morph/Tests/AuthIdentity.lean` | 185 | 42 independent checks, incl. negative cases |

Proof burden: 38 theorems over ~230 lines of definitions (ratio ≈ 1.7
theorems per 10 definition lines; many cores are one definition plus one
law). All proofs are manual `induction`/`simp`/`omega`/`decide`; no SMT, no
automation beyond core tactics. No core file (`Morph.HIR`, `Morph.MIR`,
`Morph.Semantics`) was touched, per the register's trusted-core rule.

Build record (warm cache, this machine):

- `lake build Morph.Specs.AuthIdentity.Lemmas` — 15–19 s.
- `lake build Morph.Specs.AuthIdentity.Spec` — 19–45 s.
- `lake build Morph.Tests.AuthIdentity` — ~5 s incremental.
- `lake build Morph Morph.Tests` — 416 jobs, success, no warnings, no
  `sorry` in the
...[truncated 3881 chars]