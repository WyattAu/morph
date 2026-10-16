# Taint Tracking Across Dialect Boundaries Specification

**Spec ID:** SEC-IFC-002
**Version:** 1.0.0
**Status:** Formalized (Lean 4)
**Date:** 2026-10-16
**Formal Module:** `Morph/Specs/TaintFlow/`, `Morph/Specs/SecurityFlow/`
**Closes:** SG-003 (taint tracking across dialect boundaries)
**Related Specifications:** [`security_flow_spec.md`](./security_flow_spec.md),
[`security_ocap_spec.md`](./security_ocap_spec.md),
[`morph_language_spec.md`](../language/morph_language_spec.md)

---

## 1. Purpose

SG-003 asked what happens to a taint label when a program crosses a *dialect*
boundary. The existing `SecurityFlow` module could not answer it: its
`NonInterference` predicate quantified over *labels* as though they were program
states, making it vacuous, and every theorem in it had the form `h → h`.

This specification states information-flow control over an actual expression
language and proves the property that a dialect boundary preserves it.

---

## 2. Research Basis (research loop 4)

| Source | Result used | Relevance |
|--------|-------------|-----------|
| Zdancewic & Myers. *Robust Declassification.* POPL 2001 | Robustness: an attacker must not control *whether* declassification happens | The rule `Trusted pc` in `translate` |
| Myers & Liskov. *Enforcing Robust Declassification.* CSFW 2004 | Type-based enforcement: the decision to downgrade requires sufficient integrity | The pc label stands in for the deciding context's integrity |
| Zdancewic. *A Type System for Robust Declassification.* TOPLAS 2003 | The `Robust-Declassify` rule `I(pc) ⊑ auth(ℓ,ℓ′)` | Directly instantiated |
| Köpf, Bartsch, Smith, Wenzl. *Nonmalleable Information Flow Control.* CCS 2017/2021 | Robustness as a **4-safety hyperproperty**; subsumes transparent endorsement | Documents what is *not* formalized here (§6) |
| Costa, Köpf, Kolluri, Paverd, Russinovich, Salem, Tople, Wutschitz, Zanella-Béguelin. *Securing AI Agents with Information-Flow Control* (Fides), arXiv:2505.23643, 2025 | Characterizes **the class of properties enforceable by dynamic taint-tracking** for agent planners; tracks confidentiality *and* integrity | The closest work to Morph: an agentic language. Its conclusion — a taint label must survive every planner transformation — is exactly SG-003 |
| Schneider. *Handbook of Applied Cryptography*, ch. 9 (Sept. 2025) | Standard sink-based IFC typing rule | The `AllowedAssign` predicate |

**Conclusion of the survey.** For a general agentic planner, dynamic taint
tracking is known to be enforceable for *end-to-end* flow properties — but only
if the label survives each transformation the planner performs. A dialect
projection is such a transformation. Nobody in the literature formalizes that
for a multi-dialect language; the mechanism (reject-or-preserve) and the
robustness condition (authority to downgrade) are the contributions here.

---

## 3. Model

*SEC-IFC-001:* Confidentiality labels are the two-point lattice
`pub ⊑ sec`, with `join` and the usual order laws (`le_refl`, `le_trans`,
`le_antisymm`, `join_le_iff`).

*SEC-IFC-002:* Labelled expressions are `lit | var | add | ite | decl`. `decl`
is the declassification form. `taint ρ e` computes the label structurally;
`ite` contributes an **implicit flow**.

*SEC-IFC-003:* `Dialect := strict | permissive`. `translate to pc e` either
returns an expression **unchanged** or returns `none`. It never rewrites.

*SEC-IFC-004:* `Trusted pc ↔ pc = .sec`. A declassifying expression crosses
into the `strict` dialect only when the program counter is trusted —
Zdancewic's `I(pc) ⊑ auth(ℓ, ℓ′)`.

*SEC-IFC-005:* A program is a list of assignments. `AllowedAssign ρ x e`
requires `taint ρ e ⊑ ρ x` (the sink check), and `Allowed` requires it at every
statement.

---

## 4. Formal Results

| Theorem | Statement |
|---------|-----------|
| `taint_preserved` | `translate to pc e = some e' → taint ρ e' = taint ρ e`. **Exactly** — a boundary cannot quietly downgrade a label, because the only operation it has is rejection. |
| `reject_untrusted_decl` | **Robustness:** an untrusted pc gets `translate .strict .pub (.decl e) = none` |
| `allow_trusted_decl` | a trusted pc may cross with the label intact |
| `no_decl_after_translation` | whatever crosses into `strict` is declassification-free, or the pc was trusted |
| `flows_translation` | `Flows ρ pc e l` is preserved by translation, at the *same* label `l` |
| `flows_pub_without_decl` | a public-pc, declassification-free program can only produce public |
| `allowed_no_leak` | **Noninterference:** an allowed program's secret variables can only shrink |
| `allowed_preserved` | the sink check transfers across the boundary (each statement's label is unchanged, so each intermediate environment is literally equal) |
| **`boundary_preserves_noninterference`** | **SG-003, end to end:** a noninterfering program stays noninterfering after translation into the strict dialect |

`SecurityFlow` is rewired: `spec_non_interference_statement`,
`noninterference_formalized` and `taint_preserved_across_dialects` are the
transfer theorems, replacing the vacuous predicate and the `h → h` proofs.

---

## 5. Why reject-or-preserve

The alternative to rejection is *retyping*: translating a program across a
boundary and re-deriving its labels. That is unsound in the presence of
declassification — the new typing judgment has no record of which labels were
downgraded, so a second projection can treat a downgraded label as original.
Making translation a relation that preserves labels *by construction* removes
the question: either the label is the same, or the program does not cross.

This is the same argument as in loop 2 (SG-002): a modelling decision that
removes a class of proofs is worth more than one that discharges them.

---

## 6. Scope Limits

1. **Confidentiality only.** Integrity (endorsement) and the 4-safety
   hyperproperty form of robustness (Köpf et al.) are not formalized; the pc
   label is a proxy for integrity, not a second lattice.
2. **No attacker model.** Robustness is proved *statically* (the translation
   rejects), not as a hyperproperty over traces.
3. **No implicit-flow analysis.** `ite` adds the pc to the taint, which is the
   standard conservative treatment; path-insensitive.
4. **Labels are binary.** A principal lattice (decentralized labels model) is
   future work; the `SecurityLattice` interface already generalises it.

---

## 7. Traceability

| Requirement | Formalized in |
|-------------|---------------|
| SG-003 taint across dialect boundaries | `taint_preserved`, `taint_preserved_across_dialects` |
| SEC-REQ noninterference | `allowed_no_leak`, `noninterference_formalized` |
| SEC-REQ robust declassification | `reject_untrusted_decl`, `no_decl_after_translation` |
| SEC-REQ sink-based typing | `AllowedAssign`, `flows_translation` |

---

## Change Log

| Version | Date | Change | Author |
|---------|------|--------|--------|
| 1.0.0 | 2026-10-16 | Initial: taint lattice, dialect translation, robust-declassification rule, noninterference, and the boundary theorems; `SecurityFlow` rewired to the real statements | Morph research loop 4 |