# Specification Contradictions

This document catalogs contradictions identified across the Morph specification suite and their resolutions.

---

## Contradiction #1: Agent-First vs Human Usability

*Source:* `spec/language/dual_optimization_spec.md`

The specification simultaneously mandates projectional-only editing (agent-first) while requiring human-readable syntax (human usability). The resolution prioritizes agent-first design with human-readable projections as secondary artifacts.

*Status:* Resolved in `spec/language/dual_optimization_spec.md`

---

## Contradiction #10 (C-003): Effect Category Mismatch

*Source:* `spec/language/morph_language_spec.md` (LANG-REQ-040), `spec/type/type_system_spec.md` (Section 2.6.1), `spec/type/effect_system_spec.md` (EFF-REQ-001)

Three different definitions of the effect category set existed:
- `effect_system_spec.md` (canonical): 4 effects {IO, Net, Time, System}, Pure is a capability not an effect
- `morph_language_spec.md` LANG-REQ-040: 5 items {Pure, IO, Net, Time, System} — Pure incorrectly listed as effect
- `type_system_spec.md` Section 2.6.1: 5 items with Pure in the lattice — same error
- `infrastructure_safety_contracts_spec.md`: Used `Sys` instead of `System` — only file with this abbreviation

*Fix:* Updated morph_language_spec.md, type_system_spec.md, infrastructure_safety_contracts_spec.md, and GLOSSARY.md to reflect the canonical 4-effect lattice {IO, Net, Time, System} with Pure as a separate capability. Fixed `Sys` → `System` in infrastructure_safety_contracts_spec.md.

*Status:* Resolved

*Source:* `spec/memory/memory_model_spec.md`, `spec/memory/memory_affine_logic_spec.md`

Three locations incorrectly stated affine logic requires resources to be used "exactly once," which is the definition of linear logic. The canonical distinction is: affine = at most once (use 0 or 1 times), linear = exactly once (use exactly 1 time, cannot discard).

Fixed 3 occurrences of "exactly once" to "at most once" in `memory_model_spec.md` and `memory_affine_logic_spec.md`. Canonical definition confirmed: affine = at most once, linear = exactly once.

*Status:* Resolved

---

## Contradiction #6 (C-001): Duplicate LANG-REQ-071 — FALSE POSITIVE

*Source:* Audit report flagged LANG-REQ-071 as appearing twice with different descriptions ("Input Normalization" and "Error Type Enumeration").

*Resolution:* Investigated — not a contradiction. Both occurrences of LANG-REQ-071 refer to "Input Normalization." The audit report incorrectly stated the second occurrence was "Error Type Enumeration," which is actually LANG-REQ-114 (Section 15.1.2). The LANG-REQ-072 dependency reference to LANG-REQ-071 is correct.

*Status:* No fix needed — false positive in audit report.

---

## Contradiction #7 (C-002): `async fn` Syntax in Code Examples Violates LANG-REQ-023

*Source:* `spec/language/morph_language_spec.md` (Section 15.7, 15.9, 15.14)

The keyword definitions in `morph_language_spec.md` (LANG-REQ-023) and `lexical_structure_syntax_spec.md` are consistent — `async` is a contextual keyword used only with `let` bindings. However, code examples throughout Section 15 (Error Handling) use `async fn` and `.await` syntax, which directly contradicts LANG-REQ-023: *"There are no standalone `async`/`await` keywords."*

*Fix:* All `async fn` examples updated to use `fn ... performs IO` syntax with `.await` removed (functions marked `performs IO` automatically yield the Green Thread per LANG-REQ-023).

*Status:* Fixed in `spec/language/morph_language_spec.md`

---

## Contradiction #8 (C-005): Keyword Count Off-by-One — FALSE POSITIVE

*Source:* Audit report flagged potential mismatch between stated keyword count and actual count.

*Resolution:* Verified — 22 keywords is correct. The keyword table in `lexical_structure_syntax_spec.md` (Section 2.1) lists exactly 22 keywords including `async` as a contextual keyword for dataflow/let modifier. `morph_language_spec.md` LANG-REQ-006 (line 108) correctly states "22 keywords (including `async` as a contextual keyword used only as a `let` modifier)." No contradiction.

*Status:* No fix needed — false positive in audit report.

---

## Contradiction #9 (C-006): Version Drift in Examples — ALREADY CORRECT

*Source:* Audit report flagged stale v2.0.0 references in `version_compatibility_spec.md` for type_system, memory_model, and execution_model.

*Resolution:* Verified — all version references are current. The inventory table (Section 4.1) correctly lists type_system as 2.1.0, memory_model as 3.3.0, and execution_model as 2.2.0, matching the actual spec file headers. All compatibility matrix entries and dependency tables use these correct versions. The remaining `2.0.0` references in the file refer to SemVer 2.0.0 (the standard), historical upgrade paths, and generic code examples — not stale spec versions.

*Status:* No fix needed — versions already correct.

