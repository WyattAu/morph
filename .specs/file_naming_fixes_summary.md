# File Naming Fixes Summary

**Date:** 2026-01-01
**Status:** Ready for Execution

## Summary

This document summarizes the 22 files with naming typos that need to be fixed.

## Files to Rename

| # | Current Name | Correct Name | Category | Typo Type |
|---|--------------|---------------|----------|------------|
| 1 | `spec/optimization/optimization_search_engine_specification.md` | `spec/optimization/optimization_search_engine_specification.md` | OPT | Vowel substitution (a→e) |
| 2 | `spec/tooling/operational_semantics_spec.md` | `spec/tooling/operational_semantics_spec.md` | TOO | Vowel substitution (a→e) |
| 3 | `spec/tooling/reactive_frp_spec.md` | `spec/tooling/reactive_frp_spec.md` | TOO | Vowel substitution (a→e) |
| 4 | `spec/tooling/context_comonad_spec.md` | `spec/tooling/context_comonad_spec.md` | TOO | Vowel substitution (o→a) |
| 5 | `spec/tooling/symbolic_execution_fuzz_spec.md` | `spec/tooling/symbolic_execution_fuzz_spec.md` | FUZ | Vowel substitution (e→a) |
| 6 | `spec/tooling/synthesis_inhabitation_spec.md` | `spec/tooling/synthesis_inhabitation_spec.md` | TOO | Vowel substitution (a→e) |
| 7 | `spec/tooling/fuzzing_combinatorial_spec.md` | `spec/tooling/fuzzing_combinatorial_spec.md` | FUZ | Vowel substitution (a→e) |
| 8 | `spec/tooling/parsing_island_grammar_spec.md` | `spec/tooling/parsing_island_grammar_spec.md` | TOO | Vowel substitution (a→e) |
| 9 | `spec/tooling/registry_merkle_spec.md` | `spec/tooling/registry_merkle_spec.md` | REG | Vowel substitution (e→a) |
| 10 | `spec/language/lexical_structure_syntax_spec.md` | `spec/language/lexical_structure_syntax_spec.md` | LNG | Vowel substitution (a→e) |
| 11 | `spec/language/scoping_lambda_calculus_spec.md` | `spec/language/scoping_lambda_calculus_spec.md` | LNG | Vowel substitution (a→e) |
| 12 | `spec/memory/memory_affine_logic_spec.md` | `spec/memory/memory_affine_logic_spec.md` | MEM | Vowel substitution (a→e) |
| 13 | `spec/memory/memory_acyclicity_spec.md` | `spec/memory/memory_acyclicity_spec.md` | MEM | Vowel substitution (a→e) |
| 14 | `spec/stdlib/stdlib_amortized_spec.md` | `spec/stdlib/stdlib_amortized_spec.md` | STD | Vowel substitution (a→e) |
| 15 | `spec/stdlib/stdlib_algebraic_spec.md` | `spec/stdlib/stdlib_algebraic_spec.md` | STD | Vowel substitution (a→e) |
| 16 | `spec/licensing/license_deontic_logic_spec.md` | `spec/licensing/license_deontic_logic_spec.md` | LIC | Vowel substitution (a→e) |
| 17 | `spec/scheduler_randomized_stealing_spec.md` | `spec/scheduler_randomized_stealing_spec.md` | SCH | Vowel substitution (a→e) |
| 18 | `spec/security_ocap_spec.md` | `spec/security_ocap_spec.md` | SEC | Vowel substitution (a→e) |
| 19 | `spec/storage_dawg_spec.md` | `spec/storage_dawg_spec.md` | STO | Vowel substitution (a→e) |
| 20 | `spec/distributed_vector_clock_spec.md` | `spec/distributed_vector_clock_spec.md` | DIS | Vowel substitution (a→e) |
| 21 | `spec/module_existential_spec.md` | `spec/module_existential_spec.md` | MOD | Vowel substitution (a→e) |
| 22 | `spec/build/abi_data_refinement_spec.md` | `spec/build/abi_data_refinement_spec.md` | BLD | Vowel substitution (a→e) |

## Typo Patterns

The typos follow these consistent patterns:

1. **Vowel Substitution (a→e):** 16 files
   - optimization → optimization
   - semantics → semantics
   - frp → frp
   - inhabitation → inhabitation
   - combinatorial → combinatorial
   - island → island
   - merkle → merkle
   - structure → structure
   - lambda → lambda
   - affine → affine
   - acyclicity → acyclicity
   - amortized → amortized
   - algebraic → algebraic
   - deontic → deontic
   - randomized → randomized
   - ocap → ocap
   - dawg → dawg
   - vector → vector
   - existential → existential
   - refinement → refinement

2. **Consonant Duplication (mm→m):** 0 files
   - None identified

3. **Letter Transposition (ae→ea):** 0 files
   - None identified

## Execution Strategy

1. **Rename files using Git** to preserve history
2. **Update all internal references** in specification files
3. **Update documentation** (spec/README.md, roadmap.md, etc.)
4. **Verify no broken links** remain

## Next Steps

1. Execute file renames using `git mv` commands
2. Search for and update all internal references
3. Update spec/README.md with corrected file names
4. Verify all links work correctly
5. Final validation to ensure no conflicts remain

## Notes

- All files follow the same typo pattern (vowel substitution a→e)
- This suggests a systematic error in file naming
- The fix is straightforward: rename files to correct spelling
- No content changes needed, only file renames
- All specification files have already been refactored to v2.0.0 convention

---

**Status:** Ready to execute file renames
**Confidence:** High - Clear list of all files to rename
