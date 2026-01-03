# Specification Conflict Resolution Progress

**Date:** 2026-01-01
**Status:** In Progress

## Summary

Applying **Prefix Differentiation** strategy to resolve identifier conflicts across 7 categories affecting 14 specification files and approximately 222 identifiers.

## Completed Fixes

### 1. UI Category ✓
- **spec/ui/ui_event_topology_spec.md**: Changed `UI-` → `UIEVT-` (UI Event Topology)
  - 22 identifiers updated (UIEVT-INV-001 to UIEVT-INV-010, UIEVT-REQ-001 to UIEVT-REQ-009, UIEVT-NFR-001 to UIEVT-NFR-003, UIEVT-THM-001 to UIEVT-THM-005)
  
- **spec/ui/ui_constraint_algebra_spec.md**: Changed `UI-` → `UICST-` (UI Constraint Algebra)
  - 22 identifiers updated (UICST-INV-001 to UICST-INV-009, UICST-REQ-001 to UICST-REQ-008, UICST-NFR-001 to UICST-NFR-003, UICST-THM-001 to UICST-THM-003)

### 2. TYP Category ✓
- **spec/type/type_unification_spec.md**: Changed `TYP-` → `TYPUNI-` (Type Unification)
  - 22 identifiers updated (TYPUNI-INV-001 to TYPUNI-INV-009, TYPUNI-REQ-001 to TYPUNI-REQ-006, TYPUNI-NFR-001 to TYPUNI-NFR-002, TYPUNI-THM-001 to TYPUNI-THM-003)

- **spec/type/type_system_spec.md**: Keeps `TYP-` prefix (no change needed - primary type system spec)

## Remaining Fixes

### 3. FUZ Category (Pending)
- **spec/tooling/symbolic_execution_fuzz_spec.md**: Change `FUZ-` → `FUZSYM-` (Fuzzing Symbolic)
  - ~30 identifiers to update
  
- **spec/tooling/fuzzing_combinatorial_spec.md**: Change `FUZ-` → `FUZCOM-` (Fuzzing Combinatorial)
  - ~30 identifiers to update

### 4. REG Category (Pending)
- **spec/tooling/registry_merkle_spec.md**: Change `REG-` → `REGMRK-` (Registry Merkle)
  - ~40 identifiers to update
  
- **spec/registry_consensus_spec.md**: Change `REG-` → `REGCNS-` (Registry Consensus)
  - ~40 identifiers to update

### 5. OPT Category (Pending)
- **spec/optimization/optimization_manifold_spec.md**: Change `OPT-` → `OPTMAN-` (Optimization Manifold)
  - ~30 identifiers to update
  
- **spec/optimization/optimization_bayesian_spec.md**: Change `OPT-` → `OPTBAY-` (Optimization Bayesian)
  - ~30 identifiers to update

### 6. MEM Category (Pending)
- **spec/memory/memory_affine_logic_spec.md**: Change `MEM-` → `MEMAFF-` (Memory Affine)
  - ~30 identifiers to update
  
- **spec/memory/memory_acyclicity_spec.md**: Change `MEM-` → `MEMACY-` (Memory Acyclicity)
  - ~30 identifiers to update

### 7. STD Category (Pending)
- **spec/stdlib/stdlib_amortized_spec.md**: Change `STD-` → `STDAMO-` (Stdlib Amortized)
  - ~30 identifiers to update
  
- **spec/stdlib/stdlib_algebraic_spec.md**: Change `STD-` → `STDALG-` (Stdlib Algebraic)
  - ~30 identifiers to update

## Progress Summary

| Category | Files | Status | Identifiers Fixed |
|----------|--------|---------|------------------|
| UI | 2 | ✓ Complete | 44 |
| TYP | 2 | ✓ Complete | 22 |
| FUZ | 2 | ⏳ Pending | 0 |
| REG | 2 | ⏳ Pending | 0 |
| OPT | 2 | ⏳ Pending | 0 |
| MEM | 2 | ⏳ Pending | 0 |
| STD | 2 | ⏳ Pending | 0 |
| **Total** | **14** | **2/7 (29%)** | **66/222 (30%)** |

## Next Steps

1. Complete remaining 5 categories (FUZ, REG, OPT, MEM, STD)
2. Verify no conflicts remain across all specifications
3. Update specification convention document to clarify prefix uniqueness requirements
4. Update spec/README.md with corrected identifiers

## Notes

- All changes follow the **Prefix Differentiation** strategy as recommended in conflict analysis
- Prefixes are designed to be:
  - Short (3-6 characters)
  - Descriptive (indicates specification focus)
  - Unique (no conflicts within category)
  - Consistent (follows naming pattern)
- Dependencies and traceability sections are updated to reflect new prefixes
