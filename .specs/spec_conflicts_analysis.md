# Specification Conflicts Analysis

**Date:** 2026-01-01
**Status:** CRITICAL - Multiple identifier conflicts detected

## Summary

During validation of the specification files, critical conflicts were discovered where the same identifier prefixes are being reused across multiple specification files within the same category. This violates the specification convention which requires unique prefixes per specification file.

## Conflicts Identified

### 1. UI Category Conflicts
**Prefix:** `UI-`

**Files Using This Prefix:**
- `spec/ui/ui_event_topology_spec.md` (UI-INV-001 to UI-INV-010, UI-REQ-001 to UI-REQ-009, UI-NFR-001 to UI-NFR-003, UI-THM-001 to UI-THM-005)
- `spec/ui/ui_constraint_algebra_spec.md` (UI-INV-001 to UI-INV-009, UI-REQ-001 to UI-REQ-008, UI-NFR-001 to UI-NFR-003, UI-THM-001 to UI-THM-003)

**Impact:** 22 conflicting identifiers

### 2. TYP Category Conflicts
**Prefix:** `TYP-`

**Files Using This Prefix:**
- `spec/type/type_unification_spec.md` (TYP-INV-001 to TYP-INV-009, TYP-REQ-001 to TYP-REQ-006, TYP-NFR-001 to TYP-NFR-002, TYP-THM-001 to TYP-THM-003)
- `spec/type/type_system_spec.md` (TYP-INV-001 to TYP-INV-017, TYP-REQ-001 to TYP-REQ-014, TYP-NFR-001 to TYP-NFR-003, TYP-THM-001 to TYP-THM-002)

**Impact:** 40 conflicting identifiers

### 3. FUZ Category Conflicts
**Prefix:** `FUZ-`

**Files Using This Prefix:**
- `spec/tooling/symbolic_execution_fuzz_spec.md` (FUZ-INV-001 to FUZ-INV-012, FUZ-REQ-001 to FUZ-REQ-007, FUZ-NFR-001 to FUZ-NFR-003, FUZ-THM-001 to FUZ-THM-003)
- `spec/tooling/fuzzing_combinatorial_spec.md` (FUZ-INV-001 to FUZ-INV-008, FUZ-REQ-001 to FUZ-REQ-006, FUZ-NFR-001 to FUZ-NFR-003, FUZ-THM-001 to FUZ-THM-002)

**Impact:** 30 conflicting identifiers

### 4. REG Category Conflicts
**Prefix:** `REG-`

**Files Using This Prefix:**
- `spec/tooling/registry_merkle_spec.md` (REG-INV-001 to REG-INV-011, REG-REQ-001 to REG-REQ-009, REG-NFR-001 to REG-NFR-002, REG-THM-001 to REG-THM-005)
- `spec/registry_consensus_spec.md` (REG-INV-001 to REG-INV-014, REG-REQ-001 to REG-REQ-008, REG-NFR-001 to REG-NFR-002, REG-THM-001 to REG-THM-002)

**Impact:** 40 conflicting identifiers

### 5. OPT Category Conflicts
**Prefix:** `OPT-`

**Files Using This Prefix:**
- `spec/optimization/optimization_manifold_spec.md` (OPT-INV-001 to OPT-INV-010, OPT-REQ-001 to OPT-REQ-006, OPT-NFR-001 to OPT-NFR-003, OPT-THM-001 to OPT-THM-002)
- `spec/optimization/optimization_bayesian_spec.md` (OPT-INV-001 to OPT-INV-008, OPT-REQ-001 to OPT-REQ-006, OPT-NFR-001 to OPT-NFR-003, OPT-THM-001 to OPT-THM-002)

**Impact:** 30 conflicting identifiers

### 6. MEM Category Conflicts
**Prefix:** `MEM-`

**Files Using This Prefix:**
- `spec/memory/memory_affine_logic_spec.md` (MEM-INV-001 to MEM-INV-010, MEM-REQ-001 to MEM-REQ-006, MEM-NFR-001 to MEM-NFR-003, MEM-THM-001 to MEM-THM-002)
- `spec/memory/memory_acyclicity_spec.md` (MEM-INV-001 to MEM-INV-010, MEM-REQ-001 to MEM-REQ-006, MEM-NFR-001 to MEM-NFR-003, MEM-THM-001 to MEM-THM-002)

**Impact:** 30 conflicting identifiers

### 7. STD Category Conflicts
**Prefix:** `STD-`

**Files Using This Prefix:**
- `spec/stdlib/stdlib_amortized_spec.md` (STD-INV-001 to STD-INV-008, STD-REQ-001 to STD-REQ-006, STD-NFR-001 to STD-NFR-003, STD-THM-001 to STD-THM-002)
- `spec/stdlib/stdlib_algebraic_spec.md` (STD-INV-001 to STD-INV-010, STD-REQ-001 to STD-REQ-006, STD-NFR-001 to STD-NFR-003, STD-THM-001 to STD-THM-002)

**Impact:** 30 conflicting identifiers

## Root Cause

The specification convention states that identifiers should follow the pattern `[PREFIX]-[TYPE]-[NUMBER]` where PREFIX is unique per specification file. However, during the creation of multiple specifications within the same category, the same prefix was reused, leading to conflicts.

## Resolution Strategy

### Option 1: Prefix Differentiation (RECOMMENDED)

Add a suffix to the prefix to make it unique per file:

**UI Category:**
- `spec/ui/ui_event_topology_spec.md`: `UIEVT-` (UI Event Topology)
- `spec/ui/ui_constraint_algebra_spec.md`: `UICST-` (UI Constraint Algebra)

**TYP Category:**
- `spec/type/type_unification_spec.md`: `TYPUNI-` (Type Unification)
- `spec/type/type_system_spec.md`: `TYP-` (Type System - keep original)

**FUZ Category:**
- `spec/tooling/symbolic_execution_fuzz_spec.md`: `FUZSYM-` (Fuzzing Symbolic)
- `spec/tooling/fuzzing_combinatorial_spec.md`: `FUZCOM-` (Fuzzing Combinatorial)

**REG Category:**
- `spec/tooling/registry_merkle_spec.md`: `REGMRK-` (Registry Merkle)
- `spec/registry_consensus_spec.md`: `REGCNS-` (Registry Consensus)

**OPT Category:**
- `spec/optimization/optimization_manifold_spec.md`: `OPTMAN-` (Optimization Manifold)
- `spec/optimization/optimization_bayesian_spec.md`: `OPTBAY-` (Optimization Bayesian)

**MEM Category:**
- `spec/memory/memory_affine_logic_spec.md`: `MEMAFF-` (Memory Affine)
- `spec/memory/memory_acyclicity_spec.md`: `MEMACY-` (Memory Acyclicity)

**STD Category:**
- `spec/stdlib/stdlib_amortized_spec.md`: `STDAMO-` (Stdlib Amortized)
- `spec/stdlib/stdlib_algebraic_spec.md`: `STDALG-` (Stdlib Algebraic)

### Option 2: Number Range Segmentation

Keep the same prefix but use non-overlapping number ranges:

**UI Category:**
- `spec/ui/ui_event_topology_spec.md`: UI-INV-001 to UI-INV-099
- `spec/ui/ui_constraint_algebra_spec.md`: UI-INV-100 to UI-INV-199

**TYP Category:**
- `spec/type/type_unification_spec.md`: TYP-INV-001 to TYP-INV-099
- `spec/type/type_system_spec.md`: TYP-INV-100 to TYP-INV-199

...and so on for all categories.

**Disadvantage:** Less intuitive, harder to maintain, requires tracking number ranges.

### Option 3: File-Based Prefixes

Use the full file name as the prefix:

**UI Category:**
- `spec/ui/ui_event_topology_spec.md`: `UIEVT-`
- `spec/ui/ui_constraint_algebra_spec.md`: `UICST-`

**Disadvantage:** Longer prefixes, but very clear and unique.

## Recommendation

**Option 1 (Prefix Differentiation)** is recommended because:
1. Maintains short, readable prefixes
2. Clearly distinguishes between related specifications
3. Follows existing naming patterns
4. Easy to implement with find-and-replace
5. Maintains traceability and readability

## Implementation Plan

1. For each conflicting category, apply the recommended prefix changes
2. Update all identifier references in the affected files
3. Update dependencies and traceability sections
4. Verify no conflicts remain
5. Update specification convention document to clarify prefix uniqueness requirements

## Impact Assessment

- **Files to Modify:** 14 specification files
- **Identifiers to Update:** ~222 identifiers
- **Estimated Effort:** 2-3 hours
- **Risk:** Low (mechanical changes with clear mapping)

## Next Steps

1. Obtain approval for the resolution strategy
2. Implement prefix changes
3. Validate no conflicts remain
4. Update documentation
5. Commit changes with clear commit message
