# ADR-001: Lean 4.28.0-rc1 Migration

**Status:** Accepted  
**Date:** 2026-01-31  
**Decision Type:** Technical  
**Related ADRs:** ADR-002, ADR-003  
**Related Documents:** [`.specs/00_current_state/manifest.md`](../00_current_state/manifest.md), [`.specs/04_future_state/manifest.md`](../04_future_state/manifest.md), [`.specs/03_threat_model/analysis.md`](../03_threat_model/analysis.md)

---

## Context

The Morph project currently specifies Lean 4.28.0-rc1 as its toolchain in the [`lean-toolchain`](../../lean-toolchain) file, but all direct dependencies in [`lakefile.toml`](../../lakefile.toml) are pinned to v4.10.0 versions. This represents an 18 minor version gap between the toolchain and dependencies, which is unprecedented in Lean 4's evolution history.

### Current State

| Component | Current Version | File |
|-----------|----------------|------|
| Lean Toolchain | v4.28.0-rc1 | [`lean-toolchain`](../../lean-toolchain) |
| batteries | v4.10.0 | [`lakefile.toml`](../../lakefile.toml) |
| aesop | v4.10.0 | [`lakefile.toml`](../../lakefile.toml) |
| mathlib4 | v4.10.0 | [`lakefile.toml`](../../lakefile.toml) |

### Problems

1. **Critical Version Mismatch (RISK-COMP-001):** The 18 minor version gap causes complete build failure due to API incompatibilities, type signature changes, and breaking changes in Lean 4 core library.

2. **ProofWidgets Incompatibility (RISK-COMP-002):** The transitive ProofWidgets4 dependency (v0.0.84) has configuration errors incompatible with Lean 4.28.0-rc1, blocking Lake workspace configuration entirely.

3. **Core Library Breaking Changes (RISK-COMP-003):** Between v4.10.0 and v4.28.0-rc1, significant changes to the Lean 4 core library include type signature modifications, deprecated API removals, changes to implicit parameter synthesis, and modifications to metaprogramming APIs.

4. **mathlib4 API Incompatibilities (RISK-COMP-004):** Major changes include module reorganization, theorem renaming, type class hierarchy updates, and proof automation strategy modifications.

### Alternatives Considered

#### Alternative 1: Downgrade Toolchain to v4.10.0

**Pros:**
- Immediate compatibility with existing dependencies
- Minimal code changes required
- Stable, production-ready toolchain

**Cons:**
- Forfeits access to Lean 4.28.0-rc1 improvements and bug fixes
- May require future migration anyway
- Misses opportunity to modernize the codebase
- Does not address underlying architectural debt

#### Alternative 2: Maintain Mixed Versions

**Pros:**
- Gradual migration path
- Can test compatibility incrementally

**Cons:**
- Unsupported configuration
- Unpredictable behavior
- Increased maintenance burden
- No clear path to resolution

#### Alternative 3: Upgrade to Lean 4.28.0-rc1 (Chosen)

**Pros:**
- Access to latest Lean 4 features and improvements
- Future-proof codebase
- Aligns with Lean 4 ecosystem direction
- Enables use of latest dependency versions
- Addresses technical debt comprehensively

**Cons:**
- Significant migration effort required
- Breaking changes across all files
- Potential for new bugs in release candidate
- Requires dependency updates

---

## Decision

**Upgrade the Morph project to Lean 4.28.0-rc1** and align all dependencies to versions compatible with this toolchain.

### Implementation Plan

#### Phase 1: Toolchain and Dependency Alignment

1. **Keep Lean Toolchain at v4.28.0-rc1**
   - The toolchain is already correctly set in [`lean-toolchain`](../../lean-toolchain)
   - This is the target version we are migrating to

2. **Update Direct Dependencies** (see [ADR-003](./ADR-003-dependency-version-alignment.md))
   - Update batteries to v4.28.0-compatible version
   - Update aesop to v4.28.0-compatible version
   - Update mathlib4 to v4.28.0-compatible version

3. **Resolve ProofWidgets Incompatibility** (see [ADR-002](./ADR-002-proofwidgets-removal.md))
   - Remove ProofWidgets dependency if not needed
   - Or update to a v4.28.0-compatible version

#### Phase 2: Code Migration

1. **Fix Syntax Errors**
   - Resolve unterminated comment in [`Morph/Specs/ArcAffineIntegration/Examples.lean`](../../Morph/Specs/ArcAffineIntegration/Examples.lean:237)

2. **Update Imports**
   - Replace deprecated imports with new module paths
   - Update mathlib4 imports to match new module structure

3. **Fix Type Errors**
   - Update function calls to match new type signatures
   - Add explicit type annotations where needed
   - Replace deprecated functions with current equivalents

4. **Update Proof Scripts**
   - Fix broken proof tactics
   - Update aesop configurations
   - Adjust proof automation strategies

#### Phase 3: Verification

1. **Compilation Verification**
   - Run `lake build` to ensure all modules compile
   - Verify zero syntax errors
   - Verify zero type errors

2. **Testing**
   - Run all tests in [`Morph/Tests/`](../../Morph/Tests/)
   - Execute all examples in specification directories
   - Verify all proofs complete successfully

3. **Documentation Update**
   - Update README to reflect Lean 4.28.0-rc1 requirement
   - Document migration changes
   - Update build instructions

---

## Consequences

### Positive Consequences

1. **Modern Toolchain:** Access to Lean 4.28.0-rc1 features including improved type checking, better error messages, and enhanced metaprogramming capabilities.

2. **Ecosystem Alignment:** Compatibility with the latest versions of the Lean 4 ecosystem, including mathlib4, batteries, and aesop.

3. **Technical Debt Reduction:** Comprehensive resolution of version mismatch issues, eliminating a major source of technical debt.

4. **Future-Proofing:** The codebase will be positioned to adopt future Lean 4 releases more easily.

5. **Improved Developer Experience:** Better tooling, editor support, and documentation from using a current toolchain.

6. **Security Benefits:** Access to security fixes and improvements in the Lean 4 toolchain and dependencies.

### Negative Consequences

1. **Migration Effort:** Significant effort required to update all code to be compatible with Lean 4.28.0-rc1.

2. **Breaking Changes:** All files may require changes due to breaking changes in the Lean 4 core library and dependencies.

3. **Learning Curve:** Team members need to learn new APIs and patterns introduced in v4.28.0-rc1.

4. **Release Candidate Risks:** Using a release candidate means potential for bugs or instability before final release.

5. **Dependency Availability:** Some dependencies may not have v4.28.0-compatible versions available yet, requiring workarounds.

6. **Proof Re-verification:** All proofs may need to be re-verified and potentially adjusted due to changes in proof automation and type class resolution.

### Neutral Consequences

1. **Build Time:** Build times may increase or decrease depending on changes in the Lean 4 compiler and dependency optimizations.

2. **Binary Compatibility:** Compiled artifacts will not be compatible with v4.10.0 toolchain, requiring rebuilds for all consumers.

3. **CI/CD Updates:** CI/CD pipelines will need to be updated to use v4.28.0-rc1 toolchain.

---

## Status

**Accepted** - This decision has been approved and implementation is in progress.

### Implementation Status

| Phase | Status | Notes |
|-------|--------|-------|
| Phase 1: Toolchain and Dependency Alignment | Pending | Waiting on ADR-002 and ADR-003 completion |
| Phase 2: Code Migration | Pending | Depends on Phase 1 |
| Phase 3: Verification | Pending | Depends on Phase 2 |

---

## References

- [Lean 4 Changelog](https://github.com/leanprover/lean4/blob/master/CHANGELOG.md)
- [Lean 4.28.0-rc1 Release Notes](https://github.com/leanprover/lean4/releases/tag/v4.28.0-rc1)
- [`.specs/00_current_state/manifest.md`](../00_current_state/manifest.md) - Current state analysis
- [`.specs/04_future_state/manifest.md`](../04_future_state/manifest.md) - Target state definition
- [`.specs/03_threat_model/analysis.md`](../03_threat_model/analysis.md) - Risk analysis
- [ADR-002: ProofWidgets Dependency Removal](./ADR-002-proofwidgets-removal.md)
- [ADR-003: Dependency Version Alignment](./ADR-003-dependency-version-alignment.md)
