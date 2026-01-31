# ADR-006: Complete Proof Requirement

## Status
**Accepted**

## Context

The Morph language Lean validation project is a formal verification effort where the correctness of specifications depends on complete and valid proofs. Analysis of the original undergraduate codebase revealed significant issues with proof completeness:

1. **Extensive Use of `sorry`**: Many theorems and lemmas used Lean's `sorry` placeholder instead of complete proofs
2. **Incomplete Proofs**: Some proofs were partially written but never finished
3. **Unverified Theorems**: Theorems were stated without proof, making their correctness uncertain
4. **Commented-Out Proofs**: Complete proofs were commented out, leaving only theorem statements
5. **Proof Fragments**: Proof attempts were abandoned mid-way, leaving invalid code

These issues undermine the entire purpose of formal verification: to provide mathematical certainty about the correctness of specifications. A theorem without a proof is merely a conjecture, not a verified property.

The project requires that all theorems be fully proved before submission, ensuring that every stated property is mathematically verified.

## Decision Drivers

1. **Formal Correctness**: All theorems must be mathematically verified
2. **Trustworthiness**: Users must be able to trust that specifications are correct
3. **Verification Integrity**: The value of formal verification depends on complete proofs
4. **Code Quality**: Incomplete proofs indicate incomplete work
5. **Maintainability**: Future developers need complete proofs to understand and extend specifications
6. **CI/CD Reliability**: Automated builds should fail if proofs are incomplete
7. **Educational Value**: Complete proofs serve as examples for learning
8. **Security**: Security-related theorems must be fully verified

## Considered Options

### Option 1: Allow `sorry` in Development, Require Removal Before Merge
- Permit `sorry` during development but require complete proofs before merging to main
- **Pros**: Allows rapid prototyping, acknowledges that proofs take time
- **Cons**: Relies on developer discipline, difficult to enforce, incomplete code may slip through

### Option 2: Allow `sorry` with Explicit Tracking
- Permit `sorry` but require tracking in a separate file (e.g., `TODO.lean`)
- **Pros**: Makes incomplete work visible, provides accountability
- **Cons**: Still allows incomplete code, tracking may become outdated, adds administrative overhead

### Option 3: Allow `sorry` Only in Feature Branches
- Feature branches can use `sorry`, but main branch must have complete proofs
- **Pros**: Separates development from production, allows experimentation
- **Cons**: Requires strict branch discipline, incomplete code may be merged accidentally

### Option 4: Zero-Tolerance for `sorry` and Incomplete Proofs
- All theorems must have complete proofs before any commit
- **Pros**: Ensures correctness at all times, enforces quality, no incomplete code in repository
- **Cons**: May slow development, requires proofs to be completed before committing

### Option 5: Tiered Proof Requirements
- Core theorems require complete proofs, auxiliary theorems can use `sorry`
- **Pros**: Focuses effort on critical properties, acknowledges varying importance
- **Cons**: Subjective classification of importance, auxiliary theorems may be critical for others

## Decision Outcome

**Adopt Option 4: Zero-Tolerance for `sorry` and Incomplete Proofs**

All theorems and lemmas must have complete, valid proofs before any commit. The use of `sorry` placeholders is strictly prohibited in the repository.

### Policy Definition

**Prohibited:**
- Use of `sorry` in any theorem or lemma proof
- Incomplete proofs (proofs that don't fully discharge all goals)
- Theorem statements without any proof
- Partial proof attempts that don't compile

**Required:**
- Every theorem and lemma must have a complete, compiling proof
- All proof goals must be discharged
- Proofs must be verified by Lean's kernel
- No outstanding proof obligations

### Enforcement Mechanisms

1. **Lean Compiler**: The Lean compiler will reject any code containing `sorry`
2. **Pre-commit Hooks**: Automated detection of `sorry` before commit
3. **CI Pipeline**: GitLab CI and Jenkins will fail builds if `sorry` is detected
4. **Code Review Guidelines**: Reviewers must reject any PR containing `sorry`
5. **Linting Rules**: Static analysis to identify potential violations
6. **Documentation**: Clear guidelines in contribution documentation

### Exception Process

In exceptional circumstances where a proof cannot be completed:
1. Create a GitHub issue documenting the theorem and why it cannot be proved
2. Do not commit the theorem statement without proof
3. Discuss with the team to determine if the theorem is necessary or if the specification should be adjusted
4. If the theorem is essential, work on completing the proof before committing

## Positive Consequences

1. **Guaranteed Correctness**: All theorems are mathematically verified
2. **Trustworthiness**: Users can trust that specifications are correct
3. **Code Quality**: High standard for all code in the repository
4. **Maintainability**: Future developers have complete proofs to understand specifications
5. **CI/CD Reliability**: Automated builds provide strong guarantees
6. **Educational Value**: Complete proofs serve as examples for learning
7. **Security**: Security-related theorems are fully verified
8. **No Technical Debt**: No accumulation of incomplete work

## Negative Consequences

1. **Slower Development**: Proofs must be completed before committing, potentially slowing iteration
2. **Higher Barrier to Entry**: Contributors must be comfortable writing complete proofs
3. **Potential for Abandonment**: Difficult proofs may lead to abandoning valuable theorems
4. **Pressure to Simplify**: May encourage simplifying specifications to make proofs easier
5. **Time Investment**: Requires significant time investment in proof development

## Related ADRs

- **ADR-001: Three-File Module Pattern** - Lemmas.lean files contain complete proofs
- **ADR-002: Zero-Tolerance for Commented-Out Code** - Complements this policy by ensuring no commented-out proofs
- **ADR-007: CI/CD Integration** - Describes how the complete proof requirement is enforced in CI pipelines

## Implementation Notes

### Detection

The following patterns are detected as violations:

```lean
-- Prohibited
theorem example_theorem : P :=
  sorry

-- Prohibited
lemma example_lemma : P :=
  by
  -- incomplete proof
  sorry

-- Prohibited
theorem incomplete : P :=
  by
  apply some_lemma
  -- goal not discharged
```

### Allowed Patterns

```lean
-- Required
theorem complete_theorem : P :=
  by
  -- complete proof that discharges all goals
  apply some_lemma
  exact hypothesis

-- Required
lemma complete_lemma : P → Q :=
  by
  intro h
  -- complete proof
  exact (some_construction h)
```

### Proof Strategies

When facing difficult proofs:
1. Break down the theorem into smaller lemmas
2. Use automation tools (aesop, batteries) where appropriate
3. Consult with team members for proof strategies
4. Consider if the theorem statement can be simplified
5. Verify that all necessary assumptions are included

### Documentation

Each theorem and lemma should include:
- Clear statement of what is being proved
- Explanation of the proof strategy (if non-obvious)
- References to related theorems or lemmas
- Comments explaining non-trivial proof steps

## Examples

### Prohibited (Incomplete Proof)

```lean
-- This is NOT allowed
theorem memory_safety : ∀ p, is_safe p :=
  by
  -- TODO: complete this proof
  sorry
```

### Required (Complete Proof)

```lean
-- This IS required
theorem memory_safety : ∀ p, is_safe p :=
  by
  intro p
  unfold is_safe
  -- complete proof that discharges all goals
  apply safe_allocation
  exact p.allocated
  apply safe_access
  exact p.in_bounds
```

## References

- [Specification Validation Checklist](../../docs/SPECIFICATION_VALIDATION_CHECKLIST.md)
- [Pre-commit Configuration](../../.pre-commit-config.yaml)
- [GitLab CI Configuration](../../.gitlab-ci.yml)
- [Lean 4 Documentation on Proofs](https://leanprover.github.io/lean4/doc/proofs.html)
