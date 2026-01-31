# ADR-002: Zero-Tolerance for Commented-Out Code

## Status
**Accepted**

## Context

The Morph language Lean validation project involves rewriting approximately 40+ specification modules that were originally authored by undergraduate students. Analysis of the existing codebase revealed pervasive issues with commented-out code:

1. **Extensive Dead Code**: Many files contained large blocks of commented-out code, sometimes exceeding the amount of active code
2. **Unclear Intent**: Commented-out code lacked explanations of why it was disabled or whether it should be preserved
3. **Maintenance Burden**: Reviewers and maintainers had to mentally parse and ignore commented sections, increasing cognitive load
4. **Version Control Confusion**: Commented-out code obscured the actual history of changes, making diffs difficult to interpret
5. **Compilation Issues**: Some commented-out code contained syntax errors that would prevent compilation if uncommented, creating uncertainty about its validity
6. **Security Risks**: In security-related modules, commented-out code could potentially contain sensitive logic or backdoors
7. **Proof Obfuscation**: In formal verification, commented-out proofs made it difficult to understand the actual proof strategy

Specific examples from the undergraduate codebase included:
- Entire theorem proofs commented out with no indication of why
- Alternative implementations left as comments without comparison
- Debugging statements and test code never removed
- Incomplete experiments and exploratory code abandoned in-place

The project requires a clean, maintainable codebase where every line of code serves a clear purpose and can be trusted as part of the formal specification.

## Decision Drivers

1. **Code Clarity**: Every line of code should be intentional and meaningful
2. **Reviewability**: Reviewers should not have to filter out irrelevant commented content
3. **Formal Correctness**: Formal specifications must be unambiguous and complete
4. **Version Control Best Practices**: Git should be the sole mechanism for preserving historical code
5. **Security**: No hidden or ambiguous code in security-critical modules
6. **Maintainability**: Future developers should not need to guess about commented code's purpose
7. **Compilation Reliability**: All code in the repository should compile successfully

## Considered Options

### Option 1: Allow Commented-Out Code with Documentation
- Permit commented-out code if accompanied by explanatory comments
- **Pros**: Preserves potentially useful code, allows for experimentation
- **Cons**: Still creates noise, documentation can become outdated, violates formal verification principles

### Option 2: Allow Temporary Commented-Out Code During Development
- Permit commented-out code only in feature branches, require removal before merge
- **Pros**: Allows experimentation during development
- **Cons**: Relies on developer discipline, difficult to enforce, can slip through review

### Option 3: Move Commented-Out Code to Separate Files
- Create `archive/` or `deprecated/` directories for old code
- **Pros**: Keeps main files clean, preserves potentially useful code
- **Cons**: Still creates maintenance burden, archived code becomes stale, version control already serves this purpose

### Option 4: Zero-Tolerance Policy with Git-Based History
- Prohibit all commented-out code blocks; rely on Git for historical preservation
- **Pros**: Clean codebase, clear intent, leverages version control properly, enforces discipline
- **Cons**: Requires cultural shift, developers must be comfortable with Git history

## Decision Outcome

**Adopt Option 4: Zero-Tolerance Policy with Git-Based History**

All commented-out code blocks are strictly prohibited in the repository. Historical code must be preserved through Git's version control system, not through comments.

### Policy Definition

**Prohibited:**
- Any block of code (3+ lines) that is commented out
- Commented-out function definitions, theorem statements, or proofs
- Commented-out imports or module declarations
- Large commented-out sections within active code

**Allowed:**
- Single-line comments explaining code (e.g., `-- This lemma is used in Theorem 5`)
- Inline comments clarifying complex logic
- TODO comments for future work
- Documentation comments (e.g., `/-- ... -/` in Lean)

### Enforcement Mechanisms

1. **Pre-commit Hooks**: Automated detection of commented-out code blocks before commit
2. **CI Pipeline Validation**: Fail builds if commented-out code blocks are detected
3. **Code Review Guidelines**: Reviewers must reject any PR containing commented-out code
4. **Linting Rules**: Static analysis to identify potential violations
5. **Documentation**: Clear guidelines in contribution documentation

### Developer Workflow

When developers need to remove or replace code:
1. Delete the code directly (do not comment it out)
2. Commit the deletion with a clear message explaining why
3. If code might be needed later, reference the commit hash in a TODO comment
4. Use Git branches for experimental code, not comments

## Positive Consequences

1. **Cleaner Codebase**: Every file contains only active, meaningful code
2. **Improved Reviewability**: Reviewers focus on actual changes, not noise
3. **Better Version Control**: Git history accurately reflects the evolution of the code
4. **Enhanced Security**: No hidden or ambiguous code in security-critical modules
5. **Formal Clarity**: Specifications are unambiguous and complete
6. **Reduced Cognitive Load**: Developers don't need to mentally filter out commented code
7. **Enforced Best Practices**: Encourages proper use of version control
8. **Faster Compilation**: No parsing of commented-out code blocks
9. **Better Documentation**: Comments serve only to explain, not to preserve

## Negative Consequences

1. **Cultural Adjustment**: Developers accustomed to commenting out code must change habits
2. **Git Proficiency Required**: All developers must be comfortable with Git history navigation
3. **Initial Friction**: Some developers may feel constrained during experimentation
4. **Learning Curve**: New contributors may need training on the policy
5. **Potential for Lost Work**: If developers don't commit experimental code before deletion

## Related ADRs

- **ADR-001: Three-File Module Pattern** - Complements clean separation by ensuring each file contains only relevant content
- **ADR-006: Complete Proof Requirement** - Ensures no incomplete proofs are left as commented-out placeholders
- **ADR-007: CI/CD Integration** - Describes how the zero-tolerance policy is enforced in CI pipelines

## Implementation Notes

1. **Detection Heuristics**: Commented-out code blocks are defined as 3+ consecutive lines of commented code (excluding documentation comments)
2. **Exceptions**: Documentation comments (`/-- ... -/` in Lean) are explicitly allowed
3. **Migration Strategy**: Existing commented-out code in the undergraduate codebase will be removed during the rewrite process
4. **Training**: Onboarding documentation will include examples of proper Git-based code preservation
5. **Tooling**: Pre-commit hooks will use pattern matching to detect violations

## Examples

### Prohibited
```lean
-- Old implementation that didn't work
-- theorem old_lemma : ∀ x, P x :=
--   by
--   -- incomplete proof
--   sorry

-- New implementation
theorem new_lemma : ∀ x, P x :=
  by
  -- complete proof
  ...
```

### Allowed
```lean
-- This lemma is a direct consequence of Theorem 3.2
theorem corollary_3_3 : ∀ x, P x → Q x :=
  by
  -- Apply Theorem 3.2 with the given hypothesis
  apply theorem_3_2
  ...
```

## References

- [Specification Convention](../../docs/conventions/specification_convention.md)
- [Pre-commit Configuration](../../.pre-commit-config.yaml)
- [GitLab CI Configuration](../../.gitlab-ci.yml)
