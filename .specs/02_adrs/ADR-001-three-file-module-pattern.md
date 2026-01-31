# ADR-001: Three-File Module Pattern

## Status
**Accepted**

## Context

The Morph language Lean validation project involves rewriting approximately 40+ specification modules that were originally authored by undergraduate students. Analysis of the existing codebase revealed significant structural and quality issues:

1. **Monolithic Files**: Original specifications mixed definitions, theorems, proofs, and examples in single large files, making them difficult to navigate and understand.
2. **Poor Separation of Concerns**: Core type definitions were interspersed with auxiliary lemmas and example usage, obscuring the primary specification content.
3. **Difficult Review Process**: Reviewers had to scan through entire files to locate specific components, increasing cognitive load and review time.
4. **Limited Reusability**: Examples and lemmas were tightly coupled with specifications, preventing independent use or testing.

The project requires a structured approach that supports:
- Clear separation between specification content, mathematical proofs, and educational examples
- Efficient code review and validation workflows
- Independent compilation and testing of different components
- Scalability to 40+ modules across multiple domains

## Decision Drivers

1. **Maintainability**: Code should be easy to understand, modify, and extend
2. **Reviewability**: Reviewers should be able to quickly locate and verify specific components
3. **Testability**: Specifications, lemmas, and examples should be independently testable
4. **Educational Value**: Examples should serve as clear documentation without cluttering core specifications
5. **Scalability**: Pattern must work consistently across 40+ modules

## Considered Options

### Option 1: Single File with Sections
- Keep all content in one file but use clear section markers
- **Pros**: Simpler file structure, fewer files to manage
- **Cons**: Still monolithic, sections don't enforce separation, compilation still requires entire file

### Option 2: Two-File Pattern (Spec + Proofs)
- Separate specifications into `Spec.lean` and combine lemmas/examples in `Proofs.lean`
- **Pros**: Better than single file, separates core from auxiliary content
- **Cons**: Examples mixed with proofs, examples still clutter proof files

### Option 3: Three-File Pattern (Spec + Lemmas + Examples)
- `Spec.lean`: Core type definitions, axioms, and theorem statements
- `Lemmas.lean`: Mathematical lemmas and their proofs
- `Examples.lean`: Concrete examples, usage demonstrations, and test cases
- **Pros**: Clear separation of concerns, independent compilation, optimal for review and testing
- **Cons**: More files to manage, requires coordination of imports

### Option 4: Four-File Pattern (Spec + Lemmas + Proofs + Examples)
- Further separate theorem statements from their proofs
- **Pros**: Maximum separation
- **Cons**: Overkill for most modules, introduces coordination complexity, theorem statements often closely tied to proofs

## Decision Outcome

**Adopt Option 3: Three-File Module Pattern**

Each specification module will be organized into three files:

```
Morph/Specs/[ModuleName]/
├── Spec.lean      # Core definitions, axioms, theorem statements
├── Lemmas.lean    # Mathematical lemmas and proofs
└── Examples.lean  # Concrete examples and usage demonstrations
```

### File Responsibilities

**Spec.lean** contains:
- Type definitions and structures
- Function signatures and axioms
- Theorem statements (declarations only, no proofs)
- Import statements for dependencies
- Module-level documentation

**Lemmas.lean** contains:
- Lemma statements and their complete proofs
- Helper theorems used in main proofs
- Mathematical derivations
- Imports from `Spec.lean`

**Examples.lean** contains:
- Concrete instantiations of types
- Example computations and their expected results
- Usage demonstrations
- Test cases
- Imports from `Spec.lean` and optionally `Lemmas.lean`

## Positive Consequences

1. **Improved Navigation**: Reviewers can quickly locate specifications, proofs, or examples without scanning monolithic files
2. **Independent Compilation**: Each file can be compiled separately, enabling faster iteration and targeted testing
3. **Clear Separation of Concerns**: Core specifications remain uncluttered by auxiliary content
4. **Enhanced Educational Value**: Examples serve as standalone documentation for understanding module behavior
5. **Parallel Development**: Different team members can work on different files without constant merge conflicts
6. **Easier Code Review**: Reviewers can focus on specific aspects (specifications, proofs, or examples) in isolation
7. **Better Version Control**: Changes to examples don't create noise in specification diffs
8. **Scalability**: Pattern scales consistently across all 40+ modules

## Negative Consequences

1. **Increased File Count**: Three files per module instead of one, increasing repository size
2. **Import Coordination**: Care must be taken to manage import dependencies between files
3. **Initial Learning Curve**: Team members must understand and follow the pattern consistently
4. **Potential for Duplication**: Some content may need to be referenced across multiple files
5. **Tooling Considerations**: Some Lean tools may assume single-file modules

## Related ADRs

- **ADR-005: Domain-Based Module Organization** - Describes how modules are grouped by domain
- **ADR-006: Complete Proof Requirement** - Specifies that all proofs in Lemmas.lean must be complete
- **ADR-007: CI/CD Integration** - Describes how the three-file pattern is validated in CI pipelines

## Implementation Notes

1. Each module directory must contain all three files, even if some are minimal
2. `Spec.lean` imports only necessary dependencies, not Lemmas or Examples
3. `Lemmas.lean` imports from `Spec.lean` in the same module
4. `Examples.lean` imports from both `Spec.lean` and `Lemmas.lean` as needed
5. File naming must exactly match the pattern: `Spec.lean`, `Lemmas.lean`, `Examples.lean`
6. Pre-commit hooks will verify the three-file structure exists for each module

## References

- [Specification Convention](../../docs/conventions/specification_convention.md)
- [File Naming Structure Convention](../../docs/conventions/file_naming_structure_convention.md)
- [Specification Validation Checklist](../../docs/SPECIFICATION_VALIDATION_CHECKLIST.md)
