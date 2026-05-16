# Specification Inconsistencies

This document catalogs terminology inconsistencies, naming conflicts, and formatting deviations found across the Morph specification suite.

---

## Terminology Conflicts

*Referenced by:* `spec/conventions/terminology_standardization_spec.md`

### File Naming Inconsistencies

| Correct Name | Incorrect Name | Location | Status |
|-------------|---------------|----------|--------|
| `lexical_structure_syntax_spec.md` | `lexical_strcutre_syntax_spec.md` | Legacy references | Fixed |

### Naming Convention Violations

| Category | Violation | Correct Form | Status |
|----------|-----------|-------------|--------|
| Type names | Inconsistent snake_case vs PascalCase | PascalCase for types | Documented in terminology spec |
| Function names | Inconsistent PascalCase vs camelCase | camelCase for functions | Documented in terminology spec |
| File names | Inconsistent conventions and typos | snake_case, no typos | Documented in terminology spec |

---

## Standardization Requirements

*Referenced by:* `spec/conventions/terminology_standardization_spec.md`

All specifications must follow the canonical naming conventions defined in `spec/conventions/terminology_standardization_spec.md`. Key rules:

1. **File names**: snake_case, no abbreviations except well-known ones (AST, LSP, GC)
2. **Type names**: PascalCase (e.g., `MemoryBlock`, `TypeEnv`)
3. **Function names**: camelCase (e.g., `allocateBlock`, `lookupType`)
4. **Constants**: UPPER_SNAKE_CASE (e.g., `MAX_BLOCK_SIZE`)
5. **Spec identifiers**: PREFIX-NUMBER format (e.g., `UDF-REQ-001`, `SSUS-INV-002`)

See `spec/conventions/version_compatibility_spec.md` for version compatibility rules governing these conventions.
