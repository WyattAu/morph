# ADR-005: Domain-Based Module Organization

## Status
**Accepted**

## Context

The Morph language Lean validation project involves formalizing approximately 40+ specification modules covering diverse aspects of the Morph programming language. These modules include:

- Type systems and algebraic structures
- Memory models and semantics
- Concurrency and process calculi
- Security properties and access control
- Compiler optimizations and transformations
- Mathematical foundations and logic

The original undergraduate codebase had poor organization, with modules scattered without clear categorization. This made it difficult to:
- Locate relevant specifications
- Understand relationships between modules
- Navigate the codebase efficiently
- Identify dependencies between modules
- Assign ownership and responsibility for modules

As the project scales, a systematic organization scheme is essential for maintainability, discoverability, and effective collaboration.

## Decision Drivers

1. **Discoverability**: Easy to find modules related to specific domains
2. **Maintainability**: Clear structure supports long-term maintenance
3. **Logical Grouping**: Related modules should be co-located
4. **Dependency Management**: Clear understanding of module dependencies
5. **Team Organization**: Supports assignment of domain experts to specific areas
6. **Scalability**: Organization scheme must accommodate future growth
7. **Documentation**: Structure should be self-documenting
8. **Build Optimization**: Enables selective building of domains

## Considered Options

### Option 1: Alphabetical Organization
- Organize modules alphabetically by name
- **Pros**: Simple, predictable, no ambiguity
- **Cons**: Doesn't reflect logical relationships, difficult to find related modules, no semantic grouping

### Option 2: Layer-Based Organization
- Organize by abstraction level (foundations → core → applications)
- **Pros**: Reflects dependency hierarchy, clear build order
- **Cons**: Many modules span multiple layers, artificial categorization, difficult to maintain

### Option 3: Domain-Based Organization
- Group modules by semantic domain (Memory, Concurrency, Security, etc.)
- **Pros**: Logical grouping, easy to find related modules, supports domain expertise assignment, self-documenting
- **Cons**: Some modules may span multiple domains, requires clear domain definitions

### Option 4: Flat Organization
- All modules in a single directory
- **Pros**: Simplest structure, no nesting
- **Cons**: Doesn't scale, difficult to navigate, no logical grouping

### Option 5: Tag-Based Organization
- Use tags or metadata to categorize modules, keep flat structure
- **Pros**: Flexible, modules can belong to multiple categories
- **Cons**: Requires tooling support, not self-documenting, harder to navigate

## Decision Outcome

**Adopt Option 3: Domain-Based Organization**

Modules are organized into semantic domains within the `Morph/Specs/` directory. Each domain contains related specification modules that address a specific aspect of the Morph language.

### Domain Structure

```
Morph/Specs/
├── Core/              # Core language foundations
│   ├── MorphLanguage/
│   ├── LexicalStructureSyntax/
│   └── ScopingLambdaCalculus/
├── Memory/            # Memory models and semantics
│   ├── MemoryModel/
│   ├── MemoryAffineLogic/
│   └── MemoryAcyclicity/
├── Concurrency/       # Concurrency and parallelism
│   ├── ConcurrencyProcessAlgebra/
│   ├── LayeredConcurrency/
│   ├── SchedulerRandomizedStealing/
│   └── SchedulingModes/
├── Security/          # Security properties and access control
│   ├── SecurityFlow/
│   ├── SecurityOCap/
│   └── InfrastructureSafetyContracts/
├── Compilation/       # Compiler transformations and optimizations
│   ├── BackendTiling/
│   ├── DualOptimization/
│   └── DialectProjection/
├── Algebra/           # Algebraic structures and mathematics
│   ├── AbiAlignmentAlgebra/
│   ├── AbiDataRefinement/
│   ├── BuildLattice/
│   └── Maths/
├── Logic/             # Logical foundations
│   ├── LicenseDeonticLogic/
│   └── MonadicEffect/
├── Infrastructure/    # Infrastructure and tooling
│   ├── ModuleSystem/
│   ├── ModuleExistential/
│   └── LinkerLogic/
├── Execution/         # Execution models and semantics
│   ├── ExecutionModel/
│   └── DependencySat/
├── Storage/           # Storage and data structures
│   └── StorageDAWG/
├── Licensing/         # Licensing and compliance
│   ├── Licensing/
│   └── Financial/
└── Meta/              # Meta-specifications and utilities
    ├── GLOSSARY/
    ├── README/
    ├── ASTGraph/
    └── CommonTypes/
```

### Domain Definitions

**Core**: Fundamental language definitions, syntax, and scoping
**Memory**: Memory models, allocation, and memory safety
**Concurrency**: Process calculi, scheduling, and parallel execution
**Security**: Type-based security, access control, and safety contracts
**Compilation**: Compiler passes, optimizations, and code generation
**Algebra**: Algebraic structures, lattices, and mathematical foundations
**Logic**: Logical systems, modal logic, and effect systems
**Infrastructure**: Module systems, linking, and build infrastructure
**Execution**: Operational semantics, evaluation, and dependency analysis
**Storage**: Data structures, storage models, and representations
**Licensing**: Licensing models, compliance, and financial aspects
**Meta**: Glossaries, common types, and meta-specifications

## Positive Consequences

1. **Improved Discoverability**: Easy to locate modules related to specific domains
2. **Logical Grouping**: Related modules are co-located, reflecting semantic relationships
3. **Domain Expertise**: Enables assignment of domain experts to specific areas
4. **Self-Documenting**: Directory structure provides immediate insight into project organization
5. **Scalability**: Clear structure accommodates future growth and new modules
6. **Selective Building**: Can build and test specific domains independently
7. **Clear Ownership**: Facilitates assignment of responsibility for domains
8. **Reduced Cognitive Load**: Developers can focus on specific domains without distraction
9. **Better Documentation**: Domain-specific documentation can be co-located with modules

## Negative Consequences

1. **Cross-Domain Dependencies**: Modules in different domains may have dependencies, requiring careful management
2. **Ambiguous Classification**: Some modules may not clearly fit into a single domain
3. **Directory Depth**: Increased nesting may make file paths longer
4. **Refactoring Overhead**: Moving modules between domains may be required as understanding evolves
5. **Learning Curve**: New contributors must learn the domain classification scheme
6. **Potential for Silos**: May encourage isolation between domain teams

## Related ADRs

- **ADR-001: Three-File Module Pattern** - Each module within a domain uses the three-file pattern
- **ADR-006: Complete Proof Requirement** - Applies to all modules across all domains

## Implementation Notes

### Module Naming

Each module directory name should:
- Use PascalCase
- Be descriptive and self-explanatory
- Avoid abbreviations unless widely understood
- Reflect the module's primary purpose

### Cross-Domain Imports

When a module in one domain needs to import from another domain:
- Use full import paths (e.g., `import Morph.Specs.Memory.MemoryModel`)
- Document the reason for cross-domain imports
- Minimize cross-domain dependencies where possible
- Consider if a module should be moved if it has many cross-domain dependencies

### Domain Documentation

Each domain directory should contain a `README.md` file explaining:
- The domain's purpose and scope
- List of modules in the domain
- Key dependencies on other domains
- Domain-specific conventions or guidelines

### Build Configuration

Lake can be configured to support domain-specific build targets:

```lean
-- lakefile.lean example
def buildDomain (domainName : String) : ScriptM Bool := do
  let modules ← findModulesInDomain domainName
  buildModules modules
```

### Module Index

A central index (e.g., `Morph/Specs/INDEX.md`) should maintain:
- List of all domains
- Modules in each domain
- Cross-domain dependency graph
- Module ownership information

## References

- [File Naming Structure Convention](../../docs/conventions/file_naming_structure_convention.md)
- [Specification Convention](../../docs/conventions/specification_convention.md)
- [Morph/Specs Directory](../../Morph/Specs/)
