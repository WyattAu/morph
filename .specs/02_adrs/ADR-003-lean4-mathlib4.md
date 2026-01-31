# ADR-003: Lean 4 with mathlib4

## Status
**Accepted**

## Context

The Morph language Lean validation project requires a formal verification framework to specify and prove properties of a novel programming language. The project involves:

1. **Complex Mathematical Specifications**: 40+ modules covering algebraic structures, process calculi, memory models, concurrency, security, and more
2. **Proof Automation**: Need for automated theorem proving to handle complex proofs efficiently
3. **Type System Integration**: The Morph language itself has a sophisticated type system that needs formal specification
4. **Educational Component**: Specifications must be understandable to both researchers and students
5. **Long-term Maintainability**: The formalization must remain maintainable as the project evolves

The project originally used undergraduate-authored Lean files that suffered from quality issues. A robust, well-supported formal verification framework is essential for the rewrite.

## Decision Drivers

1. **Expressiveness**: Must support complex mathematical structures and type systems
2. **Automation**: Proof automation to reduce manual proof burden
3. **Ecosystem**: Strong library support for mathematical foundations
4. **Performance**: Efficient compilation and proof checking
5. **Community**: Active development and community support
6. **Tooling**: Good IDE support, documentation, and learning resources
7. **Stability**: Mature enough for production use
8. **Future-proofing**: Active development with clear roadmap

## Considered Options

### Option 1: Lean 3 with mathlib
- Use the previous version of Lean with its established mathlib library
- **Pros**: Mature, extensive documentation, many existing formalizations
- **Cons**: No longer actively developed, slower compilation, limited automation, being superseded by Lean 4

### Option 2: Coq with Mathematical Components
- Industry-standard proof assistant with extensive library support
- **Pros**: Very mature, extensive ecosystem, strong automation (SSReflect), widely used in academia
- **Cons**: Steeper learning curve, less modern type system, different syntax paradigm, slower compilation for large projects

### Option 3: Isabelle/HOL
- Higher-order logic theorem prover with strong automation
- **Pros**: Excellent automation (Sledgehammer), large library, strong industrial adoption
- **Cons**: Different logical foundation (HOL vs dependent type theory), less suitable for programming language metatheory, steeper learning curve

### Option 4: Lean 4 with mathlib4
- Latest version of Lean with redesigned kernel and improved performance
- **Pros**: Modern metaprogramming, excellent performance, growing ecosystem, strong automation (aesop, batteries), active development, good IDE support, extensible via user-defined tactics
- **Cons**: Newer than Lean 3 (though now mature), ecosystem still growing (but mathlib4 is comprehensive)

### Option 5: Agda
- Dependently typed functional programming language
- **Pros**: Very expressive type system, good for programming language theory
- **Cons**: Less automation, smaller ecosystem, more focused on programming than theorem proving

## Decision Outcome

**Adopt Option 4: Lean 4 v4.10.0 with mathlib4, aesop, and batteries**

### Technology Stack

- **Core**: Lean 4 v4.10.0 (pinned via `lean-toolchain`)
- **Standard Library**: mathlib4 (comprehensive mathematical library)
- **Proof Automation**: aesop (automated search for proofs)
- **Additional Tactics**: batteries (collection of useful tactics)
- **Build System**: Lake (Lean's package manager and build tool)

### Rationale

Lean 4 provides the optimal balance of expressiveness, automation, and ecosystem for this project:

1. **Performance**: Lean 4's redesigned kernel provides significantly faster compilation than Lean 3, essential for a project with 40+ modules
2. **Metaprogramming**: Lean 4's metaprogramming capabilities allow custom tactic development for domain-specific automation
3. **Automation**: aesop provides powerful automated proof search, reducing manual proof effort
4. **Ecosystem**: mathlib4 is comprehensive and actively maintained, covering most mathematical structures needed
5. **Type System**: Lean 4's dependent type theory is ideal for specifying programming language semantics and type systems
6. **Tooling**: Excellent VS Code integration with real-time type checking and proof state visualization
7. **Community**: Active development with regular releases and responsive community
8. **Documentation**: Growing documentation and tutorial resources

### Version Pinning

The project pins Lean 4 to v4.10.0 via the `lean-toolchain` file to ensure reproducible builds. This version is chosen because:
- Stable and well-tested
- Compatible with current versions of mathlib4, aesop, and batteries
- Includes all features needed for the project
- Has good performance characteristics

## Positive Consequences

1. **Fast Compilation**: Lean 4's performance enables rapid iteration during development
2. **Strong Automation**: aesop and batteries significantly reduce manual proof effort
3. **Comprehensive Library**: mathlib4 provides most mathematical structures needed, reducing development time
4. **Modern Type System**: Dependent types enable precise specification of Morph language semantics
5. **Excellent Tooling**: VS Code integration provides real-time feedback and proof state visualization
6. **Extensibility**: Custom tactics can be developed for domain-specific proof patterns
7. **Active Community**: Regular updates and responsive support for issues
8. **Future-proof**: Lean 4 is actively developed with a clear roadmap
9. **Educational Value**: Good documentation and tutorials support onboarding of new contributors

## Negative Consequences

1. **Learning Curve**: Team members must learn Lean 4, which may take time
2. **Version Sensitivity**: Pinning to v4.10.0 requires careful management when upgrading
3. **Ecosystem Maturity**: While growing, Lean 4's ecosystem is newer than Lean 3's
4. **Documentation Gaps**: Some advanced features may have limited documentation
5. **Tooling Dependencies**: Requires specific versions of mathlib4, aesop, and batteries
6. **Compilation Time**: Despite improvements, large projects still require significant compilation time
7. **Binary Size**: Compiled binaries can be large due to Lean's runtime

## Related ADRs

- **ADR-004: Lake Build System** - Describes how Lean 4 packages are built and managed
- **ADR-007: CI/CD Integration** - Describes how Lean 4 compilation is automated in CI pipelines

## Implementation Notes

1. **Version Management**: The `lean-toolchain` file pins Lean 4 to v4.10.0
2. **Dependency Management**: Lake manages dependencies on mathlib4, aesop, and batteries
3. **CI Configuration**: GitLab CI and Jenkins pipelines compile all Lean files to ensure correctness
4. **IDE Configuration**: VS Code workspace settings configure Lean 4 server settings
5. **Documentation**: Project documentation includes Lean 4 setup instructions and coding conventions

### Required Dependencies

```toml
[dependencies]
mathlib = { git = "https://github.com/leanprover-community/mathlib4", rev = "v4.10.0" }
aesop = { git = "https://github.com/JLimperg/aesop", rev = "v4.10.0" }
batteries = { git = "https://github.com/leanprover-community/batteries", rev = "v4.10.0" }
```

### Lean 4 Features Used

- **Dependent Types**: For precise specification of Morph language semantics
- **Metaprogramming**: For custom tactic development
- **Tactic Framework**: For structured proof development
- **Type Classes**: For organizing mathematical structures
- **Monads**: For effectful specifications (e.g., state, nondeterminism)

## References

- [Lean 4 Documentation](https://leanprover.github.io/lean4/doc/)
- [mathlib4 Documentation](https://leanprover-community.github.io/mathlib4_docs/)
- [aesop Documentation](https://github.com/JLimperg/aesop)
- [Lake Documentation](https://github.com/leanprover/lean4/blob/master/doc/lake.md)
- [Lean 4 v4.10.0 Release Notes](https://github.com/leanprover/lean4/releases/tag/v4.10.0)
