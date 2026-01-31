# ADR-004: Lake Build System

## Status
**Accepted**

## Context

The Morph language Lean validation project is a large-scale formal verification project with 40+ specification modules. The project requires:

1. **Dependency Management**: Managing dependencies on mathlib4, aesop, batteries, and other Lean packages
2. **Build Automation**: Compiling all Lean files efficiently, including incremental builds
3. **Reproducible Builds**: Ensuring consistent builds across different environments
4. **CI/CD Integration**: Supporting automated builds in GitLab CI and Jenkins
5. **Package Distribution**: Potential need to distribute the Morph specification as a package
6. **Multi-file Organization**: Supporting the three-file module pattern (Spec.lean, Lemmas.lean, Examples.lean)

The project already uses Lake (Lean's package manager and build tool) as evidenced by the presence of `lakefile.lean`, `lakefile.toml`, and `lake-manifest.json` files. This ADR documents the decision to continue using Lake and the rationale behind it.

## Decision Drivers

1. **Lean Integration**: Must integrate seamlessly with Lean 4's toolchain
2. **Performance**: Fast incremental builds for large projects
3. **Dependency Management**: Reliable management of external Lean packages
4. **Reproducibility**: Consistent builds across different machines
5. **CI/CD Support**: Easy integration with GitLab CI and Jenkins
6. **Extensibility**: Ability to customize build targets and tasks
7. **Community Support**: Active development and community adoption
8. **Documentation**: Good documentation and examples

## Considered Options

### Option 1: Lake (Current Choice)
- Lean 4's official package manager and build system
- **Pros**: Native Lean integration, active development, good performance, supports Lean-specific features, well-documented, standard in Lean community
- **Cons**: Newer than some alternatives, learning curve for custom tasks

### Option 2: Make
- Traditional Unix build tool
- **Pros**: Ubiquitous, well-understood, highly flexible
- **Cons**: Poor Lean integration, manual dependency management, no package management, verbose configuration, doesn't understand Lean's module system

### Option 3: CMake
- Cross-platform build system generator
- **Pros**: Cross-platform, widely used, good IDE integration
- **Cons**: Poor Lean integration, overkill for Lean projects, no package management, complex configuration

### Option 4: Custom Build Script
- Write a custom build script in Python, Bash, or Lean itself
- **Pros**: Complete control over build process
- **Cons**: Reinventing the wheel, maintenance burden, no community support, likely to have bugs

### Option 5: Lean 3's leanpkg
- Package manager for Lean 3
- **Pros**: Familiar to Lean 3 users
- **Cons**: Not compatible with Lean 4, deprecated, no longer maintained

## Decision Outcome

**Adopt Option 1: Lake Build System**

Lake is Lean 4's official package manager and build system, designed specifically for Lean projects. It provides:

1. **Native Lean Integration**: Deep understanding of Lean's module system and compilation process
2. **Package Management**: Automatic fetching and caching of dependencies (mathlib4, aesop, batteries)
3. **Incremental Builds**: Efficient recompilation of only changed files
4. **Reproducible Builds**: Version pinning via `lake-manifest.json`
5. **Extensibility**: Custom build targets and tasks via `lakefile.lean`
6. **CI/CD Integration**: Easy integration with GitLab CI and Jenkins
7. **Community Standard**: Widely used in the Lean community, ensuring compatibility

### Configuration Files

The project uses three Lake configuration files:

1. **`lean-toolchain`**: Pins Lean 4 version (v4.10.0)
2. **`lakefile.toml`**: Package metadata and dependencies
3. **`lakefile.lean`**: Custom build targets and tasks
4. **`lake-manifest.json`**: Lock file for dependency versions

### Build Targets

Lake provides several built-in targets:

- `lake build`: Build all targets in the project
- `lake build <target>`: Build a specific target
- `lake run <executable>`: Run an executable target
- `lake test`: Run test targets
- `lake clean`: Clean build artifacts
- `lake update`: Update dependencies

## Positive Consequences

1. **Standard Tooling**: Using Lake aligns with Lean 4 best practices
2. **Efficient Builds**: Incremental compilation reduces build time during development
3. **Dependency Management**: Automatic handling of mathlib4, aesop, and batteries
4. **Reproducible Builds**: Lock file ensures consistent builds across environments
5. **CI/CD Integration**: Simple integration with GitLab CI and Jenkins pipelines
6. **Extensibility**: Custom build tasks can be added via `lakefile.lean`
7. **Community Support**: Access to community knowledge and examples
8. **Lean-Specific Features**: Support for Lean-specific build requirements (e.g., olean caching)
9. **Documentation**: Well-documented with examples and tutorials

## Negative Consequences

1. **Learning Curve**: Team members must learn Lake's configuration and commands
2. **Newer Tool**: Lake is relatively new, so some edge cases may be less well-documented
3. **Custom Task Complexity**: Writing complex custom tasks in `lakefile.lean` can be challenging
4. **Performance**: For very large projects, Lake's performance may need optimization
5. **Dependency on Lean**: Lake is tied to Lean 4, limiting its use outside Lean projects

## Related ADRs

- **ADR-003: Lean 4 with mathlib4** - Describes the Lean 4 version and dependencies managed by Lake
- **ADR-007: CI/CD Integration** - Describes how Lake is integrated with GitLab CI and Jenkins

## Implementation Notes

### Package Configuration (lakefile.toml)

```toml
[package]
name = "Morph"
version = "0.1.0"
lean_version = "leanprover/lean4:v4.10.0"

[dependencies]
mathlib = { git = "https://github.com/leanprover-community/mathlib4", rev = "v4.10.0" }
aesop = { git = "https://github.com/JLimperg/aesop", rev = "v4.10.0" }
batteries = { git = "https://github.com/leanprover-community/batteries", rev = "v4.10.0" }
```

### Custom Build Tasks (lakefile.lean)

The `lakefile.lean` can define custom build targets, such as:

- Building specific modules or groups of modules
- Running custom validation scripts
- Generating documentation
- Running example files

### Build Artifacts

Lake generates build artifacts in the `.lake/` directory:

- **`.lake/build/`**: Compiled `.olean` files
- **`.lake/packages/`**: Downloaded dependencies
- **`.lake/lib/`**: Library files for executables

### CI/CD Integration

GitLab CI and Jenkins use Lake commands:

```yaml
# GitLab CI example
build:
  script:
    - lake build
```

```groovy
// Jenkins example
stage('Build') {
    steps {
        sh 'lake build'
    }
}
```

### Development Workflow

1. **Initial Setup**: Run `lake update` to fetch dependencies
2. **Incremental Builds**: Run `lake build` to compile changes
3. **Clean Builds**: Run `lake clean && lake build` for a full rebuild
4. **Dependency Updates**: Run `lake update` to update dependencies

## References

- [Lake Documentation](https://github.com/leanprover/lean4/blob/master/doc/lake.md)
- [Lake Configuration Guide](https://github.com/leanprover/lean4/blob/master/doc/lake.md#configuration)
- [Lean 4 Package Development](https://leanprover.github.io/lean4/doc/setup.html)
- [lakefile.lean](../../lakefile.lean)
- [lakefile.toml](../../lakefile.toml)
- [lake-manifest.json](../../lake-manifest.json)
