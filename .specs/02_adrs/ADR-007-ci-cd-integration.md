# ADR-007: CI/CD Integration

## Status
**Accepted**

## Context

The Morph language Lean validation project is a large-scale formal verification effort with 40+ specification modules. The project requires:

1. **Automated Quality Assurance**: Continuous validation of code quality and correctness
2. **Proof Verification**: Automated checking that proofs are complete (no `sorry` placeholders; 3 known exceptions in Preservation.lean)
3. **Code Style Enforcement**: Consistent coding standards across all modules
4. **Build Validation**: Ensuring all Lean files compile successfully
5. **Pre-commit Validation**: Early detection of issues before commits
6. **Merge Protection**: Preventing problematic code from being merged to main branches
7. **Documentation Generation**: Automated documentation updates
8. **Performance Monitoring**: Tracking build times and resource usage

The project already uses GitLab CI (`.gitlab-ci.yml`) and Jenkins (`Jenkinsfile`) as evidenced by the presence of these configuration files. This ADR documents the decision to use both CI systems and the rationale behind this dual approach.

## Decision Drivers

1. **Quality Assurance**: Automated validation of code quality and correctness
2. **Proof Completeness**: Ensuring no `sorry` placeholders or incomplete proofs (3 known exceptions in Preservation.lean)
3. **Code Style**: Enforcing consistent coding standards
4. **Build Reliability**: Ensuring all code compiles successfully
5. **Early Detection**: Catching issues as early as possible (pre-commit > CI > merge)
5. **Team Workflow**: Supporting both GitLab-based and Jenkins-based workflows
6. **Performance**: Efficient CI pipeline execution
7. **Flexibility**: Supporting different deployment environments
8. **Scalability**: CI system must handle 40+ modules efficiently

## Considered Options

### Option 1: GitLab CI Only
- Use only GitLab's built-in CI/CD system
- **Pros**: Native GitLab integration, good UI, free for public projects, well-documented
- **Cons**: Limited to GitLab, may not meet all deployment needs, less flexible for complex workflows

### Option 2: Jenkins Only
- Use only Jenkins for CI/CD
- **Pros**: Highly flexible, extensive plugin ecosystem, industry-standard, works with any Git host
- **Cons**: Requires separate infrastructure, more complex setup, no native GitLab integration

### Option 3: GitHub Actions Only
- Use GitHub Actions (would require migrating from GitLab)
- **Pros**: Native GitHub integration, good marketplace, modern UI
- **Cons**: Requires migration from GitLab, not currently using GitHub

### Option 4: GitLab CI + Jenkins (Dual System)
- Use both GitLab CI and Jenkins, each for different purposes
- **Pros**: Best of both worlds, GitLab CI for quick checks, Jenkins for complex workflows, supports diverse team preferences, redundancy
- **Cons**: More complex to maintain, potential for duplication, higher infrastructure cost

### Option 5: No CI/CD (Manual Validation)
- Rely on manual validation and testing
- **Pros**: Simplest approach, no infrastructure needed
- **Cons**: No automated quality assurance, prone to human error, doesn't scale

## Decision Outcome

**Adopt Option 4: GitLab CI + Jenkins (Dual System)**

The project uses both GitLab CI and Jenkins, each serving complementary purposes:

### GitLab CI Responsibilities

GitLab CI handles lightweight, fast checks that run on every commit:

1. **Pre-commit Hooks Validation**: Verify that pre-commit hooks are properly configured
2. **Linting**: Run code style checks (e.g., flake8, black for Python files if any)
3. **Lean Compilation**: Quick compilation of changed Lean files
4. **Proof Completeness Check**: Detect `sorry` placeholders and incomplete proofs
5. **Commented-Out Code Detection**: Enforce zero-tolerance policy for commented-out code
6. **Three-File Pattern Validation**: Verify each module has Spec.lean, Lemmas.lean, Examples.lean
7. **Documentation Checks**: Validate documentation formatting and completeness

### Jenkins Responsibilities

Jenkins handles heavier, less frequent tasks:

1. **Full Build**: Complete compilation of all Lean files in the project
2. **Proof Verification**: Comprehensive proof checking with all dependencies
3. **Documentation Generation**: Generate and deploy documentation
4. **Performance Benchmarking**: Track build times and resource usage
5. **Security Scanning**: Run security analysis tools
6. **Integration Tests**: Run comprehensive test suites
7. **Artifact Publishing**: Publish build artifacts and packages
8. **Deployment**: Handle deployment to staging/production environments

### Pipeline Triggers

**GitLab CI**: Runs on every push and merge request
**Jenkins**: Runs on schedule (e.g., nightly) and on merge to main branches

### Pre-commit Hooks

Pre-commit hooks (configured in `.pre-commit-config.yaml`) provide the first line of defense:

1. **Fast Checks**: Run before commits, providing immediate feedback
2. **Local Execution**: Developers get feedback without pushing to remote
3. **Minimal Overhead**: Designed to be fast and non-intrusive
4. **Configurable**: Developers can skip hooks with `--no-verify` (discouraged)

## Positive Consequences

1. **Early Detection**: Issues caught at multiple stages (pre-commit, GitLab CI, Jenkins)
2. **Quality Assurance**: Multiple layers of validation ensure high code quality
3. **Proof Completeness**: Automated detection of `sorry` and incomplete proofs
4. **Code Style**: Consistent coding standards across all modules
5. **Flexibility**: Supports diverse team workflows and preferences
6. **Redundancy**: Dual CI systems provide backup and resilience
7. **Scalability**: Efficient handling of 40+ modules
8. **Documentation**: Automated documentation generation and updates
9. **Performance Monitoring**: Tracking build times and resource usage
10. **Merge Protection**: Prevents problematic code from being merged

## Negative Consequences

1. **Complexity**: Maintaining two CI systems increases complexity
2. **Infrastructure Cost**: Running both GitLab CI and Jenkins requires more resources
3. **Duplication**: Some checks may be duplicated between systems
4. **Learning Curve**: Team members must understand both systems
5. **Configuration Overhead**: More configuration files to maintain
6. **Potential Conflicts**: Differences between CI systems may cause confusion
7. **Slower Feedback**: Jenkins runs less frequently, delaying some feedback

## Related ADRs

- **ADR-002: Zero-Tolerance for Commented-Out Code** - Enforced by CI/CD pipelines
- **ADR-006: Complete Proof Requirement** - Enforced by CI/CD pipelines
- **ADR-004: Lake Build System** - Used by CI/CD pipelines for building Lean files

## Implementation Notes

### GitLab CI Configuration (.gitlab-ci.yml)

```yaml
stages:
  - lint
  - build
  - test

# Pre-commit validation
lint:
  stage: lint
  script:
    - pre-commit run --all-files
  rules:
    - if: '$CI_PIPELINE_SOURCE == "merge_request_event"'

# Lean compilation
build:
  stage: build
  script:
    - lake build
  rules:
    - if: '$CI_PIPELINE_SOURCE == "merge_request_event"'
    - if: '$CI_COMMIT_BRANCH == "main"'

# Proof completeness check
check_proofs:
  stage: test
  script:
    - ! grep -r "sorry" Morph/Specs/
  rules:
    - if: '$CI_PIPELINE_SOURCE == "merge_request_event"'
```

### Jenkins Configuration (Jenkinsfile)

```groovy
pipeline {
    agent any
    
    stages {
        stage('Full Build') {
            steps {
                sh 'lake clean && lake build'
            }
        }
        
        stage('Documentation') {
            steps {
                sh './scripts/generate_docs.sh'
            }
        }
        
        stage('Publish') {
            steps {
                sh './scripts/publish_artifacts.sh'
            }
        }
    }
    
    triggers {
        cron('H 0 * * *')  // Daily at midnight
    }
}
```

### Pre-commit Configuration (.pre-commit-config.yaml)

```yaml
repos:
  - repo: local
    hooks:
      - id: check-sorry
        name: Check for sorry placeholders
        entry: '! grep -r "sorry" Morph/Specs/'
        language: system
      - id: check-commented-code
        name: Check for commented-out code
        entry: './scripts/check_commented_code.sh'
        language: script
      - id: check-three-file-pattern
        name: Check three-file module pattern
        entry: './scripts/check_three_file_pattern.sh'
        language: script
```

### CI/CD Workflow

1. **Developer commits code**: Pre-commit hooks run locally
2. **Push to GitLab**: GitLab CI runs on every push
3. **Merge Request**: GitLab CI runs additional checks
4. **Merge to main**: Both GitLab CI and Jenkins run comprehensive checks
5. **Scheduled**: Jenkins runs nightly builds and documentation generation

### Failure Handling

- **Pre-commit failure**: Commit is blocked, developer must fix issues
- **GitLab CI failure**: Merge request is blocked, cannot merge until fixed
- **Jenkins failure**: Team is notified, issues must be addressed before next release

### Performance Optimization

- **Incremental Builds**: Lake's incremental compilation reduces build time
- **Caching**: GitLab CI and Jenkins cache dependencies and build artifacts
- **Parallel Execution**: Run checks in parallel where possible
- **Selective Builds**: Only build changed modules when possible

## References

- [GitLab CI Configuration](../../.gitlab-ci.yml)
- [Jenkins Configuration](../../Jenkinsfile)
- [Pre-commit Configuration](../../.pre-commit-config.yaml)
- [GitLab CI Documentation](https://docs.gitlab.com/ee/ci/)
- [Jenkins Documentation](https://www.jenkins.io/doc/)
- [Pre-commit Documentation](https://pre-commit.com/)
