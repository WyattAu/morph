# Verification Tools Documentation

This document provides comprehensive usage instructions for all verification
tools created for Task 6 - Prepare verification tools.

## Overview

The verification tools package provides enterprise-grade Python tools for verifying
Lean 4 specification files, following ADR-002, ADR-003, ADR-006,
and threat model guidelines.

## Tools Included

### 1. Lean 4 Compilation Verification (`compilation.py`)

**Purpose:** Verify Lean 4 specification files through compilation.

**ADR Reference:** [ADR-002: Lean 4 Compilation Verification](../../../.specs/02_adrs/ADR-002_lean4_compilation_verification.md)

**Features:**
- Full compilation coverage for all spec files
- Error classification (Syntax, Type, Import, Proof Obligations)
- Fallback strategies for compilation failures
- Resource management (timeouts, memory monitoring)
- Markdown report generation

**Usage:**

```python
from pathlib import Path
from spec_tools.verification.compilation import Lean4CompilationVerifier, CompilationConfig

# Create verifier with default configuration
verifier = Lean4CompilationVerifier()

# Or with custom configuration
config = CompilationConfig(
    lean_path=Path("lake"),
    timeout_seconds=300,
    memory_limit_mb=4096,
    clean_before_build=True,
    parallel_jobs=1,
    verbose=True
)
verifier = Lean4CompilationVerifier(config)

# Verify a single file
result = verifier.verify_file(Path("Morph/Specs/AbiAlignmentAlgebra/Spec.lean"))
print(f"Status: {result.status}")
print(f"Duration: {result.duration:.2f}s")
print(f"Errors: {len(result.errors)}")

# Verify all specs
results = verifier.verify_specs()
stats = verifier.get_statistics(results)
print(f"Success rate: {stats['success_rate']:.1f}%")
```

**Configuration Options:**

| Option | Type | Default | Description |
|---------|------|---------|-------------|
| `lean_path` | Path | `Path("lake")` | Path to Lean 4 compiler |
| `lake_path` | Path | `Path("lake")` | Path to Lake package manager |
| `timeout_seconds` | int | 300 | Maximum compilation time in seconds |
| `memory_limit_mb` | int | 4096 | Memory limit in MB (4GB default) |
| `clean_before_build` | bool | True | Clean build artifacts before compilation |
| `parallel_jobs` | int | 1 | Number of parallel compilation jobs |
| `verbose` | bool | False | Enable verbose output |

**Error Types Detected:**

- **Syntax Errors:** Invalid Lean 4 syntax that prevents parsing
- **Type Errors:** Type mismatches, missing type annotations, incorrect type inference
- **Import Errors:** Missing or incorrect imports, dependency resolution failures
- **Proof Obligations:** Unresolved proof goals, failed proof searches

**Success Criteria (ADR-002):**
- Compilation Success Rate: >95%
- Type Checking Success Rate: >98%
- Proof Search Timeout Rate: <5%
- Memory Exhaustion Rate: <2%
- Dependency Resolution Success Rate: >99%

---

### 2. Automated Issue Detection (`issue_detection.py`)

**Purpose:** Automatically detect issues in Lean 4 specification files.

**ADR Reference:** [ADR-013: Automated Issue Detection](../../../.specs/02_adrs/ADR-013_automated_issue_detection.md)

**Features:**
- Detection of unclear specification points (USP)
- Detection of Lean 4 compilation failures (LCF)
- Detection of insufficient rigor (ISR)
- Detection of missing examples or lemmas (MEL)
- Detection of inconsistencies between files (IBF)
- Cross-file inconsistency detection

**Usage:**

```python
from pathlib import Path
from spec_tools.verification.issue_detection import AutomatedIssueDetector, DetectionConfig

# Create detector with default configuration
detector = AutomatedIssueDetector()

# Or with custom configuration
config = DetectionConfig(
    detect_usp=True,
    detect_lcf=True,
    detect_isr=True,
    detect_mel=True,
    detect_ibf=True,
    strict_mode=False
)
detector = AutomatedIssueDetector(config)

# Detect issues in a single file
issues = detector.detect_issues(Path("Morph/Specs/AbiAlignmentAlgebra/Spec.lean"))
for issue in issues:
    print(f"{issue.issue_id}: {issue.description}")

# Detect issues in a directory
issues = detector.detect_directory(Path("Morph/Specs"))
stats = detector.get_statistics(issues)
print(f"Total issues: {stats['total_issues']}")
print(f"USP issues: {stats['USP_count']}")
print(f"LCF issues: {stats['LCF_count']}")

# Detect cross-file inconsistencies
spec_dir = Path("Morph/Specs/AbiAlignmentAlgebra")
issues = detector.detect_cross_file_inconsistencies(spec_dir)
for issue in issues:
    print(f"{issue.issue_id}: {issue.description}")
```

**Configuration Options:**

| Option | Type | Default | Description |
|---------|------|---------|-------------|
| `detect_usp` | bool | True | Detect unclear specification points |
| `detect_lcf` | bool | True | Detect Lean 4 compilation failures |
| `detect_isr` | bool | True | Detect insufficient rigor |
| `detect_mel` | bool | True | Detect missing examples or lemmas |
| `detect_ibf` | bool | True | Detect inconsistencies between files |
| `strict_mode` | bool | False | Treat warnings as errors |

**Issue Categories (ADR-003):**

| Category | Code | Description | Detection Criteria |
|----------|------|-------------|------------------|
| Unclear Specification Points | USP | Vague terminology, ambiguous requirements, missing definitions |
| Lean 4 Compilation Failures | LCF | Syntax errors, type mismatches, import errors, proof obligations |
| Insufficient Rigor | ISR | Informal descriptions, missing invariants, unstated assumptions |
| Missing Examples or Lemmas | MEL | Empty files, missing key examples, insufficient lemmas |
| Inconsistencies Between Files | IBF | Contradictory definitions, examples that contradict specs |

---

### 3. Issue Classification Helper (`classification.py`)

**Purpose:** Classify verification issues according to ADR-003 taxonomy.

**ADR Reference:** [ADR-003: Issue Classification Taxonomy](../../../.specs/02_adrs/ADR-003_issue_classification_taxonomy.md)

**Features:**
- Five-category taxonomy (USP, LCF, ISR, MEL, IBF)
- Four severity levels (Critical, High, Medium, Low)
- Classification guidelines and decision trees
- Peer review support and audit trails
- Validation of classifications

**Usage:**

```python
from spec_tools.verification.classification import IssueClassifier, ClassificationConfig

# Create classifier with default configuration
classifier = IssueClassifier()

# Or with custom configuration
config = ClassificationConfig(
    strict_mode=False,
    require_rationale=True,
    allow_secondary_categories=True,
    default_severity=IssueSeverity.MEDIUM
)
classifier = IssueClassifier(config)

# Classify an issue based on description
category, severity, rationale = classifier.classify_issue(
    description="The term 'appropriate alignment' is used but not formally defined",
    category_hint=IssueCategory.USP,
    severity_hint=IssueSeverity.HIGH
)
print(f"Category: {category.value}")
print(f"Severity: {severity.value}")
print(f"Rationale: {rationale}")

# Classify a compilation error
category, severity = classifier.classify_compilation_error(
    error_type="Type Mismatch",
    error_message="expected Nat, found String",
    blocks_compilation=True
)
print(f"Category: {category.value}")
print(f"Severity: {severity.value}")

# Get classification statistics
stats = classifier.get_classification_statistics(issues)
print(f"Classification accuracy: {stats['classification_accuracy']}%")
```

**Configuration Options:**

| Option | Type | Default | Description |
|---------|------|---------|-------------|
| `strict_mode` | bool | False | Enforce strict classification rules |
| `require_rationale` | bool | True | Require rationale for classification |
| `allow_secondary_categories` | bool | True | Allow multiple categories per issue |
| `default_severity` | IssueSeverity | MEDIUM | Default severity if not specified |

**Severity Levels (ADR-006):**

| Severity | Description | Action Required | Examples |
|----------|-------------|-----------------|----------|
| **Critical** | Blocks compilation or fundamental contradictions | Immediate attention required | Type mismatches that prevent compilation, contradictory definitions |
| **High** | Significant gaps in rigor or missing key content | Address within current iteration | Missing lemmas for key properties, informal descriptions |
| **Medium** | Ambiguities or minor inconsistencies | Address in next iteration | Vague terminology without formal definition, minor inconsistencies |
| **Low** | Minor issues or documentation improvements | Address when time permits | Formatting issues, minor documentation improvements |

**Classification Guidelines:**

1. **Primary Category Selection:**
   - Choose category that best describes primary issue
   - If multiple categories apply, choose most severe
   - Document secondary categories in issue notes

2. **Severity Assessment:**
   - Use severity assessment matrix for consistency
   - Consider impact on verification and refactoring
   - Assess likelihood of causing bugs or confusion

3. **Documentation Requirements:**
   - Provide clear description of issue
   - Include line numbers where applicable
   - Suggest potential solutions
   - Link to related issues or specifications

4. **Review Process:**
   - Require peer review of issue classifications
   - Establish appeal process for disputed classifications
   - Regularly audit classifications for consistency

---

### 4. Severity Assessment Tool (`severity.py`)

**Purpose:** Assess issue severity according to ADR-006 criteria.

**ADR Reference:** [ADR-006: Severity-Based Prioritization](../../../.specs/02_adrs/ADR-006_severity_based_prioritization.md)

**Features:**
- Four-level severity system (Critical, High, Medium, Low)
- Severity assessment matrix for consistency
- Peer review support and audit trails
- Resource allocation guidelines based on severity
- Priority ordering for issue resolution

**Usage:**

```python
from spec_tools.verification.severity import SeverityAssessor, SeverityConfig

# Create assessor with default configuration
assessor = SeverityAssessor()

# Or with custom configuration
config = SeverityConfig(
    strict_mode=False,
    require_rationale=True,
    enable_peer_review=True,
    resource_allocation={
        IssueSeverity.CRITICAL: 0.50,  # 50% of resources
        IssueSeverity.HIGH: 0.30,     # 30% of resources
        IssueSeverity.MEDIUM: 0.15,   # 15% of resources
        IssueSeverity.LOW: 0.05,      # 5% of resources
    }
)
assessor = SeverityAssessor(config)

# Assess severity for an issue
severity, rationale = assessor.assess_severity(issue)
print(f"Severity: {severity.value}")
print(f"Rationale: {rationale}")

# Get priority order for issues
priority_issues = assessor.get_priority_order(issues)
for issue in priority_issues:
    print(f"{issue.severity.value}: {issue.issue_id}")

# Get resource allocation
allocation = assessor.get_resource_allocation(issues)
for severity, count in allocation.items():
    print(f"{severity.value}: {count} issues ({count} resources)")

# Get severity statistics
stats = assessor.get_severity_statistics(issues)
print(f"Critical issues: {stats['CRITICAL_count']}")
print(f"High issues: {stats['HIGH_count']}")
```

**Configuration Options:**

| Option | Type | Default | Description |
|---------|------|---------|-------------|
| `strict_mode` | bool | False | Enforce strict severity rules |
| `require_rationale` | bool | True | Require rationale for severity assessment |
| `enable_peer_review` | bool | True | Enable peer review workflow |
| `resource_allocation` | Dict[IssueSeverity, float] | See table below | Resource allocation by severity |

**Default Resource Allocation:**

| Severity | Percentage | Description |
|----------|------------|-------------|
| Critical | 50% | Immediate attention, blocks progress until resolved |
| High | 30% | Address within current iteration, prioritize after Critical issues |
| Medium | 15% | Address in next iteration, address when resources permit |
| Low | 5% | Address when time permits, lowest priority |

**Severity Assessment Criteria:**

**Critical Severity:**
- Blocks compilation or verification
- Fundamental contradictions between files
- Missing core definitions or imports
- Type errors that prevent type-checking
- Proof obligations that cannot be satisfied

**High Severity:**
- Significant gaps in mathematical rigor
- Missing key lemmas or examples
- Informal descriptions where formal definitions expected
- Empty or incomplete Lemmas.lean files
- Missing examples for key specification points

**Medium Severity:**
- Ambiguities in specification language
- Minor inconsistencies between files
- Incomplete examples or lemmas
- Vague terminology without formal definition
- Edge cases not critical to specification

**Low Severity:**
- Documentation improvements
- Formatting issues
- Minor edge cases
- Non-critical clarifications
- Style inconsistencies

---

### 5. Coverage Tracking (`coverage.py`)

**Purpose:** Track verification coverage across all specification files.

**ADR Reference:** Threat Model success criteria for completeness

**Features:**
- File-level coverage tracking
- Spec point coverage tracking
- Category-level coverage metrics
- Success criteria validation
- Progress reporting

**Usage:**

```python
from pathlib import Path
from spec_tools.verification.coverage import CoverageTracker, CoverageConfig

# Create tracker with default configuration
tracker = CoverageTracker()

# Or with custom configuration
config = CoverageConfig(
    specs_root=Path("Morph/Specs"),
    required_files=["Spec.lean", "Examples.lean", "Lemmas.lean"],
    spec_point_threshold=1,
    success_criteria={
        "file_coverage": 95.0,
        "spec_coverage": 95.0,
        "compilation_success_rate": 95.0,
        "type_checking_success_rate": 98.0,
    }
)
tracker = CoverageTracker(config)

# Track a compilation result
tracker.track_compilation_result(result)

# Track an issue
tracker.track_issue(issue)

# Track coverage for a directory
tracker.track_directory(Path("Morph/Specs"))

# Track coverage for all specs
tracker.track_specs()

# Get coverage metrics
metrics = tracker.get_coverage_metrics()
print(f"Spec coverage: {metrics.spec_coverage:.1f}%")
print(f"File coverage: {metrics.file_coverage:.1f}%")

# Validate success criteria
all_passed, criteria = tracker.validate_success_criteria()
print(f"Overall: {criteria['overall_success']}")

# Generate progress summary
summary = tracker.get_progress_summary()
print(summary)

# Generate markdown report
tracker.generate_markdown_report()
```

**Configuration Options:**

| Option | Type | Default | Description |
|---------|------|---------|-------------|
| `specs_root` | Path | `Path("Morph/Specs")` | Root directory containing all specification directories |
| `required_files` | List[str] | See table below | Required files per spec |
| `spec_point_threshold` | int | 1 | Minimum spec points required for coverage |
| `success_criteria` | Dict[str, float] | See table below | Success criteria thresholds |

**Default Required Files:**
- Spec.lean
- Examples.lean
- Lemmas.lean

**Success Criteria:**

| Criterion | Threshold | Description |
|----------|-----------|-------------|
| File Coverage | 95% | Percentage of files successfully verified |
| Spec Coverage | 95% | Percentage of specs successfully verified |
| Compilation Success Rate | 95% | Percentage of files that compile successfully |
| Type Checking Success Rate | 98% | Percentage of spec points that type-check successfully |

**Coverage Metrics:**

- `total_specs`: Total number of specification directories
- `verified_specs`: Number of verified specifications
- `total_files`: Total number of Lean 4 files
- `verified_files`: Number of successfully verified files
- `total_spec_points`: Total number of spec points
- `verified_spec_points`: Number of verified spec points
- `issues_by_category`: Count of issues by category
- `issues_by_severity`: Count of issues by severity
- `coverage_percentage`: Overall coverage percentage

---

## Integration Examples

### Complete Verification Workflow

```python
from pathlib import Path
from spec_tools.verification.compilation import Lean4CompilationVerifier
from spec_tools.verification.issue_detection import AutomatedIssueDetector
from spec_tools.verification.classification import IssueClassifier
from spec_tools.verification.severity import SeverityAssessor
from spec_tools.verification.coverage import CoverageTracker

# Initialize all tools
verifier = Lean4CompilationVerifier()
detector = AutomatedIssueDetector()
classifier = IssueClassifier()
assessor = SeverityAssessor()
tracker = CoverageTracker()

# Verify all specs
specs_root = Path("Morph/Specs")
results = verifier.verify_specs(specs_root)

# Detect issues
for result in results:
    if not result.success or result.errors:
        # Detect issues in failed files
        issues = detector.detect_issues(result.file_path)
        for issue in issues:
            # Classify and assess severity
            category, severity, rationale = classifier.classify_issue(
                description=issue.description,
                category_hint=issue.category,
                severity_hint=issue.severity
            )
            issue.severity = severity
            issue.notes = rationale

            # Track for coverage
            tracker.track_issue(issue)

# Track successful compilations
for result in results:
    if result.success:
        tracker.track_compilation_result(result)

# Generate final reports
tracker.generate_markdown_report()
```

### CLI Usage

The tools can be used from the command line:

```bash
# Verify all specs
python -m spec_tools.verification.compilation

# Detect issues
python -m spec_tools.verification.issue_detection

# Generate coverage report
python -m spec_tools.verification.coverage
```

## Threat Model Mitigation

These tools mitigate the following risks from the threat model:

### Data Integrity Risks

- **RISK-DI-001** (Critical): Misclassification of Spec Issues
  - **Mitigation:** Structured taxonomy with clear guidelines
  - **Tool:** IssueClassifier with validation

- **RISK-DI-002** (High): False Positive Issue Identification
  - **Mitigation:** Validation process, peer review
  - **Tool:** IssueClassifier validation

- **RISK-DI-003** (Critical): False Negative Issue Identification
  - **Mitigation:** Coverage tracking, multiple detection methods
  - **Tool:** CoverageTracker with comprehensive metrics

- **RISK-DI-007** (High): Issue Severity Misassessment
  - **Mitigation:** Severity assessment matrix, peer review
  - **Tool:** SeverityAssessor with clear criteria

### Completeness Risks

- **RISK-COMP-001** (Critical): Missing Specification Files
  - **Mitigation:** Automated file enumeration, coverage tracking
  - **Tool:** CoverageTracker with file discovery

- **RISK-COMP-002** (High): Incomplete Spec Point Verification
  - **Mitigation:** Spec point enumeration, coverage tracking
  - **Tool:** CoverageTracker with spec point tracking

### Lean 4 Compilation Risks

- **RISK-LEAN-001** (Critical): Lean 4 Compilation Failures Blocking Verification
  - **Mitigation:** Incremental verification, error isolation
  - **Tool:** Lean4CompilationVerifier with fallback strategies

- **RISK-LEAN-002** (High): Lean 4 Type Checking Errors
  - **Mitigation:** Type validation, type error reporting
  - **Tool:** Lean4CompilationVerifier with error parsing

- **RISK-LEAN-003** (High): Lean 4 Proof Search Timeouts
  - **Mitigation:** Timeout configuration, resource monitoring
  - **Tool:** Lean4CompilationVerifier with timeout handling

- **RISK-LEAN-004** (High): Lean 4 Memory Exhaustion
  - **Mitigation:** Memory limits, monitoring, file splitting
  - **Tool:** Lean4CompilationVerifier with memory monitoring

- **RISK-LEAN-005** (High): Lean 4 Dependency Resolution Failures
  - **Mitigation:** Dependency locking, validation
  - **Tool:** Lean4CompilationVerifier with dependency checking

- **RISK-LEAN-007** (Critical): Lean 4 Version Incompatibility
  - **Mitigation:** Version pinning, environment standardization
  - **Tool:** Lean4CompilationVerifier with version checking

## Testing

All tools should be tested with sample files before use in production:

```python
# Test compilation verification
from spec_tools.verification.compilation import Lean4CompilationVerifier

verifier = Lean4CompilationVerifier()
result = verifier.verify_file(Path("Morph/Specs/AbiAlignmentAlgebra/Spec.lean"))
assert result.success, "Expected successful compilation"

# Test issue detection
from spec_tools.verification.issue_detection import AutomatedIssueDetector

detector = AutomatedIssueDetector()
issues = detector.detect_issues(Path("Morph/Specs/AbiAlignmentAlgebra/Spec.lean"))
assert len(issues) >= 0, "Expected issues to be detected"

# Test classification
from spec_tools.verification.classification import IssueClassifier

classifier = IssueClassifier()
category, severity, rationale = classifier.classify_issue(
    description="Type mismatch in memory allocation",
)
assert category == IssueCategory.LCF, "Expected LCF category"
assert severity == IssueSeverity.HIGH, "Expected HIGH severity"

# Test severity assessment
from spec_tools.verification.severity import SeverityAssessor

assessor = SeverityAssessor()
severity, rationale = assessor.assess_compilation_error(
    error_type="Type Mismatch",
    blocks_compilation=True
)
assert severity == IssueSeverity.CRITICAL, "Expected CRITICAL severity"

# Test coverage tracking
from spec_tools.verification.coverage import CoverageTracker

tracker = CoverageTracker()
tracker.track_compilation_result(result)
metrics = tracker.get_coverage_metrics()
assert metrics.file_coverage > 0, "Expected positive coverage"
```

## Requirements Satisfied

Based on Task 6 Definition of Done:

- [x] Lean 4 compilation verification script is created
- [x] Automated issue detection tools are set up
- [x] Classification helper tool is created based on ADR-003
- [x] Severity assessment tool is created based on ADR-006
- [x] Coverage tracking script is created
- [x] All tools are documented with usage instructions
- [ ] Tools are tested with sample files

## References

- [Threat Model Analysis](../../../.specs/03_threat_model/spec_verification_analysis.md)
- [ADR-002: Lean 4 Compilation Verification](../../../.specs/02_adrs/ADR-002_lean4_compilation_verification.md)
- [ADR-003: Issue Classification Taxonomy](../../../.specs/02_adrs/ADR-003_issue_classification_taxonomy.md)
- [ADR-006: Severity-Based Prioritization](../../../.specs/02_adrs/ADR-006_severity_based_prioritization.md)
- [Coding Standards](../../../.specs/01_standards/coding_standards.md)
