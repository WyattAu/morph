# Specification Version Validator

A comprehensive tool for validating version numbers and compatibility across all Morph specifications according to [`spec/conventions/version_compatibility_spec.md`](../spec/conventions/version_compatibility_spec.md).

## Table of Contents

- [Overview](#overview)
- [Features](#features)
- [Installation](#installation)
- [Usage](#usage)
- [Validation Checks](#validation-checks)
- [Output Formats](#output-formats)
- [Examples](#examples)
- [Exit Codes](#exit-codes)
- [Integration](#integration)
- [Troubleshooting](#troubleshooting)

## Overview

The Specification Version Validator ensures that all Morph specifications follow consistent versioning practices and maintain compatibility across the specification ecosystem. It validates:

- Version format compliance (Semantic Versioning 2.0.0)
- Version compatibility between specifications
- Synchronization group consistency
- Dependency version requirements
- End of Life (EOL) version detection

## Features

### Core Validation

- **Version Format Validation**: Ensures all versions follow MAJOR.MINOR.PATCH format
- **Compatibility Checking**: Validates that specifications with dependencies have compatible versions
- **Synchronization Group Validation**: Ensures specs in sync groups have consistent MAJOR versions
- **Dependency Validation**: Verifies that dependent specs meet minimum version requirements
- **EOL Detection**: Identifies and reports End of Life versions

### Version Support

- **Semantic Versioning 2.0.0**: Full support for SemVer including:
  - MAJOR.MINOR.PATCH format
  - Pre-release versions (e.g., `1.0.0-alpha`, `1.0.0-rc.1`)
  - Build metadata (e.g., `1.0.0+20230101`)
  - MASTER branch versions (e.g., `2.0.0-MASTER`)

### Reporting

- **Text Reports**: Human-readable reports with detailed error messages
- **JSON Reports**: Machine-readable reports for CI/CD integration
- **Compatibility Matrix**: Visual matrix showing compatibility between all spec pairs
- **Error Severity**: Clear distinction between errors and warnings

## Installation

### Prerequisites

- Python 3.7 or higher
- Access to the Morph specification repository

### Setup

The validator is part of the Morph tooling suite. No additional installation is required beyond cloning the repository:

```bash
# Clone the repository (if not already done)
git clone <repository-url>
cd morph
```

The validator script is located at [`scripts/spec_version_validator.py`](scripts/spec_version_validator.py).

## Usage

### Basic Usage

Validate all specifications in the default `spec/` directory:

```bash
python scripts/spec_version_validator.py
```

### Command-Line Options

```
usage: spec_version_validator.py [-h] [--spec-dir SPEC_DIR] 
                                 [--format {text,json}] 
                                 [--output OUTPUT] 
                                 [--errors-only] 
                                 [--quiet]

Validate version numbers and compatibility across Morph specifications

optional arguments:
  -h, --help            Show help message and exit
  --spec-dir SPEC_DIR   Directory containing specification files (default: spec)
  --format {text,json}  Output format (default: text)
  --output OUTPUT       Output file path (default: stdout)
  --errors-only         Show only errors, not warnings
  --quiet               Suppress all output except errors
```

### Options Explained

#### `--spec-dir`

Specify a custom directory containing specification files:

```bash
python scripts/spec_version_validator.py --spec-dir ./custom_specs
```

#### `--format`

Choose the output format:

- `text` (default): Human-readable text report
- `json`: Machine-readable JSON report

```bash
# Generate JSON report
python scripts/spec_version_validator.py --format json

# Generate text report (explicit)
python scripts/spec_version_validator.py --format text
```

#### `--output`

Save the report to a file instead of printing to stdout:

```bash
python scripts/spec_version_validator.py --output validation_report.txt
python scripts/spec_version_validator.py --format json --output report.json
```

#### `--errors-only`

Display only errors, suppressing warnings:

```bash
python scripts/spec_version_validator.py --errors-only
```

#### `--quiet`

Suppress all output except errors (useful for CI/CD):

```bash
python scripts/spec_version_validator.py --quiet
```

## Validation Checks

### 1. Version Format Validation

Validates that all version strings follow Semantic Versioning 2.0.0 format:

**Valid formats:**
- `1.0.0`
- `2.1.3`
- `1.0.0-alpha`
- `1.0.0-beta.2`
- `1.0.0-rc.1`
- `2.0.0-MASTER`
- `1.0.0+20230101`

**Invalid formats:**
- `1.0` (missing PATCH)
- `v1.0.0` (prefix not allowed)
- `1.0.0.0` (too many components)
- `invalid` (not a version)

**Error Example:**
```
ERROR: Invalid version format: 1.0. Expected MAJOR.MINOR.PATCH format
  spec/test_spec.md:3
```

### 2. Version Compatibility Validation

Checks compatibility between all specification pairs according to the compatibility rules:

**Compatibility Rules:**
- Same MAJOR version: Compatible
- Different MAJOR version: Incompatible

**Error Example:**
```
ERROR: Incompatible versions: 1.0.0 vs 2.0.0. Different MAJOR versions are incompatible.
  spec/spec1.md:3
  spec/spec2.md:3
```

### 3. Synchronization Group Validation

Ensures specifications in the same synchronization group have compatible MAJOR versions:

**Synchronization Groups:**

**Core Group:**
- `morph_language_spec.md`
- `type_system_spec.md`
- `memory_model_spec.md`
- `execution_model_spec.md`
- `security_flow_spec.md`

**Type System Group:**
- `type_system_spec.md`
- `type_category_spec.md`
- `type_unification_spec.md`
- `pure_type_spec.md`
- `effect_system_spec.md`

**Concurrency Group:**
- `execution_model_spec.md`
- `concurrency_process_algebra_spec.md`
- `monadic_effect_spec.md`
- `scheduling_modes_spec.md`
- `scheduler_randomized_stealing_spec.md`
- `layered_concurrency_spec.md`

**Error Example:**
```
ERROR: Synchronization group 'core' has inconsistent MAJOR versions:
    morph_language_spec.md: 2.0.0
    type_system_spec.md: 1.0.0
    memory_model_spec.md: 2.0.0
  spec/morph_language_spec.md:3
```

### 4. Dependency Validation

Validates that dependent specifications meet minimum version requirements:

**Dependency Requirements:**

| Dependent Spec | Dependency | Minimum Version |
|----------------|------------|-----------------|
| `type_system_spec.md` | `morph_language_spec.md` | 2.0.0 |
| `memory_model_spec.md` | `type_system_spec.md` | 2.0.0 |
| `execution_model_spec.md` | `type_system_spec.md` | 2.0.0 |
| `execution_model_spec.md` | `memory_model_spec.md` | 2.0.0 |
| `security_flow_spec.md` | `type_system_spec.md` | 2.0.0 |

**Error Example:**
```
ERROR: Dependency version mismatch: memory_model_spec.md requires type_system_spec.md >= 2.0.0, but found 1.0.0
  spec/memory_model_spec.md:3
  spec/type_system_spec.md:3
```

### 5. EOL Version Detection

Identifies End of Life versions that should not be used:

**EOL Versions:**
- `1.0.0` (EOL since 2026-07-02)

**Error Example:**
```
ERROR: Version 1.0.0 is End of Life (EOL) since 2026-07-02. Must upgrade to a supported version.
  spec/test_spec.md:3
```

## Output Formats

### Text Format

The default text format provides a human-readable report with the following sections:

```
================================================================================
SPECIFICATION VERSION VALIDATION REPORT
================================================================================

SUMMARY
--------------------------------------------------------------------------------
Total specifications: 56
Errors: 2
Warnings: 1

VERSION INVENTORY
--------------------------------------------------------------------------------
  abi_alignment_algebra_spec.md: 1.0.0
  abi_data_refinement_spec.md: 1.0.0
  ...

ERRORS
--------------------------------------------------------------------------------
ERROR: Incompatible versions: 1.0.0 vs 2.0.0. Different MAJOR versions are incompatible.
  spec/spec1.md:3
  spec/spec2.md:3

WARNINGS
--------------------------------------------------------------------------------
WARNING: No version found in specification header
  spec/README.md:1

COMPATIBILITY MATRIX
--------------------------------------------------------------------------------
  ✅ 1.0.0 (spec1.md) <-> 1.2.3 (spec3.md)
  ❌ 1.0.0 (spec1.md) <-> 2.0.0 (spec2.md)
  ...

================================================================================
```

### JSON Format

The JSON format provides a machine-readable report suitable for CI/CD integration:

```json
{
  "summary": {
    "total_specs": 56,
    "errors": 2,
    "warnings": 1
  },
  "specifications": [
    {
      "name": "abi_alignment_algebra_spec.md",
      "version": "1.0.0",
      "path": "spec/build/abi_alignment_algebra_spec.md",
      "line_number": 3
    },
    ...
  ],
  "errors": [
    {
      "type": "INCOMPATIBLE_VERSIONS",
      "message": "Incompatible versions: 1.0.0 vs 2.0.0. Different MAJOR versions are incompatible.",
      "spec1": {
        "name": "spec1.md",
        "version": "1.0.0",
        "path": "spec/spec1.md",
        "line_number": 3
      },
      "spec2": {
        "name": "spec2.md",
        "version": "2.0.0",
        "path": "spec/spec2.md",
        "line_number": 3
      },
      "severity": "ERROR"
    },
    ...
  ],
  "warnings": [...]
}
```

## Examples

### Example 1: Basic Validation

Validate all specifications and display results:

```bash
python scripts/spec_version_validator.py
```

**Output:**
```
================================================================================
SPECIFICATION VERSION VALIDATION REPORT
================================================================================

SUMMARY
--------------------------------------------------------------------------------
Total specifications: 56
Errors: 0
Warnings: 0

VERSION INVENTORY
--------------------------------------------------------------------------------
  abi_alignment_algebra_spec.md: 1.0.0
  abi_data_refinement_spec.md: 1.0.0
  ...

COMPATIBILITY MATRIX
--------------------------------------------------------------------------------
  ✅ 1.0.0 (abi_alignment_algebra_spec.md) <-> 1.0.0 (abi_data_refinement_spec.md)
  ✅ 1.0.0 (abi_alignment_algebra_spec.md) <-> 1.0.0 (backend_tiling_spec.md)
  ...

================================================================================
```

### Example 2: Generate JSON Report for CI/CD

Generate a JSON report and save to file:

```bash
python scripts/spec_version_validator.py --format json --output validation_report.json
```

**Usage in CI/CD:**
```yaml
# GitHub Actions example
- name: Validate Specification Versions
  run: |
    python scripts/spec_version_validator.py --format json --output report.json
    
- name: Check Validation Results
  run: |
    if [ $(jq '.summary.errors' report.json) -gt 0 ]; then
      echo "Version validation failed!"
      exit 1
    fi
```

### Example 3: Validate Custom Directory

Validate specifications in a custom directory:

```bash
python scripts/spec_version_validator.py --spec-dir ./custom_specs
```

### Example 4: Show Only Errors

Display only errors, suppressing warnings:

```bash
python scripts/spec_version_validator.py --errors-only
```

### Example 5: Quiet Mode for CI/CD

Run validation in quiet mode (only output errors):

```bash
python scripts/spec_version_validator.py --quiet
```

**Exit code:** `1` if errors found, `0` otherwise

### Example 6: Integration with Pre-commit Hook

Create a pre-commit hook to validate versions before committing:

```bash
# .git/hooks/pre-commit
#!/bin/bash
echo "Validating specification versions..."
python scripts/spec_version_validator.py --quiet
if [ $? -ne 0 ]; then
    echo "Version validation failed. Please fix errors before committing."
    exit 1
fi
```

## Exit Codes

The validator returns the following exit codes:

| Exit Code | Meaning |
|-----------|---------|
| `0` | Validation passed (no errors) |
| `1` | Validation failed (errors found) |
| `2` | Invalid command-line arguments |

**Note:** Warnings do not cause a non-zero exit code. Only errors trigger a failure.

## Integration

### CI/CD Integration

#### GitHub Actions

```yaml
name: Version Validation

on: [push, pull_request]

jobs:
  validate:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v2
      - name: Set up Python
        uses: actions/setup-python@v2
        with:
          python-version: '3.9'
      - name: Validate Versions
        run: |
          python scripts/spec_version_validator.py --quiet
```

#### GitLab CI

```yaml
version_validation:
  stage: test
  script:
    - python scripts/spec_version_validator.py --quiet
  only:
    - merge_requests
    - main
```

#### Jenkins Pipeline

```groovy
pipeline {
    agent any
    stages {
        stage('Validate Versions') {
            steps {
                sh 'python scripts/spec_version_validator.py --quiet'
            }
        }
    }
}
```

### Pre-commit Integration

Add to `.pre-commit-config.yaml`:

```yaml
repos:
  - repo: local
    hooks:
      - id: spec-version-validator
        name: Specification Version Validator
        entry: python scripts/spec_version_validator.py --quiet
        language: system
        files: ^spec/.*\.md$
```

### Makefile Integration

Add to `Makefile`:

```makefile
.PHONY: validate-versions

validate-versions:
	@echo "Validating specification versions..."
	@python scripts/spec_version_validator.py --quiet

test: validate-versions
	@echo "Running tests..."
	@python -m pytest tests/
```

## Troubleshooting

### Common Issues

#### Issue: "No version found in specification header"

**Cause:** The specification file does not contain a version line in the expected format.

**Solution:** Ensure the specification header includes a version line:

```markdown
**Version:** 1.0.0
```

#### Issue: "Invalid version format"

**Cause:** The version string does not follow Semantic Versioning 2.0.0 format.

**Solution:** Ensure the version follows MAJOR.MINOR.PATCH format:

```markdown
**Version:** 1.0.0  # Correct
**Version:** 1.0    # Incorrect - missing PATCH
**Version:** v1.0.0  # Incorrect - prefix not allowed
```

#### Issue: "Incompatible versions" error

**Cause:** Two specifications have different MAJOR versions but are referenced together.

**Solution:** Ensure specifications that work together have the same MAJOR version, or update the dependency requirements.

#### Issue: "Synchronization group has inconsistent MAJOR versions"

**Cause:** Specifications in the same synchronization group have different MAJOR versions.

**Solution:** Update all specifications in the synchronization group to the same MAJOR version.

#### Issue: "Dependency version mismatch"

**Cause:** A dependent specification does not meet the minimum version requirement.

**Solution:** Upgrade the dependent specification to meet the minimum version requirement.

### Debug Mode

For detailed debugging, run the validator with verbose output:

```bash
python scripts/spec_version_validator.py --format text
```

Review the compatibility matrix to identify incompatible version pairs.

### Getting Help

If you encounter issues not covered here:

1. Check the [Version Compatibility Specification](../spec/conventions/version_compatibility_spec.md)
2. Review the error messages carefully for file paths and line numbers
3. Ensure all specification files have proper version headers
4. Verify synchronization group membership and version requirements

## Related Documentation

- [Version Compatibility Specification](../spec/conventions/version_compatibility_spec.md)
- [Specification Convention](../docs/conventions/specification_convention.md)
- [Specification Linter](./SPEC_LINTER_README.md)
- [Link Checker](./SPEC_LINK_CHECKER_README.md)

## License

This tool is part of the Morph project and follows the same license as the main project.

## Contributing

Contributions to the version validator are welcome. Please ensure:

1. All tests pass: `python -m pytest tests/test_spec_version_validator.py`
2. New features include corresponding tests
3. Documentation is updated for any changes

## Version History

| Version | Date | Changes |
|---------|------|---------|
| 1.0.0 | 2026-01-02 | Initial release - Version validation tool |
