# Spec-Tools User Guide

## Table of Contents

1. [Installation](#installation)
2. [Quick Start](#quick-start)
3. [Command Reference](#command-reference)
4. [Configuration](#configuration)
5. [Troubleshooting](#troubleshooting)
6. [Examples](#examples)

---

## Installation

### Prerequisites

- Python 3.8 or higher
- pip (Python package installer)

### Install from PyPI

```bash
pip install spec-tools
```

### Install from Source

```bash
git clone https://github.com/morph-project/spec-tools.git
cd spec-tools
pip install -e .
```

### Verify Installation

```bash
spec-tools --version
```

Expected output:
```
spec-tools 1.0.0
```

---

## Quick Start

### Basic Usage

1. **Format specification files:**

```bash
spec-tools format spec/
```

2. **Lint specification files:**

```bash
spec-tools lint spec/
```

3. **Validate specification files:**

```bash
spec-tools validate spec/
```

4. **Check links:**

```bash
spec-tools check-links spec/
```

5. **Run all checks:**

```bash
spec-tools check-all spec/
```

### Check Without Modifying

Use the `--check` flag to verify formatting without modifying files:

```bash
spec-tools format spec/ --check
```

### Generate Configuration File

Create a default configuration file:

```bash
spec-tools init-config
```

This creates a `.spec-tools.yaml` file in the current directory.

---

## Command Reference

### format

Format specification files according to the Morph project specification convention.

**Syntax:**
```bash
spec-tools format <path> [options]
```

**Arguments:**
- `<path>`: File or directory to format

**Options:**
- `--check`: Check formatting without modifying files (exit code 1 if changes needed)
- `--config <path>`: Path to configuration file (default: `.spec-tools.yaml`)

**Examples:**
```bash
# Format all spec files
spec-tools format spec/

# Format a single file
spec-tools format spec/example_spec.md

# Check formatting without modifying
spec-tools format spec/ --check

# Use custom config
spec-tools format spec/ --config my-config.yaml
```

**What it does:**
- Enforces maximum line length (default: 120 characters)
- Removes trailing whitespace
- Normalizes list formatting (uses `-` for unordered lists)
- Fixes heading spacing (exactly one space after `#`)
- Normalizes emphasis markers (`*italic*` instead of `_italic_`)

---

### lint

Lint specification files for convention compliance.

**Syntax:**
```bash
spec-tools lint <path> [options]
```

**Arguments:**
- `<path>`: File or directory to lint

**Options:**
- `--strict`: Treat warnings as errors
- `--rules <list>`: Comma-separated list of rules to run (default: all rules)
- `--fix`: Auto-fix issues where possible
- `--config <path>`: Path to configuration file (default: `.spec-tools.yaml`)

**Examples:**
```bash
# Lint all spec files
spec-tools lint spec/

# Lint with strict mode
spec-tools lint spec/ --strict

# Run specific rules only
spec-tools lint spec/ --rules header,sections,math

# Auto-fix issues
spec-tools lint spec/ --fix
```

**Rules:**
- `header`: Validates specification file header fields
- `sections`: Validates section structure and organization
- `ears`: Validates requirements against EARS pattern
- `math`: Validates mathematical notation syntax
- `mermaid`: Validates Mermaid diagram syntax
- `cross_refs`: Validates cross-references
- `change_log`: Validates change log format

---

### validate

Validate specification files against enhanced convention.

**Syntax:**
```bash
spec-tools validate <path> [options]
```

**Arguments:**
- `<path>`: File or directory to validate

**Options:**
- `--check-traceability`: Check traceability matrix
- `--check-security`: Check security specifications
- `--check-performance`: Check performance specifications
- `--check-maintainability`: Check maintainability specifications
- `--check-risk`: Check risk assessment
- `--check-verification`: Check verification plan
- `--config <path>`: Path to configuration file (default: `.spec-tools.yaml`)

**Examples:**
```bash
# Validate with all checks
spec-tools validate spec/

# Validate specific checks only
spec-tools validate spec/ --check-traceability --check-security

# Validate with custom config
spec-tools validate spec/ --config my-config.yaml
```

**Validation Checks:**
- **Traceability Matrix**: Ensures all requirements are traced to design elements and test cases
- **Verification Plan**: Validates verification methods, criteria, and acceptance criteria
- **Risk Assessment**: Validates risk identification, analysis, and mitigation strategies
- **Security Specifications**: Validates STRIDE threat modeling and security controls
- **Performance Specifications**: Validates performance metrics, targets, and measurement methods
- **Maintainability Specifications**: Validates code quality metrics, documentation standards, and evolution strategy

---

### check-links

Check links in specification files.

**Syntax:**
```bash
spec-tools check-links <path> [options]
```

**Arguments:**
- `<path>`: File or directory to check

**Options:**
- `--output <path>`: Output file for the link report (default: stdout)
- `--format <format>`: Output format (text or json, default: text)
- `--config <path>`: Path to configuration file (default: `.spec-tools.yaml`)

**Examples:**
```bash
# Check links in all spec files
spec-tools check-links spec/

# Save report to file
spec-tools check-links spec/ --output link-report.txt

# Output in JSON format
spec-tools check-links spec/ --format json
```

**What it checks:**
- Markdown links to other files
- Section references within files
- File references
- External URLs (skipped by default)

---

### check-all

Run all validation checks on specification files.

**Syntax:**
```bash
spec-tools check-all <path> [options]
```

**Arguments:**
- `<path>`: File or directory to check

**Options:**
- `--strict`: Treat warnings as errors in all checks
- `--verbose`: Show detailed output for all checks
- `--config <path>`: Path to configuration file (default: `.spec-tools.yaml`)

**Examples:**
```bash
# Run all checks
spec-tools check-all spec/

# Run with strict mode
spec-tools check-all spec/ --strict

# Show detailed output
spec-tools check-all spec/ --verbose
```

**What it does:**
Runs format check, lint, validate, and link checking in sequence.

---

### init-config

Generate a configuration file for spec-tools.

**Syntax:**
```bash
spec-tools init-config [options]
```

**Options:**
- `--output <path>`: Output file path (default: `.spec-tools.yaml`)
- `--template <template>`: Configuration template (minimal or full, default: full)

**Examples:**
```bash
# Generate full config
spec-tools init-config

# Generate minimal config
spec-tools init-config --template minimal

# Save to custom location
spec-tools init-config --output config/spec-tools.yaml
```

---

## Configuration

### Configuration File Format

The configuration file uses YAML format. Create a `.spec-tools.yaml` file in your project root.

### Full Configuration Example

```yaml
# Formatting configuration
formatting:
  max_line_length: 120
  enforce_trailing_whitespace: true
  normalize_lists: true
  fix_heading_spacing: true
  normalize_emphasis: true

# Linting configuration
linting:
  strict: false
  check_ears_pattern: true
  check_math_notation: true
  check_mermaid_syntax: true
  check_cross_references: true

# Validation configuration
validation:
  check_traceability: true
  check_verification_plan: true
  check_risk_assessment: true
  check_security_specs: true
  check_performance_specs: true
  check_maintainability_specs: true

# Link checking configuration
link_checking:
  check_broken_links: true
  check_orphaned_sections: true
  check_duplicate_links: true
  check_self_references: false

# Output configuration
output:
  format: text
  verbose: false
  quiet: false
  color_output: true
```

### Minimal Configuration Example

```yaml
formatting:
  max_line_length: 120

linting:
  strict: false

validation:
  check_traceability: true
  check_security_specs: true
```

### Configuration Options

#### Formatting Options

| Option | Type | Default | Description |
|---------|--------|----------|-------------|
| `max_line_length` | integer | 120 | Maximum allowed line length |
| `enforce_trailing_whitespace` | boolean | true | Remove trailing whitespace |
| `normalize_lists` | boolean | true | Normalize list formatting |
| `fix_heading_spacing` | boolean | true | Fix heading spacing |
| `normalize_emphasis` | boolean | true | Normalize emphasis markers |

#### Linting Options

| Option | Type | Default | Description |
|---------|--------|----------|-------------|
| `strict` | boolean | false | Treat warnings as errors |
| `check_ears_pattern` | boolean | true | Check EARS pattern compliance |
| `check_math_notation` | boolean | true | Check mathematical notation |
| `check_mermaid_syntax` | boolean | true | Check Mermaid diagram syntax |
| `check_cross_references` | boolean | true | Check cross-references |

#### Validation Options

| Option | Type | Default | Description |
|---------|--------|----------|-------------|
| `check_traceability` | boolean | true | Check traceability matrix |
| `check_verification_plan` | boolean | true | Check verification plan |
| `check_risk_assessment` | boolean | true | Check risk assessment |
| `check_security_specs` | boolean | true | Check security specifications |
| `check_performance_specs` | boolean | true | Check performance specifications |
| `check_maintainability_specs` | boolean | true | Check maintainability specifications |

#### Link Checking Options

| Option | Type | Default | Description |
|---------|--------|----------|-------------|
| `check_broken_links` | boolean | true | Check for broken links |
| `check_orphaned_sections` | boolean | true | Check for orphaned sections |
| `check_duplicate_links` | boolean | true | Check for duplicate links |
| `check_self_references` | boolean | false | Check for self-references |

#### Output Options

| Option | Type | Default | Description |
|---------|--------|----------|-------------|
| `format` | string | text | Output format (text or json) |
| `verbose` | boolean | false | Enable verbose output |
| `quiet` | boolean | false | Suppress non-error output |
| `color_output` | boolean | true | Enable colored output |

---

## Troubleshooting

### Common Issues

#### Issue: "Configuration file not found"

**Cause:** The `.spec-tools.yaml` file doesn't exist in the current directory.

**Solution:**
```bash
# Generate default configuration
spec-tools init-config
```

#### Issue: "File not found" error

**Cause:** The specified file or directory path doesn't exist.

**Solution:**
- Verify the path is correct
- Use relative or absolute paths
- Check file permissions

#### Issue: "Invalid YAML in configuration file"

**Cause:** The configuration file contains invalid YAML syntax.

**Solution:**
- Check YAML indentation (use spaces, not tabs)
- Validate YAML syntax using an online validator
- Regenerate configuration file:
  ```bash
  spec-tools init-config --output .spec-tools.yaml
  ```

#### Issue: "max_line_length must be at least 40"

**Cause:** The `max_line_length` value in configuration is too small.

**Solution:**
Set `max_line_length` to a value between 40 and 200:
```yaml
formatting:
  max_line_length: 120
```

#### Issue: "output format must be 'text' or 'json'"

**Cause:** Invalid output format specified in configuration.

**Solution:**
Use either `text` or `json`:
```yaml
output:
  format: text
```

#### Issue: "output verbose and quiet cannot both be True"

**Cause:** Both `verbose` and `quiet` are set to `true` in configuration.

**Solution:**
Set only one of them to `true`:
```yaml
output:
  verbose: true
  quiet: false
```

### Getting Help

Get help for a specific command:
```bash
spec-tools <command> --help
```

Get general help:
```bash
spec-tools --help
```

### Debug Mode

Enable verbose output to see detailed information:
```bash
spec-tools lint spec/ --verbose
```

---

## Examples

### Example 1: Format and Validate a New Specification

```bash
# 1. Create a new specification file
cat > spec/new_feature.md << 'EOF'
# New Feature Specification

## Purpose and Scope
This specification describes a new feature.

## Requirements
REQ-001: The system shall support the new feature.
EOF

# 2. Format the file
spec-tools format spec/new_feature.md

# 3. Lint the file
spec-tools lint spec/new_feature.md

# 4. Validate the file
spec-tools validate spec/new_feature.md
```

### Example 2: Check All Specifications in a Project

```bash
# Run all checks on the spec directory
spec-tools check-all spec/ --verbose

# Output:
# Checking format...
# [PASS] spec/feature_a.md: Properly formatted
# [PASS] spec/feature_b.md: Properly formatted
#
# Linting...
# [PASS] spec/feature_a.md: No issues found
# [FAIL] spec/feature_b.md: 2 issues found
#   Line 15: [WARNING] ears-validation: Requirement does not follow EARS pattern
#   Line 20: [ERROR] header-validation: Missing required header field: Version
#
# Validating...
# [PASS] spec/feature_a.md: All checks passed
# [FAIL] spec/feature_b.md: 1 issue found
#   Line 1: [ERROR] TRACEABILITY-001: Traceability Matrix section is missing
#
# Checking links...
# [PASS] spec/feature_a.md: All links valid
# [PASS] spec/feature_b.md: All links valid
```

### Example 3: Use Custom Configuration

```bash
# 1. Create custom configuration
cat > .spec-tools.yaml << 'EOF'
formatting:
  max_line_length: 100

linting:
  strict: true

validation:
  check_traceability: true
  check_security_specs: true
  check_performance_specs: false
EOF

# 2. Run checks with custom configuration
spec-tools check-all spec/
```

### Example 4: Format Check in CI/CD

```bash
#!/bin/bash
# ci-check.sh

# Check formatting without modifying
if ! spec-tools format spec/ --check; then
    echo "Formatting issues found. Run 'spec-tools format spec/' to fix."
    exit 1
fi

# Lint with strict mode
if ! spec-tools lint spec/ --strict; then
    echo "Linting issues found."
    exit 1
fi

# Validate
if ! spec-tools validate spec/; then
    echo "Validation issues found."
    exit 1
fi

echo "All checks passed!"
exit 0
```

### Example 5: Generate Link Report

```bash
# Check links and save report
spec-tools check-links spec/ --output link-report.txt

# View report
cat link-report.txt

# Output:
# Link Report for spec/
# ========================
#
# Total links: 45
# Valid links: 42
# Broken links: 2
# Orphaned sections: 1
#
# Broken links:
# - spec/feature_a.md:15: Link to 'nonexistent.md' not found
# - spec/feature_b.md:30: Link to 'missing_section' not found
#
# Orphaned sections:
# - spec/feature_c.md:10: Section 'unused_section' has no references
```

### Example 6: Validate Specific Checks

```bash
# Validate only traceability and security
spec-tools validate spec/ \
    --check-traceability \
    --check-security

# Validate only performance and maintainability
spec-tools validate spec/ \
    --check-performance \
    --check-maintainability
```

### Example 7: Auto-fix Linting Issues

```bash
# Auto-fix issues where possible
spec-tools lint spec/ --fix

# Output:
# [PASS] spec/feature_a.md: Fixed 3 issues
#   - Fixed heading spacing
#   - Normalized list formatting
#   - Removed trailing whitespace
#
# [PASS] spec/feature_b.md: Fixed 1 issue
#   - Normalized emphasis markers
```

---

## Best Practices

1. **Always run format before committing:**
   ```bash
   spec-tools format spec/
   ```

2. **Use check mode in CI/CD:**
   ```bash
   spec-tools format spec/ --check
   ```

3. **Run all checks before releases:**
   ```bash
   spec-tools check-all spec/ --strict
   ```

4. **Keep configuration in version control:**
   ```bash
   git add .spec-tools.yaml
   git commit -m "Add spec-tools configuration"
   ```

5. **Use verbose mode for debugging:**
   ```bash
   spec-tools lint spec/ --verbose
   ```

---

## Additional Resources

- [Developer Guide](developer-guide.md)
- [API Documentation](../api/)
- [Specification Convention](../conventions/specification_convention.md)
- [GitHub Repository](https://github.com/morph-project/spec-tools)
- [Issue Tracker](https://github.com/morph-project/spec-tools/issues)
