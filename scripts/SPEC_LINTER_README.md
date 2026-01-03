# Specification Linter

A comprehensive static analysis tool for validating specification documents against the Morph project's specification convention.

## Overview

The specification linter (`spec_linter.py`) validates all specification files in the `spec/` directory against the conventions defined in `docs/conventions/specification_convention.md`. It ensures consistency, completeness, and correctness across all specification documents.

## Features

### Validation Checks

The linter performs the following validation checks:

#### 1. Document Header Validation
- **Title**: First line must be a title (`# Title`)
- **File Path**: Must match actual filename
- **Version**: Must follow Semantic Versioning (MAJOR.MINOR.PATCH)
- **Context**: Must specify architectural layer and component
- **Formalism**: Must specify mathematical formalism used
- **Status**: Must be one of: Draft, Active, Deprecated
- **Last Modified**: Must be in YYYY-MM-DD format
- **Author**: Must be specified
- **Reviewers**: Must be specified

#### 2. Section Structure Validation
- **Mandatory Sections**: All required sections must be present:
  - Introduction
  - Formal Definitions
  - Requirements
  - Design
  - Correctness Properties
  - Examples
- **Section Numbering**: Must be sequential (1, 2, 3, ...)
- **Heading Hierarchy**: Must follow proper nesting (no skipped levels)

#### 3. Requirements Validation
- **EARS Pattern**: Requirements must use EARS syntax:
  - "THE system SHALL..." (Ubiquitous)
  - "WHEN [trigger], THE system SHALL..." (Event-Driven)
  - "WHILE [state], THE system SHALL..." (State-Driven)
  - "WHERE [condition], THE system SHALL..." (Optional)
- **Unique Identifiers**: Each requirement must have a unique ID (XXX-REQ-NNN)
- **ID Format**: Must match pattern: [Component]-[Type]-[Number]
- **Required Attributes**: Each requirement must include:
  - Priority (Critical | High | Medium | Low)
  - Verification Method (Inspection | Analysis | Demonstration | Test)
  - Rationale
  - Dependencies
  - Traceability

#### 4. Mathematical Notation Validation
- **LaTeX Syntax**: All math must use proper LaTeX syntax
- **Inline Math**: Must use `$...$` delimiters
- **Block Math**: Must use `$$...$$` delimiters
- **Balanced Braces**: All braces must be balanced
- **Unclosed Blocks**: Detects unclosed math blocks

#### 5. Cross-Reference Validation
- **File Paths**: Validates that referenced files exist
- **Link Format**: Checks for proper markdown link syntax
- **Section References**: Validates section reference format
- **External Links**: Skips validation for HTTP/HTTPS links

#### 6. Mermaid Diagram Validation
- **Valid Diagram Types**: Only recognized diagram types allowed:
  - `sequenceDiagram`
  - `stateDiagram-v2`
  - `flowchart`
  - `erDiagram`
  - `classDiagram`
  - `gantt`
  - `pie`
  - `gitGraph`
- **Syntax Validation**: Checks for common syntax errors
- **Unclosed Blocks**: Detects unclosed diagram blocks

#### 7. Change Log Validation
- **Presence**: Change Log section must be present
- **Format**: Must be a table with columns: Version, Date, Author, Changes
- **Chronological**: Entries should be in chronological order

#### 8. Markdown Formatting Validation
- **Line Length**: Maximum 120 characters (except code blocks and URLs)
- **Trailing Whitespace**: No trailing whitespace allowed
- **Heading Spacing**: Exactly one space after `#` characters
- **List Formatting**: Proper spacing after list markers

## Installation

No installation required. The linter is a standalone Python script that uses only standard library modules.

### Requirements

- Python 3.7 or higher
- No external dependencies

## Usage

### Basic Usage

Lint a single file:
```bash
python scripts/spec_linter.py spec/language/ast_graph_spec.md
```

Lint all files in a directory:
```bash
python scripts/spec_linter.py spec/
```

### Command-Line Options

```
usage: spec_linter.py [-h] [-v] [-s] [--fix] path

positional arguments:
  path                  Path to specification file or directory

optional arguments:
  -h, --help            show this help message and exit
  -v, --verbose         Show all warnings and info messages
  -s, --strict          Treat warnings as errors
  --fix                 Automatically fix some issues (experimental)
```

### Examples

#### Lint a single file with verbose output:
```bash
python scripts/spec_linter.py --verbose spec/language/ast_graph_spec.md
```

#### Lint all specs in strict mode:
```bash
python scripts/spec_linter.py --strict spec/
```

#### Lint with automatic fixes:
```bash
python scripts/spec_linter.py --fix spec/
```

## Output Format

The linter provides detailed error messages with:

- **File Path**: Path to the file with the issue
- **Line Number**: Line number where the issue was detected
- **Severity**: ERROR, WARNING, or INFO
- **Rule ID**: Unique identifier for the validation rule
- **Message**: Description of the issue
- **Suggestion**: (Optional) Suggested fix

### Example Output

```
================================================================================
File: spec/language/ast_graph_spec.md
================================================================================
spec/language/ast_graph_spec.md:15 [ERROR] HDR-STS: Invalid status: InvalidStatus. Must be one of: Draft, Active, Deprecated
  Suggestion: Update status to one of the valid values

spec/language/ast_graph_spec.md:42 [WARNING] REQ-EARS: Requirement AST-REQ-001 does not follow EARS pattern
  Suggestion: Use patterns like: THE system SHALL..., WHEN..., WHILE..., WHERE...

spec/language/ast_graph_spec.md:85 [WARNING] FMT-LNG: Line too long (145 characters, max 120)
  Suggestion: Break long lines or use code blocks
```

### Summary

After processing all files, the linter displays a summary:

```
================================================================================
SUMMARY
================================================================================
Files checked: 45
Files passed: 38
Files failed: 7
Total errors: 23
Total warnings: 56
Total info: 12
================================================================================
```

## Exit Codes

- **0**: All checks passed (no errors)
- **1**: One or more errors detected (or warnings in strict mode)

## Rule IDs

The linter uses the following rule ID prefixes:

| Prefix | Category |
|--------|----------|
| `HDR-` | Document Header |
| `SEC-` | Section Structure |
| `REQ-` | Requirements |
| `MATH-` | Mathematical Notation |
| `XREF-` | Cross-References |
| `MRD-` | Mermaid Diagrams |
| `CHG-` | Change Log |
| `FMT-` | Markdown Formatting |
| `FILE-` | File Operations |

## Integration with Development Workflow

### Pre-commit Hook

Add a pre-commit hook to automatically lint specs before committing:

```bash
# .git/hooks/pre-commit
#!/bin/bash
python scripts/spec_linter.py spec/
if [ $? -ne 0 ]; then
    echo "Specification linting failed. Please fix the errors before committing."
    exit 1
fi
```

### VSCode Task

Add to `.vscode/tasks.json`:

```json
{
  "version": "2.0.0",
  "tasks": [
    {
      "label": "Lint Specifications",
      "type": "shell",
      "command": "python",
      "args": [
        "scripts/spec_linter.py",
        "${file}"
      ],
      "group": "test",
      "presentation": {
        "reveal": "always"
      }
    },
    {
      "label": "Lint All Specifications",
      "type": "shell",
      "command": "python",
      "args": [
        "scripts/spec_linter.py",
        "spec/"
      ],
      "group": "test",
      "presentation": {
        "reveal": "always"
      }
    }
  ]
}
```

### CI/CD Integration

Add to your CI pipeline:

```yaml
# Example for GitHub Actions
- name: Lint Specifications
  run: |
    python scripts/spec_linter.py --strict spec/
```

## Testing

Run the unit tests:

```bash
python -m pytest tests/test_spec_linter.py -v
```

Run with coverage:

```bash
python -m pytest tests/test_spec_linter.py --cov=scripts/spec_linter --cov-report=html
```

## Troubleshooting

### Common Issues

#### "File not found" Error

**Problem**: The linter reports a broken link to a file that exists.

**Solution**: Check that the link path is relative to the specification file, not the project root. Use `../` to navigate up directories.

#### "Invalid version format" Error

**Problem**: Version doesn't match MAJOR.MINOR.PATCH format.

**Solution**: Ensure version follows Semantic Versioning:
- MAJOR: Incompatible changes
- MINOR: Backwards-compatible additions
- PATCH: Backwards-compatible bug fixes

Example: `1.2.3` (valid), `1.2` (invalid), `v1.2.3` (invalid)

#### "Missing EARS pattern" Warning

**Problem**: Requirement doesn't use EARS syntax.

**Solution**: Rewrite requirement using EARS patterns:
- Ubiquitous: "THE system SHALL [requirement]"
- Event-Driven: "WHEN [trigger], THE system SHALL [requirement]"
- State-Driven: "WHILE [state], THE system SHALL [requirement]"
- Optional: "WHERE [condition], THE system SHALL [requirement]"

#### "Unbalanced braces" Error

**Problem**: Math expression has mismatched braces.

**Solution**: Count opening and closing braces in the expression. Ensure every `{` has a matching `}`.

## Best Practices

1. **Run Linter Frequently**: Run the linter after making changes to specification files
2. **Fix Errors First**: Address ERROR severity issues before WARNINGs
3. **Use Strict Mode**: Use `--strict` mode for pre-commit hooks and CI/CD
4. **Review Suggestions**: Read the suggested fixes carefully
5. **Keep Change Logs Updated**: Always update the change log when modifying specifications
6. **Use EARS Pattern**: Write all requirements using EARS syntax for clarity
7. **Validate Links**: Check that all cross-references point to existing files
8. **Test Diagrams**: Ensure Mermaid diagrams render correctly

## Contributing

When adding new validation rules:

1. Add a new rule ID following the prefix convention
2. Implement the validation logic in the appropriate method
3. Add unit tests for the new rule
4. Update this README with documentation
5. Test on existing specification files

## License

This tool is part of the Morph project and follows the same license.

## Support

For issues or questions:
1. Check this README for common solutions
2. Review the specification convention document
3. Open an issue on the project repository

## Related Tools

- **format_markdown.py**: Automatically formats markdown files
- **fix_spec_headers.py**: Fixes common header issues
- **fix_spec_conflicts.py**: Resolves specification conflicts

## Changelog

### Version 1.0.0 (2026-01-02)
- Initial release
- Document header validation
- Section structure validation
- Requirements validation (EARS pattern)
- Mathematical notation validation
- Cross-reference validation
- Mermaid diagram validation
- Change log validation
- Markdown formatting validation
- Command-line interface
- Unit tests
- Documentation
