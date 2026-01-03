# Specification Link Checker

## Overview

The Specification Link Checker is a Python tool that validates all cross-references in Morph specification files. It detects broken links, orphaned section references, duplicate links, and self-references to ensure specification integrity.

## Features

- **Markdown Link Detection**: Finds all `[text](url)` style links
- **Section Reference Validation**: Checks that `#section` references exist
- **File Existence Checking**: Verifies that referenced files exist
- **Orphaned Section Detection**: Identifies references to non-existent sections
- **Duplicate Link Detection**: Finds links used multiple times in the same file
- **Self-Reference Detection**: Identifies references to the same file
- **Multiple Output Formats**: Text and JSON output
- **Report Generation**: Saves detailed reports to file
- **Verbose Mode**: Shows detailed checking progress

## Installation

No installation required. The tool is a standalone Python script.

```bash
# Ensure Python 3.7+ is installed
python3 --version

# Make script executable (optional)
chmod +x scripts/spec_link_checker.py
```

## Usage

### Basic Usage

Check all specification files in the default `spec/` directory:

```bash
python scripts/spec_link_checker.py
```

### Command-Line Options

```
usage: spec_link_checker.py [-h] [--spec-dir SPEC_DIR] [--output OUTPUT]
                           [--format {text,json}] [--verbose]

Validate cross-references in Morph specification files

optional arguments:
  -h, --help            Show help message and exit
  --spec-dir SPEC_DIR    Directory containing specification files (default: spec)
  --output OUTPUT, -o OUTPUT
                        Output file path for report (default: stdout)
  --format {text,json}, -f {text,json}
                        Output format (default: text)
  --verbose, -v         Show verbose output
```

### Examples

#### Check Custom Directory

```bash
python scripts/spec_link_checker.py --spec-dir docs/specs/
```

#### Save Report to File

```bash
# Save text report
python scripts/spec_link_checker.py --output link_report.txt

# Save JSON report
python scripts/spec_link_checker.py --output report.json --format json
```

#### Verbose Output

```bash
python scripts/spec_link_checker.py --verbose
```

#### Combined Options

```bash
python scripts/spec_link_checker.py \
  --spec-dir spec/ \
  --output report.json \
  --format json \
  --verbose
```

## Link Types Detected

### 1. Markdown Links

Standard markdown links with file references:

```markdown
[Text](spec/other_file.md)
[Text](spec/other_file.md#section)
```

### 2. Section References

References to sections within the same file:

```markdown
[Text](#section-name)
```

### 3. File References

Plain file references (not in markdown links):

```markdown
See spec/other_file.md for details.
```

### 4. External Links

HTTP/HTTPS links (always considered valid):

```markdown
[Text](https://example.com)
[Text](http://example.com)
```

## Report Format

### Text Report

```
================================================================================
SPECIFICATION LINK CHECKER REPORT
================================================================================

SUMMARY
--------------------------------------------------------------------------------
Total Files Checked:  42
Total Links Found:    156
Valid Links:         150
Broken Links:        3
Orphaned Sections:   2
Duplicate Links:     5
Self-References:     8

BROKEN LINKS
--------------------------------------------------------------------------------

spec/type/type_system_spec.md:
  Line 85: [effect system](spec/type/effect_system_spec.md)
    Error: File 'spec/type/effect_system_spec.md' does not exist

spec/language/morph_language_spec.md:
  Line 120: [syntax translation](spec/language/syntax_translation_spec.md)
    Error: File 'spec/language/syntax_translation_spec.md' does not exist

ORPHANED SECTION REFERENCES
--------------------------------------------------------------------------------

spec/concurrency/execution_model_spec.md:
  Line 76: [scheduling modes](spec/concurrency/scheduling_modes_spec.md#nonexistent)
    Error: Section 'nonexistent' not found in 'spec/concurrency/scheduling_modes_spec.md'

DUPLICATE LINKS
--------------------------------------------------------------------------------

spec/type/type_system_spec.md:
  spec/memory/memory_model_spec.md (used 3 times)
  spec/concurrency/execution_model_spec.md (used 2 times)

================================================================================
❌ FOUND ISSUES
================================================================================
```

### JSON Report

```json
{
  "summary": {
    "total_files": 42,
    "total_links": 156,
    "valid_links": 150,
    "broken_links": 3,
    "orphaned_sections": 2,
    "duplicate_links": 5,
    "self_references": 8
  },
  "files": [
    {
      "path": "spec/type/type_system_spec.md",
      "total_links": 12,
      "valid_links": 10,
      "broken_links": [
        {
          "line": 85,
          "text": "effect system",
          "url": "spec/type/effect_system_spec.md",
          "error": "File 'spec/type/effect_system_spec.md' does not exist"
        }
      ],
      "orphaned_sections": [],
      "duplicate_links": [
        {"url": "spec/memory/memory_model_spec.md", "count": 3}
      ],
      "self_references": []
    }
  ]
}
```

## Exit Codes

- `0`: All links are valid
- `1`: Found broken links or orphaned sections

## Integration with CI/CD

### GitHub Actions

```yaml
name: Check Specification Links

on: [push, pull_request]

jobs:
  link-check:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v2
      - name: Set up Python
        uses: actions/setup-python@v2
        with:
          python-version: '3.9'
      - name: Check links
        run: |
          python scripts/spec_link_checker.py --format json --output report.json
      - name: Upload report
        if: always()
        uses: actions/upload-artifact@v2
        with:
          name: link-check-report
          path: report.json
```

### GitLab CI

```yaml
link-check:
  image: python:3.9
  script:
    - python scripts/spec_link_checker.py --format json --output report.json
  artifacts:
    paths:
      - report.json
    when: always
```

## Best Practices

### 1. Run Regularly

Run the link checker regularly to catch issues early:

```bash
# Add to pre-commit hook
python scripts/spec_link_checker.py
```

### 2. Fix Issues Promptly

Address broken links and orphaned sections immediately to maintain specification integrity.

### 3. Use Descriptive Link Text

Use descriptive link text that clearly indicates the target:

```markdown
# Good
[Effect System Specification](spec/type/effect_system_spec.md)

# Avoid
[here](spec/type/effect_system_spec.md)
```

### 4. Validate Section Names

Ensure section names in links match the actual section headers:

```markdown
# Section header
## Section Name

# Correct link
[Section Name](#section-name)

# Incorrect link
[Section Name](#section_name)  # Wrong separator
```

### 5. Avoid Duplicate Links

Consider consolidating duplicate links or using a reference section:

```markdown
# Instead of repeating the same link multiple times
See [Effect System](spec/type/effect_system_spec.md) for details.
See [Effect System](spec/type/effect_system_spec.md) for more information.

# Use a reference section
## References

- [Effect System Specification](spec/type/effect_system_spec.md)
```

## Troubleshooting

### Issue: "File does not exist" Error

**Cause**: Referenced file path is incorrect or file was moved/deleted.

**Solution**:
1. Verify the file exists at the specified path
2. Check for typos in the file name
3. Update the link to point to the correct file

### Issue: "Section not found" Error

**Cause**: Section name in link doesn't match the actual section header.

**Solution**:
1. Check the section header in the target file
2. Normalize the section name: lowercase, replace spaces with hyphens
3. Update the link to use the correct section name

### Issue: False Positives for External Links

**Cause**: External links are always considered valid.

**Solution**: This is by design. Use external link checking tools for HTTP/HTTPS links.

### Issue: Performance Issues with Large Spec Suites

**Cause**: Checking many files can be slow.

**Solution**:
1. Use `--verbose` to see progress
2. Consider checking only changed files in CI/CD
3. Cache section headers for faster repeated checks

## Development

### Running Tests

```bash
# Run all tests
python tests/test_spec_link_checker.py

# Run specific test class
python -m unittest tests.test_spec_link_checker.TestLinkDetection

# Run with verbose output
python tests/test_spec_link_checker.py -v
```

### Adding New Features

1. Add new detection patterns to `_find_markdown_links()` or `_find_file_references()`
2. Add validation logic to `_validate_link()`
3. Update report generation in `_print_text_report()` or `_print_json_report()`
4. Add unit tests to `tests/test_spec_link_checker.py`

## Contributing

When contributing to the link checker:

1. Follow PEP 8 style guidelines
2. Add unit tests for new features
3. Update this README with new options or features
4. Ensure backward compatibility with existing usage

## License

This tool is part of the Morph project and follows the same license.

## Support

For issues, questions, or contributions:

- Open an issue on the Morph repository
- Contact the Morph development team
- Check the project documentation for more information

## Changelog

### Version 1.0.0 (2026-01-02)

- Initial release
- Markdown link detection
- Section reference validation
- File existence checking
- Orphaned section detection
- Duplicate link detection
- Self-reference detection
- Text and JSON output formats
- Report generation
- Comprehensive unit tests
- Documentation
