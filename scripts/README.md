# Spec Tools

A modular, enterprise-grade Python package for specification file management, including formatting, linting, validation, and link checking capabilities.

Copyright 2026 Morph Project

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

## Overview

Spec Tools provides a comprehensive toolkit for working with Markdown specification files following the Morph project's specification convention. It helps maintain consistency, quality, and correctness across your specification documents.

## Features

- **Formatting**: Automatically format specification files according to convention standards
- **Linting**: Check for common issues and violations of specification conventions
- **Validation**: Validate specification structure and content against requirements
- **Link Checking**: Verify all links and references are valid and up-to-date
- **Configuration**: Flexible YAML-based configuration with sensible defaults
- **CLI Interface**: Unified command-line interface for all operations
- **CI/CD Integration**: Easy integration with GitHub Actions, Jenkins, and pre-commit hooks

## Installation

### From Source

```bash
# Install in development mode
pip install -e scripts/
```

### With Development Dependencies

```bash
pip install -e "scripts/[dev]"
```

## Quick Start

### Initialize Configuration

Create a default configuration file:

```bash
spec-tools init-config
```

This creates a `.spec-tools.yaml` file in current directory with default settings.

### Format Specification Files

Format all specification files in a directory:

```bash
spec-tools format spec/
```

Check formatting without modifying files:

```bash
spec-tools format spec/ --check
```

### Lint Specification Files

Lint specification files for convention violations:

```bash
spec-tools lint spec/
```

Treat warnings as errors:

```bash
spec-tools lint spec/ --strict
```

### Validate Specification Files

Validate specification files against to convention:

```bash
spec-tools validate spec/
```

Check specific validation aspects:

```bash
spec-tools validate spec/ --check-traceability --check-security
```

### Check Links

Verify all links in specification files:

```bash
spec-tools check-links spec/
```

Output results in JSON format:

```bash
spec-tools check-links spec/ --format json --output link-report.json
```

### Run All Checks

Run all checks (format, lint, validate, check-links):

```bash
spec-tools check-all spec/
```

## Configuration

Spec Tools uses YAML configuration files for customization. Create a `.spec-tools.yaml` file in your project root:

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
  format: text  # text or json
  verbose: false
  quiet: false
  color_output: true
```

## Usage Examples

### Python API

```python
from pathlib import Path
from spec_tools import ConfigManager
from spec_tools.formatting import MarkdownFormatter
from spec_tools.linting import SpecLinter
from spec_tools.validation import SpecValidator
from spec_tools.link_checker import SpecLinkChecker

# Load configuration
config = ConfigManager.load_config(Path(".spec-tools.yaml"))

# Format files
formatter = MarkdownFormatter(config.formatting)
modified = formatter.format_directory(Path("spec/"))
print(f"Modified {modified} files")

# Lint files
linter = SpecLinter(config.linting)
results = linter.lint_directory(Path("spec/"))
for result in results:
    if not result.passed:
        print(f"Errors in {result.file_path}: {result.error_count}")

# Validate files
validator = SpecValidator(config.validation)
results = validator.validate_directory(Path("spec/"))
for result in results:
    if not result.passed:
        print(f"Validation failed for {result.file_path}")

# Check links
link_checker = SpecLinkChecker(config.link_checking)
report = link_checker.check_directory(Path("spec/"))
if not report.passed:
    print(f"Found {report.invalid_count} invalid links")
```

### CLI with Custom Configuration

```bash
# Use custom configuration file
spec-tools format spec/ --config my-config.yaml

# Run with verbose output
spec-tools lint spec/ --verbose

# Run in quiet mode (errors only)
spec-tools validate spec/ --quiet

# Output in JSON format
spec-tools check-links spec/ --format json
```

## Development

### Setting Up Development Environment

```bash
# Clone the repository
git clone https://github.com/morph/spec-tools.git
cd spec-tools

# Install in development mode with dependencies
pip install -e ".[dev]"
```

### Running Tests

```bash
# Run all tests
pytest

# Run with coverage
pytest --cov=spec_tools --cov-report=html

# Run specific test file
pytest tests/test_formatting/test_formatter.py
```

### Code Quality

```bash
# Format code with Black
black spec_tools/

# Lint with Ruff
ruff check spec_tools/

# Type check with mypy
mypy spec_tools/
```

## Project Structure

```
spec_tools/
├── __init__.py           # Package initialization
├── exceptions/           # Custom exception classes
│   ├── __init__.py
│   └── exceptions.py
├── models/              # Data models and enums
│   ├── __init__.py
│   └── models.py
├── config/              # Configuration management
│   ├── __init__.py
│   └── config_manager.py
├── utils/               # Utility functions
│   ├── __init__.py
│   ├── logging_utils.py
│   └── file_utils.py
├── formatting/          # Formatting module (Phase 2)
├── linting/             # Linting module (Phase 2)
├── validation/          # Validation module (Phase 2)
├── link_checker/        # Link checking module (Phase 2)
└── cli/                 # CLI interface (Phase 4)
```

## CI/CD Integration

### GitHub Actions

```yaml
name: Specification Validation

on:
  push:
    branches: [main, develop]
    paths:
      - 'spec/**'
  pull_request:
    branches: [main, develop]
    paths:
      - 'spec/**'

jobs:
  validate:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v3

      - name: Set up Python
        uses: actions/setup-python@v4
        with:
          python-version: '3.11'

      - name: Install spec-tools
        run: pip install -e scripts/

      - name: Format check
        run: spec-tools format spec/ --check

      - name: Lint specifications
        run: spec-tools lint spec/ --strict

      - name: Validate specifications
        run: spec-tools validate spec/

      - name: Check links
        run: spec-tools check-links spec/
```

### Pre-commit Hook

```yaml
# .pre-commit-config.yaml
repos:
  - repo: local
    hooks:
      - id: spec-format
        name: Format specifications
        entry: spec-tools format
        language: system
        files: \.md$
        pass_filenames: true

      - id: spec-lint
        name: Lint specifications
        entry: spec-tools lint
        language: system
        files: \.md$
        pass_filenames: true

      - id: spec-validate
        name: Validate specifications
        entry: spec-tools validate
        language: system
        files: \.md$
        pass_filenames: true
```

## Contributing

Contributions are welcome! Please follow these guidelines:

1. Fork the repository
2. Create a feature branch (`git checkout -b feature/amazing-feature`)
3. Make your changes
4. Add tests for new functionality
5. Ensure all tests pass (`pytest`)
6. Ensure code quality checks pass (`black`, `ruff`, `mypy`)
7. Commit your changes (`git commit -m 'Add amazing feature'`)
8. Push to the branch (`git push origin feature/amazing-feature`)
9. Open a Pull Request

### Code Style

- Follow PEP 8 for Python code
- Use type hints for all public functions
- Write comprehensive docstrings (Google or NumPy style)
- Keep functions focused and single-purpose
- Write tests for all new functionality

## License

This project is licensed under the Apache License, Version 2.0 - see the [LICENSE](LICENSE) file for details.

## Support

For issues, questions, or contributions, please visit:

- GitHub Issues: https://github.com/morph/spec-tools/issues
- Documentation: https://morph.dev/spec-tools

## Roadmap

- [ ] Phase 2: Core Module Implementation (formatting, linting, validation, link checking)
- [ ] Phase 3: Enhanced Validation Features
- [ ] Phase 4: CLI and Integration
- [ ] Phase 5: Testing and Quality Assurance
- [ ] Phase 6: Documentation and Deployment

## Acknowledgments

Built for the Morph project specification management needs.
