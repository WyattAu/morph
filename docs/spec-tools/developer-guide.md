# Spec-Tools Developer Guide

## Table of Contents

1. [Development Setup](#development-setup)
2. [Code Organization](#code-organization)
3. [Adding New Rules](#adding-new-rules)
4. [Testing Guide](#testing-guide)
5. [Release Process](#release-process)
6. [Contributing](#contributing)

---

## Development Setup

### Prerequisites

- Python 3.8 or higher
- Git
- pip (Python package installer)
- Virtual environment (recommended)

### Setting Up Development Environment

#### 1. Clone the Repository

```bash
git clone https://github.com/morph-project/spec-tools.git
cd spec-tools
```

#### 2. Create Virtual Environment

```bash
# Using venv
python -m venv venv

# Activate on Linux/Mac
source venv/bin/activate

# Activate on Windows
venv\Scripts\activate
```

#### 3. Install Development Dependencies

```bash
# Install package in editable mode
pip install -e .

# Install development dependencies
pip install -e ".[dev]"
```

#### 4. Verify Installation

```bash
spec-tools --version
```

Expected output:
```
spec-tools 1.0.0
```

### Development Tools

#### Code Formatting

```bash
# Format code with Black
black scripts/spec_tools/

# Check formatting
black --check scripts/spec_tools/
```

#### Type Checking

```bash
# Run mypy for type checking
mypy scripts/spec_tools/
```

#### Linting

```bash
# Run pylint
pylint scripts/spec_tools/

# Run flake8
flake8 scripts/spec_tools/
```

### IDE Configuration

#### VS Code

Install recommended extensions:
- Python (Microsoft)
- Pylance (Microsoft)
- Black Formatter (Microsoft)
- mypy (Microsoft)

Create `.vscode/settings.json`:
```json
{
    "python.linting.enabled": true,
    "python.linting.pylintEnabled": true,
    "python.formatting.provider": "black",
    "python.linting.mypyEnabled": true,
    "editor.formatOnSave": true,
    "python.testing.pytestEnabled": true
}
```

#### PyCharm

Configure:
- Settings → Tools → External Tools → Black
- Settings → Tools → External Tools → mypy
- Settings → Tools → Python Integrated Tools → pytest

---

## Code Organization

### Project Structure

```
spec-tools/
├── scripts/
│   ├── spec_tools/
│   │   ├── __init__.py              # Package initialization
│   │   ├── cli/                     # CLI commands
│   │   │   ├── __init__.py
│   │   │   ├── main.py              # Main CLI entry point
│   │   │   └── commands/            # Command handlers
│   │   │       ├── __init__.py
│   │   │       ├── format.py
│   │   │       ├── lint.py
│   │   │       ├── validate.py
│   │   │       ├── check_links.py
│   │   │       ├── check_all.py
│   │   │       └── init_config.py
│   │   ├── config/                  # Configuration management
│   │   │   ├── __init__.py
│   │   │   └── config_manager.py
│   │   ├── exceptions/               # Custom exceptions
│   │   │   ├── __init__.py
│   │   │   └── exceptions.py
│   │   ├── formatting/              # Formatting rules
│   │   │   ├── __init__.py
│   │   │   ├── formatter.py
│   │   │   ├── rules/
│   │   │   │   ├── __init__.py
│   │   │   │   ├── emphasis.py
│   │   │   │   ├── headings.py
│   │   │   │   ├── line_length.py
│   │   │   │   ├── lists.py
│   │   │   │   └── whitespace.py
│   │   │   └── utils/
│   │   │       └── __init__.py
│   │   ├── linting/                 # Linting rules
│   │   │   ├── __init__.py
│   │   │   ├── linter.py
│   │   │   └── rules/
│   │   │       ├── __init__.py
│   │   │       ├── change_log.py
│   │   │       ├── cross_refs.py
│   │   │       ├── header.py
│   │   │       ├── math.py
│   │   │       ├── mermaid.py
│   │   │       ├── requirements.py
│   │   │       └── sections.py
│   │   ├── link_checker/             # Link checking
│   │   │   ├── __init__.py
│   │   │   ├── checker.py
│   │   │   ├── cache/
│   │   │   │   ├── __init__.py
│   │   │   │   └── link_cache.py
│   │   │   ├── parsers/
│   │   │   │   ├── __init__.py
│   │   │   │   ├── file_ref.py
│   │   │   │   └── markdown_link.py
│   │   │   └── validators/
│   │   │       ├── __init__.py
│   │   │       ├── file_exists.py
│   │   │       └── section_exists.py
│   │   ├── models/                  # Data models
│   │   │   ├── __init__.py
│   │   │   └── models.py
│   │   ├── utils/                   # Utility functions
│   │   │   ├── __init__.py
│   │   │   ├── file_utils.py
│   │   │   └── logging_utils.py
│   │   └── validation/               # Validation checks
│   │       ├── __init__.py
│   │       ├── validator.py
│   │       ├── checks/
│   │       │   ├── __init__.py
│   │       │   ├── maintainability.py
│   │       │   ├── performance.py
│   │       │   ├── risk_assessment.py
│   │       │   ├── security.py
│   │       │   ├── traceability.py
│   │       │   └── verification.py
│   │       └── utils/
│   │           └── __init__.py
│   ├── tests/                       # Test suite
│   │   ├── conftest.py
│   │   ├── test_cli/
│   │   ├── test_formatting/
│   │   ├── test_linting/
│   │   ├── test_link_checker/
│   │   ├── test_validation/
│   │   └── test_shared/
│   ├── pyproject.toml               # Project configuration
│   ├── README.md
│   └── LICENSE
└── docs/
    └── spec-tools/
        ├── user-guide.md
        └── developer-guide.md
```

### Module Responsibilities

#### CLI Module (`cli/`)
- **main.py**: Argument parsing and command routing
- **commands/**: Individual command handlers
  - Each command file implements a single CLI command
  - Commands are registered in `main.py`

#### Configuration Module (`config/`)
- **config_manager.py**: Load, save, and validate configuration
- Uses YAML format for configuration files
- Validates configuration values

#### Formatting Module (`formatting/`)
- **formatter.py**: Main formatter class
- **rules/**: Individual formatting rules
  - Each rule implements `FormattingRule` interface
  - Rules are applied in sequence

#### Linting Module (`linting/`)
- **linter.py**: Main linter class
- **rules/**: Individual linting rules
  - Each rule implements `LintingRule` interface
  - Rules are loaded based on configuration

#### Validation Module (`validation/`)
- **validator.py**: Main validator class
- **checks/**: Individual validation checks
  - Each check implements `ValidationCheck` interface
  - Checks are loaded based on configuration

#### Link Checker Module (`link_checker/`)
- **checker.py**: Main link checker class
- **cache/**: Link validation cache
- **parsers/**: Link parsers
- **validators/**: Link validators

#### Models Module (`models/`)
- **models.py**: Data models and enums
- Configuration dataclasses
- Error reporting structures
- Link information structures

#### Utils Module (`utils/`)
- **file_utils.py**: File system utilities
- **logging_utils.py**: Logging utilities

### Design Patterns

#### Strategy Pattern
- Rules and checks use strategy pattern
- Each rule/check implements a common interface
- Easy to add new rules without modifying existing code

#### Factory Pattern
- Rules and checks are loaded dynamically
- Configuration determines which rules to load
- Enables flexible rule selection

#### Builder Pattern
- Configuration objects use dataclasses with defaults
- Easy to construct complex configurations
- Immutable configuration objects

---

## Adding New Rules

### Adding a Formatting Rule

#### 1. Create Rule File

Create a new file in `scripts/spec_tools/formatting/rules/`:

```python
"""
Custom formatting rule description.
"""

import re
from pathlib import Path
from typing import List

from spec_tools.formatting.rules import FormattingRule
from spec_tools.models import LintError, Severity


class CustomFormattingRule(FormattingRule):
    """Custom formatting rule description.
    
    This rule ensures that...
    """

    def __init__(self, enabled: bool = True):
        """Initialize the custom formatting rule.
        
        Args:
            enabled: Whether this rule is enabled (default: True)
        """
        self.enabled = enabled
        # Compile regex patterns here for performance
        self._pattern = re.compile(r"your_pattern")

    def apply(self, content: str) -> str:
        """Apply custom formatting to content.
        
        Args:
            content: Content to format
            
        Returns:
            Content with custom formatting applied
        """
        if not self.enabled:
            return content

        # Apply your formatting logic here
        result = self._pattern.sub(replacement, content)
        return result

    def check(self, content: str, filepath: Path) -> List[LintError]:
        """Check if content complies with custom rule.
        
        Args:
            content: Content to check
            filepath: File path for error reporting
            
        Returns:
            List of formatting violations
        """
        if not self.enabled:
            return []

        errors = []
        lines = content.split("\n")

        for line_num, line in enumerate(lines, start=1):
            # Check for violations
            if self._pattern.search(line):
                errors.append(
                    LintError(
                        file_path=str(filepath),
                        line_number=line_num,
                        column_number=1,
                        severity=Severity.WARNING,
                        rule_id="custom-rule",
                        message="Custom rule violation",
                        suggestion="Fix the issue",
                        context=line,
                    )
                )

        return errors
```

#### 2. Register Rule in Formatter

Update `scripts/spec_tools/formatting/formatter.py`:

```python
from spec_tools.formatting.rules.custom_rule import CustomFormattingRule

class MarkdownFormatter:
    def _load_rules(self) -> List[FormattingRule]:
        rules = []
        
        # Add existing rules
        rules.append(LineLengthRule(self.config.max_line_length))
        rules.append(TrailingWhitespaceRule(self.config.enforce_trailing_whitespace))
        
        # Add your custom rule
        rules.append(CustomFormattingRule(enabled=True))
        
        return rules
```

#### 3. Add Configuration Option

Update `scripts/spec_tools/models/models.py`:

```python
@dataclass
class FormattingConfig:
    """Configuration for formatting operations."""
    
    max_line_length: int = 120
    enforce_trailing_whitespace: bool = True
    normalize_lists: bool = True
    fix_heading_spacing: bool = True
    normalize_emphasis: bool = True
    custom_rule_enabled: bool = True  # Add this
```

Update `scripts/spec_tools/config/config_manager.py`:

```python
@staticmethod
def _parse_config(data: dict, filepath: Path) -> Config:
    formatting_data = data.get("formatting", {})
    formatting = FormattingConfig(
        max_line_length=formatting_data.get("max_line_length", 120),
        enforce_trailing_whitespace=formatting_data.get(
            "enforce_trailing_whitespace", True
        ),
        normalize_lists=formatting_data.get("normalize_lists", True),
        fix_heading_spacing=formatting_data.get("fix_heading_spacing", True),
        normalize_emphasis=formatting_data.get("normalize_emphasis", True),
        custom_rule_enabled=formatting_data.get("custom_rule_enabled", True),  # Add this
    )
```

### Adding a Linting Rule

#### 1. Create Rule File

Create a new file in `scripts/spec_tools/linting/rules/`:

```python
"""
Custom linting rule description.
"""

import re
from pathlib import Path
from typing import List

from spec_tools.linting.rules import LintingRule
from spec_tools.models import LintError, Severity


class CustomLintingRule(LintingRule):
    """Custom linting rule description.
    
    This rule checks that...
    """

    @property
    def description(self) -> str:
        """Get rule description."""
        return "Custom linting rule description"

    def __init__(self):
        """Initialize the custom linting rule."""
        self._pattern = re.compile(r"your_pattern")

    def check(self, content: str, lines: List[str], filepath: Path) -> List[LintError]:
        """Check if content complies with custom rule.
        
        Args:
            content: Full content of file
            lines: List of lines in file
            filepath: File path for error reporting
            
        Returns:
            List of linting errors
        """
        errors = []

        for line_num, line in enumerate(lines, start=1):
            # Check for violations
            if self._pattern.search(line):
                errors.append(
                    LintError(
                        file_path=str(filepath),
                        line_number=line_num,
                        column_number=1,
                        severity=Severity.ERROR,
                        rule_id="custom-linting-rule",
                        message="Custom linting rule violation",
                        suggestion="Fix the issue",
                        context=line,
                    )
                )

        return errors
```

#### 2. Register Rule in Linter

Update `scripts/spec_tools/linting/linter.py`:

```python
from spec_tools.linting.rules.custom_rule import CustomLintingRule

class SpecLinter:
    def _load_rules(self) -> Dict[str, LintingRule]:
        rules = {}
        
        # Add existing rules
        rules["header"] = HeaderValidationRule()
        rules["sections"] = SectionStructureRule()
        
        # Add your custom rule
        rules["custom"] = CustomLintingRule()
        
        return rules
```

### Adding a Validation Check

#### 1. Create Check File

Create a new file in `scripts/spec_tools/validation/checks/`:

```python
"""
Custom validation check description.
"""

from pathlib import Path
from typing import List

from spec_tools.models import LintError, Severity
from spec_tools.validation.checks import ValidationCheck
from spec_tools.validation.utils import (
    extract_section,
    extract_list_items,
    find_section_line,
)


class CustomValidationCheck(ValidationCheck):
    """Validates custom section in specification files.
    
    This check ensures that:
    1. A custom section exists
    2. Required subsections are present
    3. Required content is specified
    """

    @property
    def description(self) -> str:
        """Get description of this check."""
        return "Validates custom section and ensures required content is present"

    def validate(self, content: str, filepath: Path) -> List[LintError]:
        """Validate custom section in the content.
        
        Args:
            content: The content of the specification file
            filepath: Path to the file being validated
            
        Returns:
            List of validation errors found
        """
        errors: List[LintError] = []

        # Check if custom section exists
        custom_section = extract_section(content, "Custom Section")
        if custom_section is None:
            errors.append(
                LintError(
                    file_path=str(filepath),
                    line_number=1,
                    severity=Severity.ERROR,
                    rule_id="CUSTOM-001",
                    message="Custom Section is missing",
                    suggestion="Add a '## Custom Section' section to the specification",
                )
            )
            return errors

        # Find the line number of the section
        section_line = find_section_line(content, "Custom Section")
        if section_line is None:
            section_line = 1

        # Check for required subsections
        subsection = extract_section(custom_section, "Required Subsection")
        if subsection is None:
            errors.append(
                LintError(
                    file_path=str(filepath),
                    line_number=section_line,
                    severity=Severity.ERROR,
                    rule_id="CUSTOM-002",
                    message="Required Subsection is missing",
                    suggestion="Add a '### Required Subsection' subsection to Custom Section",
                )
            )
        else:
            # Check if content is specified
            items = extract_list_items(subsection)
            if not items:
                errors.append(
                    LintError(
                        file_path=str(filepath),
                        line_number=section_line,
                        severity=Severity.ERROR,
                        rule_id="CUSTOM-003",
                        message="No content specified in Required Subsection",
                        suggestion="Add a list of required items",
                    )
                )

        return errors


__all__ = ["CustomValidationCheck"]
```

#### 2. Register Check in Validator

Update `scripts/spec_tools/validation/validator.py`:

```python
from spec_tools.validation.checks.custom_check import CustomValidationCheck

class SpecValidator:
    def _load_checks(self) -> List[ValidationCheck]:
        checks: List[ValidationCheck] = []

        # Add existing checks
        if self.config.check_traceability:
            checks.append(TraceabilityCheck())

        # Add your custom check
        checks.append(CustomValidationCheck())

        return checks
```

### Best Practices for Rules

1. **Use Descriptive Names**: Rule IDs should be descriptive and follow naming convention
2. **Provide Clear Messages**: Error messages should be clear and actionable
3. **Include Suggestions**: Always provide suggestions for fixing issues
4. **Use Appropriate Severity**: Use ERROR for critical issues, WARNING for style issues
5. **Handle Edge Cases**: Consider empty files, missing sections, etc.
6. **Performance**: Compile regex patterns in `__init__` for better performance
7. **Documentation**: Add comprehensive docstrings following Google style

---

## Testing Guide

### Running Tests

#### Run All Tests

```bash
pytest scripts/tests/
```

#### Run Specific Test Module

```bash
pytest scripts/tests/test_formatting/
pytest scripts/tests/test_linting/
pytest scripts/tests/test_validation/
```

#### Run Specific Test

```bash
pytest scripts/tests/test_formatting/test_formatter.py::test_format_file
```

#### Run with Coverage

```bash
pytest --cov=scripts/spec_tools --cov-report=html scripts/tests/
```

#### Run with Verbose Output

```bash
pytest -v scripts/tests/
```

### Writing Tests

#### Test Structure

```python
import pytest
from pathlib import Path
from spec_tools.formatting import MarkdownFormatter
from spec_tools.models import FormattingConfig


class TestCustomRule:
    """Test suite for custom formatting rule."""

    def test_apply_basic(self):
        """Test basic application of custom rule."""
        # Arrange
        config = FormattingConfig()
        formatter = MarkdownFormatter(config)
        content = "input content"
        
        # Act
        result = formatter.apply_rule(content)
        
        # Assert
        assert result == "expected output"

    def test_apply_disabled(self):
        """Test that disabled rule doesn't modify content."""
        # Arrange
        config = FormattingConfig(custom_rule_enabled=False)
        formatter = MarkdownFormatter(config)
        content = "input content"
        
        # Act
        result = formatter.apply_rule(content)
        
        # Assert
        assert result == content

    def test_check_violations(self):
        """Test detection of violations."""
        # Arrange
        config = FormattingConfig()
        formatter = MarkdownFormatter(config)
        content = "content with violations"
        filepath = Path("test.md")
        
        # Act
        result = formatter.check_rule(content, filepath)
        
        # Assert
        assert len(result.errors) > 0
        assert result.errors[0].rule_id == "custom-rule"

    def test_check_no_violations(self):
        """Test that valid content passes check."""
        # Arrange
        config = FormattingConfig()
        formatter = MarkdownFormatter(config)
        content = "valid content"
        filepath = Path("test.md")
        
        # Act
        result = formatter.check_rule(content, filepath)
        
        # Assert
        assert len(result.errors) == 0
```

#### Test Fixtures

Create fixtures in `scripts/tests/conftest.py`:

```python
import pytest
from pathlib import Path
from spec_tools.models import Config, FormattingConfig


@pytest.fixture
def sample_config():
    """Provide a sample configuration."""
    return Config()


@pytest.fixture
def sample_formatting_config():
    """Provide a sample formatting configuration."""
    return FormattingConfig()


@pytest.fixture
def sample_spec_file(tmp_path):
    """Provide a sample specification file."""
    content = """# Sample Specification

## Purpose and Scope
This is a sample specification.

## Requirements
REQ-001: The system shall do something.
"""
    file_path = tmp_path / "sample.md"
    file_path.write_text(content)
    return file_path
```

#### Test Naming Conventions

- Use descriptive test names
- Use `test_` prefix for test methods
- Group related tests in test classes
- Use `test_` prefix for test files

### Test Coverage

#### Coverage Goals

- Aim for > 90% code coverage
- Focus on critical paths
- Test error conditions
- Test edge cases

#### Coverage Report

```bash
# Generate HTML coverage report
pytest --cov=scripts/spec_tools --cov-report=html scripts/tests/

# View report
open htmlcov/index.html
```

### Integration Tests

Integration tests are in `scripts/tests/integration/`:

```python
import pytest
from pathlib import Path
from spec_tools.cli.commands import run_format_command
from spec_tools.models import Config


def test_format_workflow(tmp_path):
    """Test complete formatting workflow."""
    # Create test file
    test_file = tmp_path / "test.md"
    test_file.write_text("# Test\n\nContent")
    
    # Run format command
    config = Config()
    result = run_format_command(test_file, config)
    
    # Verify result
    assert result == 0
    assert test_file.exists()
```

---

## Release Process

### Version Management

#### Semantic Versioning

Spec-Tools follows Semantic Versioning (SemVer): `MAJOR.MINOR.PATCH`

- **MAJOR**: Incompatible API changes
- **MINOR**: Backwards-compatible functionality additions
- **PATCH**: Backwards-compatible bug fixes

#### Update Version

Update version in `scripts/spec_tools/__init__.py`:

```python
__version__ = "1.0.1"  # Update this
```

Update version in `scripts/pyproject.toml`:

```toml
[project]
name = "spec-tools"
version = "1.0.1"  # Update this
```

### Pre-Release Checklist

- [ ] All tests pass
- [ ] Code coverage > 90%
- [ ] Documentation updated
- [ ] CHANGELOG.md updated
- [ ] Version numbers updated
- [ ] No breaking changes without migration guide
- [ ] All dependencies up to date

### Building the Package

#### Build Wheel and Source Distribution

```bash
cd scripts
python -m build
```

This creates:
- `dist/spec_tools-1.0.1-py3-none-any.whl`
- `dist/spec-tools-1.0.1.tar.gz`

#### Verify Build

```bash
# Check wheel
twine check dist/spec_tools-1.0.1-py3-none-any.whl

# Check source distribution
twine check dist/spec-tools-1.0.1.tar.gz
```

### Testing the Package

#### Install from Wheel

```bash
pip install dist/spec_tools-1.0.1-py3-none-any.whl
```

#### Test Installation

```bash
spec-tools --version
spec-tools format --help
```

#### Uninstall

```bash
pip uninstall spec-tools
```

### Publishing to PyPI

#### Configure PyPI Credentials

```bash
# Create ~/.pypirc
[pypi]
username = __token__
password = pypi-<your-token>
```

#### Upload to PyPI

```bash
# Upload to test PyPI first
twine upload --repository testpypi dist/*

# Test installation from test PyPI
pip install --index-url https://test.pypi.org/simple/ spec-tools

# Upload to production PyPI
twine upload dist/*
```

### Creating a GitHub Release

#### Tag the Release

```bash
git tag -a v1.0.1 -m "Release version 1.0.1"
git push origin v1.0.1
```

#### Create Release on GitHub

1. Go to GitHub repository
2. Click "Releases" → "Create a new release"
3. Select tag `v1.0.1`
4. Add release notes from CHANGELOG.md
5. Attach distribution files from `dist/`
6. Click "Publish release"

### Post-Release Tasks

- [ ] Announce release on project channels
- [ ] Update documentation website
- [ ] Close related issues
- [ ] Create milestone for next release
- [ ] Monitor for bug reports

---

## Contributing

### Code Style

#### Python Style Guide

- Follow PEP 8
- Use 4 spaces for indentation
- Maximum line length: 120 characters
- Use type hints for all functions
- Use docstrings for all public functions and classes

#### Docstring Style

Use Google style docstrings:

```python
def example_function(param1: str, param2: int) -> bool:
    """Brief description of function.
    
    Longer description if needed.
    
    Args:
        param1: Description of param1
        param2: Description of param2
        
    Returns:
        Description of return value
        
    Raises:
        ValueError: If param1 is invalid
    """
    pass
```

### Commit Messages

Follow conventional commits format:

```
<type>(<scope>): <subject>

<body>

<footer>
```

Types:
- `feat`: New feature
- `fix`: Bug fix
- `docs`: Documentation changes
- `style`: Code style changes (formatting)
- `refactor`: Code refactoring
- `test`: Adding or updating tests
- `chore`: Maintenance tasks

Examples:
```
feat(formatter): add custom formatting rule

Add support for custom formatting rules with configuration.

Closes #123
```

### Pull Request Process

1. Fork the repository
2. Create a feature branch
3. Make your changes
4. Add tests for new functionality
5. Ensure all tests pass
6. Update documentation
7. Submit a pull request

#### Pull Request Template

```markdown
## Description
Brief description of changes

## Type of Change
- [ ] Bug fix
- [ ] New feature
- [ ] Breaking change
- [ ] Documentation update

## Testing
- [ ] Unit tests added/updated
- [ ] Integration tests added/updated
- [ ] All tests pass

## Checklist
- [ ] Code follows style guidelines
- [ ] Self-review completed
- [ ] Documentation updated
- [ ] No new warnings generated
- [ ] Tests added/updated
- [ ] All tests passing
```

### Issue Reporting

When reporting issues, include:

1. **Version**: Spec-Tools version
2. **Python Version**: Python version
3. **OS**: Operating system
4. **Steps to Reproduce**: Detailed steps
5. **Expected Behavior**: What should happen
6. **Actual Behavior**: What actually happens
7. **Error Messages**: Any error messages
8. **Sample Files**: Minimal reproducible example

### Getting Help

- **Documentation**: [User Guide](user-guide.md)
- **API Reference**: [API Documentation](../api/)
- **Issues**: [GitHub Issues](https://github.com/morph-project/spec-tools/issues)
- **Discussions**: [GitHub Discussions](https://github.com/morph-project/spec-tools/discussions)

---

## Additional Resources

- [User Guide](user-guide.md)
- [Specification Convention](../conventions/specification_convention.md)
- [GitHub Repository](https://github.com/morph-project/spec-tools)
- [PEP 8 - Style Guide](https://peps.python.org/pep-0008/)
- [PEP 257 - Docstring Conventions](https://peps.python.org/pep-0257/)
- [Semantic Versioning](https://semver.org/)
