"""
Unit tests for SpecValidator.
"""

from pathlib import Path

import pytest

from spec_tools.validation.validator import SpecValidator
from spec_tools.models import ValidationConfig, Severity


class TestSpecValidator:
    """Test cases for SpecValidator."""

    def test_init_default_config(self):
        """Test SpecValidator initialization with default config."""
        config = ValidationConfig()
        validator = SpecValidator(config)
        assert validator.config == config
        assert len(validator.checks) == 6

    def test_init_custom_config(self):
        """Test SpecValidator initialization with custom config."""
        config = ValidationConfig(
            check_traceability=False,
            check_verification_plan=False,
            check_risk_assessment=False,
            check_security_specs=False,
            check_performance_specs=False,
            check_maintainability_specs=False,
        )
        validator = SpecValidator(config)
        assert validator.config == config
        assert len(validator.checks) == 0

    def test_load_checks_all_enabled(self):
        """Test that all checks are loaded when enabled."""
        config = ValidationConfig()
        validator = SpecValidator(config)
        check_names = list(validator.checks.keys())
        assert "traceability" in check_names
        assert "verification_plan" in check_names
        assert "risk_assessment" in check_names
        assert "security_specs" in check_names
        assert "performance_specs" in check_names
        assert "maintainability_specs" in check_names

    def test_load_checks_some_disabled(self):
        """Test that only enabled checks are loaded."""
        config = ValidationConfig(
            check_traceability=False,
            check_verification_plan=False,
        )
        validator = SpecValidator(config)
        check_names = list(validator.checks.keys())
        assert "traceability" not in check_names
        assert "verification_plan" not in check_names
        assert "risk_assessment" in check_names
        assert "security_specs" in check_names
        assert "performance_specs" in check_names
        assert "maintainability_specs" in check_names

    def test_validate_file_no_errors(self, temp_dir):
        """Test validate_file() with file that has no errors."""
        config = ValidationConfig()
        validator = SpecValidator(config)

        content = """# Specification

## Requirements

### REQ-001: Basic Requirement

The system SHALL provide basic functionality.

**Traceability:**
- Design: DESIGN-001
- Implementation: IMPL-001
- Test: TEST-001

## Verification Plan

1. Unit tests
2. Integration tests
3. Acceptance tests

## Risk Assessment

| Risk | Probability | Impact | Mitigation |
|-------|-------------|--------|------------|
| Database failure | Medium | High | Replication |

## Security Specifications

The system SHALL implement authentication.

## Performance Specifications

The system SHALL respond within 200ms.

## Maintainability Specifications

The system SHALL maintain 80% code coverage.
"""
        filepath = temp_dir / "test.md"
        filepath.write_text(content, encoding="utf-8")

        result = validator.validate_file(filepath)
        assert result.passed is True
        assert len(result.errors) == 0

    def test_validate_file_with_errors(self, temp_dir):
        """Test validate_file() with file that has errors."""
        config = ValidationConfig()
        validator = SpecValidator(config)

        content = """# Specification

## Requirements

### REQ-001: Basic Requirement

The system SHALL provide basic functionality.
"""
        filepath = temp_dir / "test.md"
        filepath.write_text(content, encoding="utf-8")

        result = validator.validate_file(filepath)
        assert result.passed is False
        assert len(result.errors) > 0

    def test_validate_file_not_found(self, temp_dir):
        """Test validate_file() with non-existent file."""
        config = ValidationConfig()
        validator = SpecValidator(config)

        filepath = temp_dir / "nonexistent.md"

        with pytest.raises(Exception) as exc_info:
            validator.validate_file(filepath)
        assert "File not found" in str(exc_info.value)

    def test_validate_directory_single_file(self, temp_dir):
        """Test validate_directory() with single file."""
        config = ValidationConfig()
        validator = SpecValidator(config)

        content = """# Specification

## Requirements

### REQ-001: Basic Requirement

The system SHALL provide basic functionality.

**Traceability:**
- Design: DESIGN-001
- Implementation: IMPL-001
- Test: TEST-001

## Verification Plan

1. Unit tests

## Risk Assessment

| Risk | Probability | Impact | Mitigation |
|-------|-------------|--------|------------|
| Database failure | Medium | High | Replication |

## Security Specifications

The system SHALL implement authentication.

## Performance Specifications

The system SHALL respond within 200ms.

## Maintainability Specifications

The system SHALL maintain 80% code coverage.
"""
        (temp_dir / "test.md").write_text(content, encoding="utf-8")

        results = validator.validate_directory(temp_dir, recursive=False)
        assert len(results) == 1

    def test_validate_directory_multiple_files(self, temp_dir):
        """Test validate_directory() with multiple files."""
        config = ValidationConfig()
        validator = SpecValidator(config)

        content = """# Specification

## Requirements

### REQ-001: Basic Requirement

The system SHALL provide basic functionality.

**Traceability:**
- Design: DESIGN-001
- Implementation: IMPL-001
- Test: TEST-001

## Verification Plan

1. Unit tests

## Risk Assessment

| Risk | Probability | Impact | Mitigation |
|-------|-------------|--------|------------|
| Database failure | Medium | High | Replication |

## Security Specifications

The system SHALL implement authentication.

## Performance Specifications

The system SHALL respond within 200ms.

## Maintainability Specifications

The system SHALL maintain 80% code coverage.
"""
        (temp_dir / "test1.md").write_text(content, encoding="utf-8")
        (temp_dir / "test2.md").write_text(content, encoding="utf-8")
        (temp_dir / "test3.md").write_text(content, encoding="utf-8")

        results = validator.validate_directory(temp_dir, recursive=False)
        assert len(results) == 3

    def test_validate_directory_recursive(self, temp_dir):
        """Test validate_directory() with recursive option."""
        config = ValidationConfig()
        validator = SpecValidator(config)

        content = """# Specification

## Requirements

### REQ-001: Basic Requirement

The system SHALL provide basic functionality.

**Traceability:**
- Design: DESIGN-001
- Implementation: IMPL-001
- Test: TEST-001

## Verification Plan

1. Unit tests

## Risk Assessment

| Risk | Probability | Impact | Mitigation |
|-------|-------------|--------|------------|
| Database failure | Medium | High | Replication |

## Security Specifications

The system SHALL implement authentication.

## Performance Specifications

The system SHALL respond within 200ms.

## Maintainability Specifications

The system SHALL maintain 80% code coverage.
"""
        (temp_dir / "test1.md").write_text(content, encoding="utf-8")
        subdir = temp_dir / "subdir"
        subdir.mkdir()
        (subdir / "test2.md").write_text(content, encoding="utf-8")

        results = validator.validate_directory(temp_dir, recursive=True)
        assert len(results) == 2

    def test_validate_directory_empty(self, temp_dir):
        """Test validate_directory() with empty directory."""
        config = ValidationConfig()
        validator = SpecValidator(config)

        results = validator.validate_directory(temp_dir, recursive=False)
        assert len(results) == 0

    def test_validate_file_with_disabled_checks(self, temp_dir):
        """Test validate_file() respects disabled checks."""
        config = ValidationConfig(
            check_traceability=False,
            check_verification_plan=False,
            check_risk_assessment=False,
            check_security_specs=False,
            check_performance_specs=False,
            check_maintainability_specs=False,
        )
        validator = SpecValidator(config)

        content = """# Specification

## Requirements

### REQ-001: Basic Requirement

The system SHALL provide basic functionality.
"""
        filepath = temp_dir / "test.md"
        filepath.write_text(content, encoding="utf-8")

        result = validator.validate_file(filepath)
        assert result.passed is True

    def test_validate_file_error_details(self, temp_dir):
        """Test validate_file() provides detailed error information."""
        config = ValidationConfig()
        validator = SpecValidator(config)

        content = """# Specification

## Requirements

### REQ-001: Basic Requirement

The system SHALL provide basic functionality.
"""
        filepath = temp_dir / "test.md"
        filepath.write_text(content, encoding="utf-8")

        result = validator.validate_file(filepath)
        assert result.file_path == str(filepath)
        assert len(result.errors) > 0

        # Check that errors have required fields
        for error in result.errors:
            assert error.file_path == str(filepath)
            assert error.line_number > 0
            assert error.rule_id != ""
            assert error.message != ""

    def test_validate_file_encoding(self, temp_dir):
        """Test validate_file() handles UTF-8 encoding correctly."""
        config = ValidationConfig()
        validator = SpecValidator(config)

        content = """# Specification with unicode: café

## Requirements

### REQ-001: Basic Requirement

The system SHALL provide basic functionality with emoji: 🎉

**Traceability:**
- Design: DESIGN-001
- Implementation: IMPL-001
- Test: TEST-001

## Verification Plan

1. Unit tests

## Risk Assessment

| Risk | Probability | Impact | Mitigation |
|-------|-------------|--------|------------|
| Database failure | Medium | High | Replication |

## Security Specifications

The system SHALL implement authentication.

## Performance Specifications

The system SHALL respond within 200ms.

## Maintainability Specifications

The system SHALL maintain 80% code coverage.
"""
        filepath = temp_dir / "test.md"
        filepath.write_text(content, encoding="utf-8")

        result = validator.validate_file(filepath)
        assert result.passed is True

    def test_validate_file_empty(self, temp_dir):
        """Test validate_file() with empty file."""
        config = ValidationConfig()
        validator = SpecValidator(config)

        filepath = temp_dir / "test.md"
        filepath.write_text("", encoding="utf-8")

        result = validator.validate_file(filepath)
        assert result.passed is False
        assert len(result.errors) > 0
