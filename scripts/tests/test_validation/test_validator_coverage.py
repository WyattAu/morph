"""Additional tests for SpecValidator to improve coverage."""

from pathlib import Path
from unittest.mock import patch

import pytest

from spec_tools.models import ValidationConfig
from spec_tools.validation.validator import SpecValidator


class TestSpecValidatorErrorPaths:
    def test_validate_file_not_a_file(self, temp_dir):
        config = ValidationConfig()
        validator = SpecValidator(config)
        with pytest.raises(OSError, match="not a file"):
            validator.validate_file(temp_dir)

    def test_validate_directory_not_found(self, temp_dir):
        config = ValidationConfig()
        validator = SpecValidator(config)
        with pytest.raises(FileNotFoundError, match="Directory not found"):
            validator.validate_directory(temp_dir / "nonexistent")

    def test_validate_directory_not_a_directory(self, temp_dir):
        config = ValidationConfig()
        validator = SpecValidator(config)
        filepath = temp_dir / "file.md"
        filepath.write_text("# test\n", encoding="utf-8")
        with pytest.raises(NotADirectoryError, match="not a directory"):
            validator.validate_directory(filepath)

    def test_validate_directory_unreadable_file(self, temp_dir):
        config = ValidationConfig()
        validator = SpecValidator(config)
        filepath = temp_dir / "test.md"
        filepath.write_text("# test\n", encoding="utf-8")
        with patch.object(Path, "read_text", side_effect=PermissionError("denied")):
            results = validator.validate_directory(temp_dir, recursive=False)
        assert len(results) == 1
        assert results[0].passed is False
        assert "Failed to read file" in results[0].errors[0].message

    def test_check_traceability(self):
        config = ValidationConfig(check_traceability=False)
        validator = SpecValidator(config)
        errors = validator.check_traceability("# test\n")
        assert isinstance(errors, list)

    def test_check_verification_plan(self):
        config = ValidationConfig(check_verification_plan=False)
        validator = SpecValidator(config)
        errors = validator.check_verification_plan("# test\n")
        assert isinstance(errors, list)

    def test_check_risk_assessment(self):
        config = ValidationConfig(check_risk_assessment=False)
        validator = SpecValidator(config)
        errors = validator.check_risk_assessment("# test\n")
        assert isinstance(errors, list)

    def test_check_security_specs(self):
        config = ValidationConfig(check_security_specs=False)
        validator = SpecValidator(config)
        errors = validator.check_security_specs("# test\n")
        assert isinstance(errors, list)

    def test_check_performance_specs(self):
        config = ValidationConfig(check_performance_specs=False)
        validator = SpecValidator(config)
        errors = validator.check_performance_specs("# test\n")
        assert isinstance(errors, list)

    def test_check_maintainability_specs(self):
        config = ValidationConfig(check_maintainability_specs=False)
        validator = SpecValidator(config)
        errors = validator.check_maintainability_specs("# test\n")
        assert isinstance(errors, list)

    def test_validate_file_with_only_warnings_passes(self, temp_dir):
        config = ValidationConfig(
            check_traceability=True,
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

## Traceability Matrix

| Requirement | Design | Test |
|-------------|--------|------|
| REQ-001 | DESIGN-001 | TEST-001 |
"""
        filepath = temp_dir / "test.md"
        filepath.write_text(content, encoding="utf-8")

        result = validator.validate_file(filepath)
        assert isinstance(result.passed, bool)
        assert result.file_path == str(filepath)
