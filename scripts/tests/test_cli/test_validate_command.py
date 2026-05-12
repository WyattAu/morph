"""Tests for CLI validate command."""

from pathlib import Path
from types import SimpleNamespace
from unittest.mock import MagicMock, patch

import pytest

from spec_tools.cli.commands import validate as val_module
from spec_tools.cli.commands.validate import (
    run_validate_command,
    _validate_file,
    _validate_directory,
)
from spec_tools.exceptions import SpecToolsError
from spec_tools.models import Config, ValidationResult, Severity, LintError


def _make_args(path, **kwargs):
    defaults = dict(
        check_traceability=False,
        check_security=False,
        check_performance=False,
        check_maintainability=False,
        check_risk=False,
        check_verification=False,
    )
    defaults.update(kwargs)
    return SimpleNamespace(path=path, **defaults)


class TestRunValidateCommand:
    def test_nonexistent_path(self, sample_config):
        args = _make_args("/nonexistent/path.md")
        result = run_validate_command(args, sample_config)
        assert result == 1

    @patch.object(val_module, "_validate_file", return_value=0)
    def test_file_validate(self, mock_val, sample_config, sample_spec_file):
        args = _make_args(str(sample_spec_file))
        result = run_validate_command(args, sample_config)
        assert result == 0
        mock_val.assert_called_once()

    @patch.object(val_module, "_validate_directory", return_value=0)
    def test_directory_validate(self, mock_val, sample_config, temp_dir):
        args = _make_args(str(temp_dir))
        result = run_validate_command(args, sample_config)
        assert result == 0
        mock_val.assert_called_once()

    def test_neither_file_nor_dir(self, sample_config, temp_dir):
        fifo = temp_dir / "test.sock"
        try:
            import os
            os.mkfifo(str(fifo))
        except (OSError, AttributeError):
            pytest.skip("Cannot create fifo")
        args = _make_args(str(fifo))
        result = run_validate_command(args, sample_config)
        assert result == 1

    @patch.object(val_module, "_validate_file", return_value=0)
    def test_check_flags(self, mock_val, sample_config, sample_spec_file):
        args = _make_args(
            str(sample_spec_file),
            check_traceability=True,
            check_security=True,
            check_performance=True,
        )
        result = run_validate_command(args, sample_config)
        assert result == 0
        assert sample_config.validation.check_traceability is True
        assert sample_config.validation.check_security_specs is True

    @patch.object(val_module, "_validate_file", return_value=0)
    def test_no_flags_enables_all(self, mock_val, sample_config, sample_spec_file):
        args = _make_args(str(sample_spec_file))
        result = run_validate_command(args, sample_config)
        assert result == 0
        assert sample_config.validation.check_traceability is True
        assert sample_config.validation.check_security_specs is True
        assert sample_config.validation.check_performance_specs is True


class TestValidateFile:
    @patch("spec_tools.cli.commands.validate.SpecValidator")
    def test_passed(self, mock_validator_cls, temp_dir):
        mock_validator = MagicMock()
        mock_validator.validate_file.return_value = ValidationResult(
            file_path=str(temp_dir / "test.md"), passed=True,
        )
        result = _validate_file(mock_validator, temp_dir / "test.md")
        assert result == 0

    @patch("spec_tools.cli.commands.validate.SpecValidator")
    def test_failed(self, mock_validator_cls, temp_dir):
        mock_validator = MagicMock()
        mock_validator.validate_file.return_value = ValidationResult(
            file_path=str(temp_dir / "test.md"),
            passed=False,
            errors=[LintError("test.md", 1, severity=Severity.ERROR, message="validation error")],
        )
        result = _validate_file(mock_validator, temp_dir / "test.md")
        assert result == 1

    @patch("spec_tools.cli.commands.validate.SpecValidator")
    def test_spec_tools_error(self, mock_validator_cls, temp_dir):
        mock_validator = MagicMock()
        mock_validator.validate_file.side_effect = SpecToolsError("val error")
        result = _validate_file(mock_validator, temp_dir / "test.md")
        assert result == 1

    @patch("spec_tools.cli.commands.validate.SpecValidator")
    def test_unexpected_error(self, mock_validator_cls, temp_dir):
        mock_validator = MagicMock()
        mock_validator.validate_file.side_effect = RuntimeError("unexpected")
        result = _validate_file(mock_validator, temp_dir / "test.md")
        assert result == 1


class TestValidateDirectory:
    @patch("spec_tools.cli.commands.validate.SpecValidator")
    def test_no_md_files(self, mock_validator_cls, temp_dir):
        mock_validator = MagicMock()
        result = _validate_directory(mock_validator, temp_dir)
        assert result == 0

    @patch("spec_tools.cli.commands.validate.SpecValidator")
    def test_all_passed(self, mock_validator_cls, temp_dir):
        (temp_dir / "a.md").write_text("# Test\n")
        mock_validator = MagicMock()
        mock_validator.validate_directory.return_value = [
            ValidationResult(file_path="a.md", passed=True),
        ]
        result = _validate_directory(mock_validator, temp_dir)
        assert result == 0

    @patch("spec_tools.cli.commands.validate.SpecValidator")
    def test_errors_found(self, mock_validator_cls, temp_dir):
        (temp_dir / "a.md").write_text("# Test\n")
        mock_validator = MagicMock()
        mock_validator.validate_directory.return_value = [
            ValidationResult(
                file_path="a.md",
                passed=False,
                errors=[LintError("a.md", 1, severity=Severity.ERROR, message="error")],
            ),
        ]
        result = _validate_directory(mock_validator, temp_dir)
        assert result == 1

    @patch("spec_tools.cli.commands.validate.SpecValidator")
    def test_warnings_only(self, mock_validator_cls, temp_dir):
        (temp_dir / "a.md").write_text("# Test\n")
        mock_validator = MagicMock()
        mock_validator.validate_directory.return_value = [
            ValidationResult(
                file_path="a.md",
                passed=False,
                errors=[LintError("a.md", 1, severity=Severity.WARNING, message="warn")],
            ),
        ]
        result = _validate_directory(mock_validator, temp_dir)
        assert result == 0

    @patch("spec_tools.cli.commands.validate.SpecValidator")
    def test_spec_tools_error_dir(self, mock_validator_cls, temp_dir):
        (temp_dir / "a.md").write_text("# Test\n")
        mock_validator = MagicMock()
        mock_validator.validate_directory.side_effect = SpecToolsError("error")
        result = _validate_directory(mock_validator, temp_dir)
        assert result == 1
