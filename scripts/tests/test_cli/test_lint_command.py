"""Tests for CLI lint command."""

from pathlib import Path
from types import SimpleNamespace
from unittest.mock import MagicMock, patch

import pytest

from spec_tools.cli.commands import lint as lint_module
from spec_tools.cli.commands.lint import run_lint_command, _lint_file, _lint_directory
from spec_tools.exceptions import SpecToolsError
from spec_tools.models import Config, ValidationResult, Severity, LintError


def _make_args(path, strict=False, fix=False, rules=None):
    return SimpleNamespace(path=path, strict=strict, fix=fix, rules=rules)


class TestRunLintCommand:
    def test_nonexistent_path(self, sample_config):
        args = _make_args("/nonexistent/path.md")
        result = run_lint_command(args, sample_config)
        assert result == 1

    @patch.object(lint_module, "_lint_file", return_value=0)
    def test_file_lint(self, mock_lint, sample_config, sample_spec_file):
        args = _make_args(str(sample_spec_file))
        result = run_lint_command(args, sample_config)
        assert result == 0
        mock_lint.assert_called_once()

    @patch.object(lint_module, "_lint_directory", return_value=0)
    def test_directory_lint(self, mock_lint, sample_config, temp_dir):
        args = _make_args(str(temp_dir))
        result = run_lint_command(args, sample_config)
        assert result == 0
        mock_lint.assert_called_once()

    def test_neither_file_nor_dir(self, sample_config, temp_dir):
        fifo = temp_dir / "test.sock"
        try:
            import os
            os.mkfifo(str(fifo))
        except (OSError, AttributeError):
            pytest.skip("Cannot create fifo")
        args = _make_args(str(fifo))
        result = run_lint_command(args, sample_config)
        assert result == 1

    @patch.object(lint_module, "_lint_file", return_value=0)
    def test_with_rules(self, mock_lint, sample_config, sample_spec_file):
        args = _make_args(str(sample_spec_file), rules="rule1,rule2")
        result = run_lint_command(args, sample_config)
        assert result == 0


class TestLintFile:
    @patch("spec_tools.cli.commands.lint.SpecLinter")
    def test_passed(self, mock_linter_cls, temp_dir):
        mock_linter = MagicMock()
        mock_linter.lint_file.return_value = ValidationResult(
            file_path=str(temp_dir / "test.md"), passed=True,
        )
        result = _lint_file(mock_linter, temp_dir / "test.md", strict=False, fix=False)
        assert result == 0

    @patch("spec_tools.cli.commands.lint.SpecLinter")
    def test_failed(self, mock_linter_cls, temp_dir):
        mock_linter = MagicMock()
        mock_linter.lint_file.return_value = ValidationResult(
            file_path=str(temp_dir / "test.md"),
            passed=False,
            errors=[LintError("test.md", 1, severity=Severity.ERROR, message="lint error")],
        )
        result = _lint_file(mock_linter, temp_dir / "test.md", strict=False, fix=False)
        assert result == 1

    @patch("spec_tools.cli.commands.lint.SpecLinter")
    def test_strict_mode_warnings(self, mock_linter_cls, temp_dir):
        mock_linter = MagicMock()
        mock_linter.lint_file.return_value = ValidationResult(
            file_path=str(temp_dir / "test.md"),
            passed=False,
            errors=[LintError("test.md", 1, severity=Severity.WARNING, message="warning")],
        )
        result = _lint_file(mock_linter, temp_dir / "test.md", strict=True, fix=False)
        assert result == 1

    @patch("spec_tools.cli.commands.lint.SpecLinter")
    def test_fix_flag(self, mock_linter_cls, temp_dir):
        mock_linter = MagicMock()
        mock_linter.lint_file.return_value = ValidationResult(
            file_path=str(temp_dir / "test.md"), passed=True,
        )
        result = _lint_file(mock_linter, temp_dir / "test.md", strict=False, fix=True)
        assert result == 0

    @patch("spec_tools.cli.commands.lint.SpecLinter")
    def test_spec_tools_error(self, mock_linter_cls, temp_dir):
        mock_linter = MagicMock()
        mock_linter.lint_file.side_effect = SpecToolsError("lint error")
        result = _lint_file(mock_linter, temp_dir / "test.md", strict=False, fix=False)
        assert result == 1

    @patch("spec_tools.cli.commands.lint.SpecLinter")
    def test_unexpected_error(self, mock_linter_cls, temp_dir):
        mock_linter = MagicMock()
        mock_linter.lint_file.side_effect = RuntimeError("unexpected")
        result = _lint_file(mock_linter, temp_dir / "test.md", strict=False, fix=False)
        assert result == 1


class TestLintDirectory:
    @patch("spec_tools.cli.commands.lint.SpecLinter")
    def test_no_md_files(self, mock_linter_cls, temp_dir):
        mock_linter = MagicMock()
        result = _lint_directory(mock_linter, temp_dir, strict=False, fix=False)
        assert result == 0

    @patch("spec_tools.cli.commands.lint.SpecLinter")
    def test_all_passed(self, mock_linter_cls, temp_dir):
        (temp_dir / "a.md").write_text("# Test\n")
        (temp_dir / "b.md").write_text("# Test\n")

        mock_linter = MagicMock()
        mock_linter.lint_directory.return_value = [
            ValidationResult(file_path="a.md", passed=True),
            ValidationResult(file_path="b.md", passed=True),
        ]
        result = _lint_directory(mock_linter, temp_dir, strict=False, fix=False)
        assert result == 0

    @patch("spec_tools.cli.commands.lint.SpecLinter")
    def test_errors_found(self, mock_linter_cls, temp_dir):
        (temp_dir / "a.md").write_text("# Test\n")

        mock_linter = MagicMock()
        mock_linter.lint_directory.return_value = [
            ValidationResult(
                file_path="a.md",
                passed=False,
                errors=[LintError("a.md", 1, severity=Severity.ERROR, message="error")],
            ),
        ]
        result = _lint_directory(mock_linter, temp_dir, strict=False, fix=False)
        assert result == 1

    @patch("spec_tools.cli.commands.lint.SpecLinter")
    def test_warnings_only(self, mock_linter_cls, temp_dir):
        (temp_dir / "a.md").write_text("# Test\n")

        mock_linter = MagicMock()
        mock_linter.lint_directory.return_value = [
            ValidationResult(
                file_path="a.md",
                passed=False,
                errors=[LintError("a.md", 1, severity=Severity.WARNING, message="warn")],
            ),
        ]
        result = _lint_directory(mock_linter, temp_dir, strict=False, fix=False)
        assert result == 0

    @patch("spec_tools.cli.commands.lint.SpecLinter")
    def test_strict_warnings_fail(self, mock_linter_cls, temp_dir):
        (temp_dir / "a.md").write_text("# Test\n")

        mock_linter = MagicMock()
        mock_linter.lint_directory.return_value = [
            ValidationResult(
                file_path="a.md",
                passed=False,
                errors=[LintError("a.md", 1, severity=Severity.WARNING, message="warn")],
            ),
        ]
        result = _lint_directory(mock_linter, temp_dir, strict=True, fix=False)
        assert result == 1

    @patch("spec_tools.cli.commands.lint.SpecLinter")
    def test_spec_tools_error_dir(self, mock_linter_cls, temp_dir):
        (temp_dir / "a.md").write_text("# Test\n")
        mock_linter = MagicMock()
        mock_linter.lint_directory.side_effect = SpecToolsError("error")
        result = _lint_directory(mock_linter, temp_dir, strict=False, fix=False)
        assert result == 1
