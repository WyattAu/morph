"""Tests for CLI format command."""

from pathlib import Path
from types import SimpleNamespace
from unittest.mock import MagicMock, patch

import pytest

from spec_tools.cli.commands import format as fmt_module
from spec_tools.cli.commands.format import run_format_command, _format_file, _format_directory
from spec_tools.exceptions import SpecToolsError
from spec_tools.models import Config, ValidationResult, Severity, LintError


def _make_args(path, check=True):
    return SimpleNamespace(path=path, check=check)


class TestRunFormatCommand:
    def test_nonexistent_path(self, sample_config):
        args = _make_args("/nonexistent/path.md")
        result = run_format_command(args, sample_config)
        assert result == 1

    @patch.object(fmt_module, "_format_file", return_value=0)
    def test_file_check(self, mock_format, sample_config, sample_spec_file):
        args = _make_args(str(sample_spec_file), check=True)
        result = run_format_command(args, sample_config)
        assert result == 0
        mock_format.assert_called_once()

    @patch.object(fmt_module, "_format_directory", return_value=0)
    def test_directory_check(self, mock_format, sample_config, temp_dir):
        args = _make_args(str(temp_dir), check=True)
        result = run_format_command(args, sample_config)
        assert result == 0
        mock_format.assert_called_once()

    def test_neither_file_nor_dir(self, sample_config, temp_dir):
        fifo = temp_dir / "test.sock"
        try:
            import os
            os.mkfifo(str(fifo))
        except (OSError, AttributeError):
            pytest.skip("Cannot create fifo")
        args = _make_args(str(fifo))
        result = run_format_command(args, sample_config)
        assert result == 1


class TestFormatFile:
    @patch("spec_tools.cli.commands.format.MarkdownFormatter")
    def test_check_passed(self, mock_formatter_cls, temp_dir):
        mock_formatter = MagicMock()
        mock_formatter.check_format.return_value = ValidationResult(
            file_path=str(temp_dir / "test.md"), passed=True,
        )
        mock_formatter_cls.return_value = mock_formatter

        config = Config()
        result = _format_file(mock_formatter, temp_dir / "test.md", check_only=True)
        assert result == 0

    @patch("spec_tools.cli.commands.format.MarkdownFormatter")
    def test_check_failed(self, mock_formatter_cls, temp_dir):
        mock_formatter = MagicMock()
        mock_formatter.check_format.return_value = ValidationResult(
            file_path=str(temp_dir / "test.md"),
            passed=False,
            errors=[LintError("test.md", 1, severity=Severity.ERROR, message="bad format")],
        )
        mock_formatter_cls.return_value = mock_formatter

        result = _format_file(mock_formatter, temp_dir / "test.md", check_only=True)
        assert result == 1

    @patch("spec_tools.cli.commands.format.MarkdownFormatter")
    def test_format_modified(self, mock_formatter_cls, temp_dir):
        mock_formatter = MagicMock()
        mock_formatter.format_file.return_value = True
        result = _format_file(mock_formatter, temp_dir / "test.md", check_only=False)
        assert result == 0

    @patch("spec_tools.cli.commands.format.MarkdownFormatter")
    def test_format_already_formatted(self, mock_formatter_cls, temp_dir):
        mock_formatter = MagicMock()
        mock_formatter.format_file.return_value = False
        result = _format_file(mock_formatter, temp_dir / "test.md", check_only=False)
        assert result == 0

    @patch("spec_tools.cli.commands.format.MarkdownFormatter")
    def test_spec_tools_error(self, mock_formatter_cls, temp_dir):
        mock_formatter = MagicMock()
        mock_formatter.check_format.side_effect = SpecToolsError("format error")
        result = _format_file(mock_formatter, temp_dir / "test.md", check_only=True)
        assert result == 1

    @patch("spec_tools.cli.commands.format.MarkdownFormatter")
    def test_unexpected_error(self, mock_formatter_cls, temp_dir):
        mock_formatter = MagicMock()
        mock_formatter.check_format.side_effect = RuntimeError("unexpected")
        result = _format_file(mock_formatter, temp_dir / "test.md", check_only=True)
        assert result == 1


class TestFormatDirectory:
    @patch("spec_tools.cli.commands.format.MarkdownFormatter")
    def test_no_md_files(self, mock_formatter_cls, temp_dir):
        mock_formatter = MagicMock()
        result = _format_directory(mock_formatter, temp_dir, check_only=True)
        assert result == 0

    @patch("spec_tools.cli.commands.format.MarkdownFormatter")
    def test_all_files_passed(self, mock_formatter_cls, temp_dir):
        (temp_dir / "a.md").write_text("# Test\n")
        (temp_dir / "b.md").write_text("# Test\n")

        mock_formatter = MagicMock()
        mock_formatter.check_format.return_value = ValidationResult(
            file_path="test.md", passed=True,
        )
        result = _format_directory(mock_formatter, temp_dir, check_only=True)
        assert result == 0

    @patch("spec_tools.cli.commands.format.MarkdownFormatter")
    def test_some_files_failed(self, mock_formatter_cls, temp_dir):
        (temp_dir / "a.md").write_text("# Test\n")

        mock_formatter = MagicMock()
        mock_formatter.check_format.return_value = ValidationResult(
            file_path="a.md",
            passed=False,
            errors=[LintError("a.md", 1, severity=Severity.ERROR, message="bad")],
        )
        result = _format_directory(mock_formatter, temp_dir, check_only=True)
        assert result == 1

    @patch("spec_tools.cli.commands.format.MarkdownFormatter")
    def test_format_directory_write(self, mock_formatter_cls, temp_dir):
        (temp_dir / "a.md").write_text("# Test\n")

        mock_formatter = MagicMock()
        mock_formatter.format_directory.return_value = 1
        result = _format_directory(mock_formatter, temp_dir, check_only=False)
        assert result == 0

    @patch("spec_tools.cli.commands.format.MarkdownFormatter")
    def test_spec_tools_error_dir(self, mock_formatter_cls, temp_dir):
        (temp_dir / "a.md").write_text("# Test\n")
        mock_formatter = MagicMock()
        mock_formatter.check_format.side_effect = SpecToolsError("error")
        result = _format_directory(mock_formatter, temp_dir, check_only=True)
        assert result == 1
