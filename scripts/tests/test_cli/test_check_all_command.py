"""Tests for CLI check-all command."""

from pathlib import Path
from types import SimpleNamespace
from unittest.mock import MagicMock, patch

import pytest

from spec_tools.cli.commands import check_all as ca_module
from spec_tools.cli.commands.check_all import (
    run_check_all_command,
    _display_summary,
    _link_report_passed,
)
from spec_tools.models import Config, LinkReport


def _make_args(path, strict=False, verbose=False):
    return SimpleNamespace(path=path, strict=strict, verbose=verbose)


def _make_all_passed_results():
    return {
        "format": {"passed": True, "errors": 0, "warnings": 0},
        "lint": {"passed": True, "errors": 0, "warnings": 0},
        "validate": {"passed": True, "errors": 0, "warnings": 0},
        "links": {"passed": True, "broken_links": 0, "orphaned_sections": 0, "self_references": 0},
    }


def _make_all_failed_results():
    return {
        "format": {"passed": False, "errors": 2, "warnings": 1},
        "lint": {"passed": False, "errors": 1, "warnings": 3},
        "validate": {"passed": False, "errors": 1, "warnings": 0},
        "links": {"passed": False, "broken_links": 1, "orphaned_sections": 1, "self_references": 0},
    }


class TestRunCheckAllCommand:
    def test_nonexistent_path(self, sample_config):
        args = _make_args("/nonexistent/path.md")
        result = run_check_all_command(args, sample_config)
        assert result == 1

    @patch.object(ca_module, "_display_summary", return_value=0)
    @patch.object(ca_module, "_run_link_check", return_value={"passed": True, "broken_links": 0, "orphaned_sections": 0, "self_references": 0})
    @patch.object(ca_module, "_run_validate_check", return_value={"passed": True, "errors": 0, "warnings": 0})
    @patch.object(ca_module, "_run_lint_check", return_value={"passed": True, "errors": 0, "warnings": 0})
    @patch.object(ca_module, "_run_format_check", return_value={"passed": True, "errors": 0, "warnings": 0})
    def test_all_passed(self, mock_fmt, mock_lint, mock_val, mock_link, mock_summary, sample_config, sample_spec_file):
        args = _make_args(str(sample_spec_file))
        result = run_check_all_command(args, sample_config)
        assert result == 0

    @patch.object(ca_module, "_display_summary", return_value=1)
    @patch.object(ca_module, "_run_link_check", return_value={"passed": False, "broken_links": 1, "orphaned_sections": 0, "self_references": 0})
    @patch.object(ca_module, "_run_validate_check", return_value={"passed": True, "errors": 0, "warnings": 0})
    @patch.object(ca_module, "_run_lint_check", return_value={"passed": True, "errors": 0, "warnings": 0})
    @patch.object(ca_module, "_run_format_check", return_value={"passed": True, "errors": 0, "warnings": 0})
    def test_some_failed(self, mock_fmt, mock_lint, mock_val, mock_link, mock_summary, sample_config, sample_spec_file):
        args = _make_args(str(sample_spec_file))
        result = run_check_all_command(args, sample_config)
        assert result == 1

    @patch.object(ca_module, "_display_summary", return_value=1)
    @patch.object(ca_module, "_run_link_check", return_value={"passed": True, "broken_links": 0, "orphaned_sections": 0, "self_references": 0})
    @patch.object(ca_module, "_run_validate_check", return_value={"passed": True, "errors": 0, "warnings": 0})
    @patch.object(ca_module, "_run_lint_check", return_value={"passed": True, "errors": 0, "warnings": 0})
    @patch.object(ca_module, "_run_format_check", return_value={"passed": True, "errors": 0, "warnings": 0})
    def test_strict_mode(self, mock_fmt, mock_lint, mock_val, mock_link, mock_summary, sample_config, sample_spec_file):
        args = _make_args(str(sample_spec_file), strict=True)
        result = run_check_all_command(args, sample_config)
        assert sample_config.linting.strict is True


class TestDisplaySummary:
    def test_all_passed(self, capsys):
        results = _make_all_passed_results()
        result = _display_summary(results, strict=False)
        assert result == 0

    def test_all_failed(self, capsys):
        results = _make_all_failed_results()
        result = _display_summary(results, strict=False)
        assert result == 1

    def test_strict_mode_with_issues(self, capsys):
        results = _make_all_failed_results()
        result = _display_summary(results, strict=True)
        assert result == 1


class TestLinkReportPassed:
    def test_passed(self):
        report = LinkReport(
            file_path=Path("test.md"),
            total_links=5,
            valid_links=5,
        )
        assert _link_report_passed(report) is True

    def test_broken_links(self):
        from spec_tools.models import LinkInfo, LinkType
        report = LinkReport(
            file_path=Path("test.md"),
            total_links=5,
            valid_links=4,
            broken_links=[LinkInfo(text="b", url="http://b.com", line_number=1, link_type=LinkType.EXTERNAL)],
        )
        assert _link_report_passed(report) is False

    def test_orphaned_sections(self):
        from spec_tools.models import LinkInfo, LinkType
        report = LinkReport(
            file_path=Path("test.md"),
            total_links=5,
            valid_links=4,
            orphaned_sections=[LinkInfo(text="o", url="#o", line_number=1, link_type=LinkType.SECTION)],
        )
        assert _link_report_passed(report) is False

    def test_self_references(self):
        from spec_tools.models import LinkInfo, LinkType
        report = LinkReport(
            file_path=Path("test.md"),
            total_links=5,
            valid_links=4,
            self_references=[LinkInfo(text="s", url="#s", line_number=1, link_type=LinkType.SECTION)],
        )
        assert _link_report_passed(report) is False


class TestRunFormatCheck:
    def test_single_file_passed_verbose(self, temp_dir):
        from spec_tools.cli.commands.check_all import _run_format_check
        formatter = MagicMock()
        result = MagicMock(passed=True, error_count=0, warning_count=0)
        formatter.check_format.return_value = result
        path = temp_dir / "test.md"
        path.write_text("hello")
        out = _run_format_check(formatter, path, verbose=True)
        assert out["passed"] is True
        assert out["errors"] == 0

    def test_single_file_failed_not_verbose(self, temp_dir):
        from spec_tools.cli.commands.check_all import _run_format_check
        formatter = MagicMock()
        result = MagicMock(passed=False, error_count=2, warning_count=1)
        formatter.check_format.return_value = result
        path = temp_dir / "test.md"
        path.write_text("hello")
        out = _run_format_check(formatter, path, verbose=False)
        assert out["passed"] is False
        assert out["errors"] == 2

    def test_directory_no_md_files(self, temp_dir):
        from spec_tools.cli.commands.check_all import _run_format_check
        formatter = MagicMock()
        out = _run_format_check(formatter, temp_dir, verbose=False)
        assert out["passed"] is True

    def test_directory_all_passed(self, temp_dir):
        from spec_tools.cli.commands.check_all import _run_format_check
        (temp_dir / "a.md").write_text("hello")
        formatter = MagicMock()
        result = MagicMock(passed=True, error_count=0, warning_count=0)
        formatter.check_format.return_value = result
        out = _run_format_check(formatter, temp_dir, verbose=False)
        assert out["passed"] is True

    def test_directory_some_failed_verbose(self, temp_dir):
        from spec_tools.cli.commands.check_all import _run_format_check
        (temp_dir / "a.md").write_text("hello")
        formatter = MagicMock()
        result = MagicMock(passed=False, error_count=1, warning_count=0)
        formatter.check_format.return_value = result
        out = _run_format_check(formatter, temp_dir, verbose=True)
        assert out["passed"] is False
        assert out["errors"] == 1

    def test_format_check_exception(self, temp_dir):
        from spec_tools.cli.commands.check_all import _run_format_check
        formatter = MagicMock()
        formatter.check_format.side_effect = RuntimeError("boom")
        path = temp_dir / "a.md"
        path.write_text("hello")
        out = _run_format_check(formatter, path, verbose=False)
        assert out["passed"] is False
        assert out["errors"] == 1


class TestRunLintCheck:
    def test_single_file_passed(self, temp_dir):
        from spec_tools.cli.commands.check_all import _run_lint_check
        linter = MagicMock()
        result = MagicMock(passed=True, error_count=0, warning_count=0)
        linter.lint_file.return_value = result
        path = temp_dir / "test.md"
        path.write_text("hello")
        out = _run_lint_check(linter, path, verbose=False)
        assert out["passed"] is True

    def test_single_file_failed_verbose(self, temp_dir):
        from spec_tools.cli.commands.check_all import _run_lint_check
        linter = MagicMock()
        result = MagicMock(passed=False, error_count=3, warning_count=2)
        linter.lint_file.return_value = result
        path = temp_dir / "test.md"
        path.write_text("hello")
        out = _run_lint_check(linter, path, verbose=True)
        assert out["passed"] is False
        assert out["errors"] == 3

    def test_directory_lint_all_passed(self, temp_dir):
        from spec_tools.cli.commands.check_all import _run_lint_check
        (temp_dir / "a.md").write_text("hello")
        linter = MagicMock()
        r1 = MagicMock(passed=True, error_count=0, warning_count=0)
        linter.lint_directory.return_value = [r1]
        out = _run_lint_check(linter, temp_dir, verbose=False)
        assert out["passed"] is True

    def test_directory_lint_some_failed_verbose(self, temp_dir):
        from spec_tools.cli.commands.check_all import _run_lint_check
        (temp_dir / "a.md").write_text("hello")
        linter = MagicMock()
        r1 = MagicMock(passed=False, error_count=1, warning_count=0)
        linter.lint_directory.return_value = [r1]
        out = _run_lint_check(linter, temp_dir, verbose=True)
        assert out["passed"] is False
        assert out["errors"] == 1

    def test_lint_check_exception(self, temp_dir):
        from spec_tools.cli.commands.check_all import _run_lint_check
        linter = MagicMock()
        linter.lint_file.side_effect = RuntimeError("boom")
        path = temp_dir / "a.md"
        path.write_text("hello")
        out = _run_lint_check(linter, path, verbose=False)
        assert out["passed"] is False
        assert out["errors"] == 1


class TestRunValidateCheck:
    def test_single_file_passed(self, temp_dir):
        from spec_tools.cli.commands.check_all import _run_validate_check
        validator = MagicMock()
        result = MagicMock(passed=True, error_count=0, warning_count=0)
        validator.validate_file.return_value = result
        path = temp_dir / "test.md"
        path.write_text("hello")
        out = _run_validate_check(validator, path, verbose=False)
        assert out["passed"] is True

    def test_single_file_failed_verbose(self, temp_dir):
        from spec_tools.cli.commands.check_all import _run_validate_check
        validator = MagicMock()
        result = MagicMock(passed=False, error_count=1, warning_count=1)
        validator.validate_file.return_value = result
        path = temp_dir / "test.md"
        path.write_text("hello")
        out = _run_validate_check(validator, path, verbose=True)
        assert out["passed"] is False
        assert out["errors"] == 1

    def test_directory_validate_all_passed(self, temp_dir):
        from spec_tools.cli.commands.check_all import _run_validate_check
        (temp_dir / "a.md").write_text("hello")
        validator = MagicMock()
        r1 = MagicMock(passed=True, error_count=0, warning_count=0)
        validator.validate_directory.return_value = [r1]
        out = _run_validate_check(validator, temp_dir, verbose=False)
        assert out["passed"] is True

    def test_directory_validate_some_failed_verbose(self, temp_dir):
        from spec_tools.cli.commands.check_all import _run_validate_check
        (temp_dir / "a.md").write_text("hello")
        validator = MagicMock()
        r1 = MagicMock(passed=False, error_count=2, warning_count=0)
        validator.validate_directory.return_value = [r1]
        out = _run_validate_check(validator, temp_dir, verbose=True)
        assert out["passed"] is False
        assert out["errors"] == 2

    def test_validate_check_exception(self, temp_dir):
        from spec_tools.cli.commands.check_all import _run_validate_check
        validator = MagicMock()
        validator.validate_file.side_effect = RuntimeError("boom")
        path = temp_dir / "a.md"
        path.write_text("hello")
        out = _run_validate_check(validator, path, verbose=False)
        assert out["passed"] is False
        assert out["errors"] == 1


class TestRunLinkCheck:
    def test_single_file_passed_verbose(self, temp_dir):
        from spec_tools.cli.commands.check_all import _run_link_check
        from spec_tools.models import LinkReport
        link_checker = MagicMock()
        report = LinkReport(file_path=Path("test.md"), total_links=3, valid_links=3)
        link_checker.check_file.return_value = report
        path = temp_dir / "test.md"
        path.write_text("hello")
        out = _run_link_check(link_checker, path, verbose=True)
        assert out["passed"] is True

    def test_single_file_broken_not_verbose(self, temp_dir):
        from spec_tools.cli.commands.check_all import _run_link_check
        from spec_tools.models import LinkInfo, LinkReport, LinkType
        link_checker = MagicMock()
        broken = LinkInfo(text="b", url="http://b.com", line_number=1, link_type=LinkType.EXTERNAL)
        report = LinkReport(file_path=Path("test.md"), total_links=3, valid_links=2, broken_links=[broken])
        link_checker.check_file.return_value = report
        path = temp_dir / "test.md"
        path.write_text("hello")
        out = _run_link_check(link_checker, path, verbose=False)
        assert out["passed"] is False
        assert out["broken_links"] == 1

    def test_directory_link_check(self, temp_dir):
        from spec_tools.cli.commands.check_all import _run_link_check
        from spec_tools.models import LinkReport
        (temp_dir / "a.md").write_text("hello")
        link_checker = MagicMock()
        report = LinkReport(file_path=Path("test.md"), total_links=0, valid_links=0)
        link_checker.check_directory.return_value = report
        out = _run_link_check(link_checker, temp_dir, verbose=False)
        assert out["passed"] is True

    def test_link_check_exception(self, temp_dir):
        from spec_tools.cli.commands.check_all import _run_link_check
        link_checker = MagicMock()
        link_checker.check_file.side_effect = RuntimeError("boom")
        path = temp_dir / "a.md"
        path.write_text("hello")
        out = _run_link_check(link_checker, path, verbose=False)
        assert out["passed"] is False
        assert out["broken_links"] == 1


class TestDisplayFormatResult:
    def test_passed(self, capsys):
        from spec_tools.cli.commands.check_all import _display_format_result
        result = MagicMock(passed=True, file_path="test.md", errors=[])
        _display_format_result(result)
        assert "Properly formatted" in capsys.readouterr().out

    def test_failed_with_errors(self, capsys):
        from spec_tools.cli.commands.check_all import _display_format_result
        err = MagicMock(line_number=5, message="bad format")
        result = MagicMock(passed=False, file_path="test.md", errors=[err])
        _display_format_result(result)
        out = capsys.readouterr().out
        assert "Formatting issues" in out
        assert "Line 5" in out


class TestDisplayLintResult:
    def test_passed(self, capsys):
        from spec_tools.cli.commands.check_all import _display_lint_result
        result = MagicMock(passed=True, file_path="test.md", errors=[])
        _display_lint_result(result)
        assert "No linting issues" in capsys.readouterr().out

    def test_failed_with_errors(self, capsys):
        from spec_tools.cli.commands.check_all import _display_lint_result
        from spec_tools.models import Severity
        err = MagicMock(
            line_number=10, message="bad lint", severity=Severity.ERROR, rule_id="LINT-001"
        )
        result = MagicMock(passed=False, file_path="test.md", errors=[err])
        _display_lint_result(result)
        out = capsys.readouterr().out
        assert "Linting issues" in out
        assert "LINT-001" in out


class TestDisplayValidationResult:
    def test_passed(self, capsys):
        from spec_tools.cli.commands.check_all import _display_validation_result
        result = MagicMock(passed=True, file_path="test.md", errors=[])
        _display_validation_result(result)
        assert "Validation passed" in capsys.readouterr().out

    def test_failed_with_errors(self, capsys):
        from spec_tools.cli.commands.check_all import _display_validation_result
        from spec_tools.models import Severity
        err = MagicMock(
            line_number=3, message="validation fail", severity=Severity.WARNING, rule_id="VAL-001"
        )
        result = MagicMock(passed=False, file_path="test.md", errors=[err])
        _display_validation_result(result)
        out = capsys.readouterr().out
        assert "Validation issues" in out
        assert "VAL-001" in out


class TestDisplayLinkReport:
    def test_display(self, capsys):
        from spec_tools.cli.commands.check_all import _display_link_report
        from spec_tools.models import LinkInfo, LinkReport, LinkType
        broken = LinkInfo(text="b", url="http://b.com", line_number=1, link_type=LinkType.EXTERNAL)
        orphaned = LinkInfo(text="o", url="#o", line_number=2, link_type=LinkType.SECTION)
        self_ref = LinkInfo(text="s", url="#s", line_number=3, link_type=LinkType.SECTION)
        report = LinkReport(
            file_path=Path("test.md"),
            total_links=10,
            valid_links=7,
            broken_links=[broken],
            orphaned_sections=[orphaned],
            self_references=[self_ref],
        )
        _display_link_report(report)
        out = capsys.readouterr().out
        assert "Total links: 10" in out
        assert "Broken links: 1" in out
        assert "Orphaned sections: 1" in out
        assert "Self references: 1" in out


class TestDisplaySummaryStrictMode:
    def test_strict_mode_all_passed(self, capsys):
        results = _make_all_passed_results()
        result = _display_summary(results, strict=True)
        assert result == 0

    def test_strict_mode_warnings_only(self, capsys):
        results = {
            "format": {"passed": True, "errors": 0, "warnings": 1},
            "lint": {"passed": True, "errors": 0, "warnings": 0},
            "validate": {"passed": True, "errors": 0, "warnings": 0},
            "links": {"passed": True, "broken_links": 0, "orphaned_sections": 0, "self_references": 0},
        }
        result = _display_summary(results, strict=True)
        assert result == 1
