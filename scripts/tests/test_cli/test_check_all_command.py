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
