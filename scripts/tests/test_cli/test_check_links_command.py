"""Tests for CLI check-links command."""

import json
from pathlib import Path
from types import SimpleNamespace
from unittest.mock import MagicMock, patch

import pytest

from spec_tools.cli.commands import check_links as cl_module
from spec_tools.cli.commands.check_links import (
    run_check_links_command,
    _display_report,
    _save_report,
    _report_to_dict,
)
from spec_tools.models import Config, LinkReport, LinkInfo, LinkType


def _make_args(path, output=None, format="text"):
    return SimpleNamespace(path=path, output=output, format=format)


def _make_clean_report():
    return LinkReport(
        file_path=Path("test.md"),
        total_links=5,
        valid_links=5,
        broken_links=[],
        orphaned_sections=[],
        duplicate_links=[],
        self_references=[],
    )


def _make_report_with_issues():
    return LinkReport(
        file_path=Path("test.md"),
        total_links=5,
        valid_links=3,
        broken_links=[
            LinkInfo(text="broken", url="http://broken.com", line_number=1, link_type=LinkType.EXTERNAL,
                     error_message="404"),
        ],
        orphaned_sections=[
            LinkInfo(text="orphan", url="#nonexistent", line_number=2, link_type=LinkType.SECTION,
                     error_message="Section not found"),
        ],
        duplicate_links=[("http://dup.com", 2)],
        self_references=[
            LinkInfo(text="self", url="#self", line_number=3, link_type=LinkType.SECTION),
        ],
    )


class TestRunCheckLinksCommand:
    def test_nonexistent_path(self, sample_config):
        args = _make_args("/nonexistent/path.md")
        result = run_check_links_command(args, sample_config)
        assert result == 1

    @patch.object(cl_module, "_display_report", return_value=0)
    @patch("spec_tools.cli.commands.check_links.SpecLinkChecker")
    def test_file_check(self, mock_checker_cls, mock_display, sample_config, sample_spec_file):
        mock_checker = MagicMock()
        mock_checker.check_file.return_value = _make_clean_report()
        mock_checker_cls.return_value = mock_checker

        args = _make_args(str(sample_spec_file))
        result = run_check_links_command(args, sample_config)
        assert result == 0
        mock_display.assert_called_once()

    @patch.object(cl_module, "_save_report", return_value=0)
    @patch("spec_tools.cli.commands.check_links.SpecLinkChecker")
    def test_file_save(self, mock_checker_cls, mock_save, sample_config, sample_spec_file):
        mock_checker = MagicMock()
        mock_checker.check_file.return_value = _make_clean_report()
        mock_checker_cls.return_value = mock_checker

        args = _make_args(str(sample_spec_file), output="report.json", format="json")
        result = run_check_links_command(args, sample_config)
        assert result == 0
        mock_save.assert_called_once()

    @patch.object(cl_module, "_display_report", return_value=0)
    @patch("spec_tools.cli.commands.check_links.SpecLinkChecker")
    def test_directory_check(self, mock_checker_cls, mock_display, sample_config, temp_dir):
        mock_checker = MagicMock()
        mock_checker.check_directory.return_value = _make_clean_report()
        mock_checker_cls.return_value = mock_checker

        args = _make_args(str(temp_dir))
        result = run_check_links_command(args, sample_config)
        assert result == 0

    def test_neither_file_nor_dir(self, sample_config, temp_dir):
        fifo = temp_dir / "test.sock"
        try:
            import os
            os.mkfifo(str(fifo))
        except (OSError, AttributeError):
            pytest.skip("Cannot create fifo")
        args = _make_args(str(fifo))
        result = run_check_links_command(args, sample_config)
        assert result == 1


class TestDisplayReport:
    def test_clean_report_text(self):
        report = _make_clean_report()
        result = _display_report(report, "text")
        assert result == 0

    def test_clean_report_json(self):
        report = _make_clean_report()
        result = _display_report(report, "json")
        assert result == 0

    def test_report_with_issues(self):
        report = _make_report_with_issues()
        result = _display_report(report, "text")
        assert result == 1

    def test_report_json_serializable(self):
        report = _make_report_with_issues()
        result = _display_report(report, "json")
        assert result == 1


class TestSaveReport:
    def test_save_json(self, temp_dir):
        report = _make_clean_report()
        output_path = str(temp_dir / "report.json")
        result = _save_report(report, output_path, "json")
        assert result == 0
        assert (temp_dir / "report.json").exists()
        data = json.loads((temp_dir / "report.json").read_text())
        assert data["total_links"] == 5

    def test_save_text(self, temp_dir):
        report = _make_clean_report()
        output_path = str(temp_dir / "report.txt")
        result = _save_report(report, output_path, "text")
        assert result == 0
        assert (temp_dir / "report.txt").exists()

    def test_save_with_issues(self, temp_dir):
        report = _make_report_with_issues()
        output_path = str(temp_dir / "report.json")
        result = _save_report(report, output_path, "json")
        assert result == 1

    def test_save_error(self, temp_dir):
        report = _make_clean_report()
        result = _save_report(report, "/nonexistent/dir/report.json", "json")
        assert result == 1


class TestReportToDict:
    def test_clean_report(self):
        report = _make_clean_report()
        d = _report_to_dict(report)
        assert d["total_links"] == 5
        assert d["valid_links"] == 5
        assert d["broken_links"] == []
        assert d["orphaned_sections"] == []

    def test_report_with_issues(self):
        report = _make_report_with_issues()
        d = _report_to_dict(report)
        assert len(d["broken_links"]) == 1
        assert d["broken_links"][0]["url"] == "http://broken.com"
        assert len(d["orphaned_sections"]) == 1
        assert len(d["self_references"]) == 1
        assert len(d["duplicate_links"]) == 1
