"""Tests for coverage tracking."""

from pathlib import Path

import pytest

from spec_tools.verification.coverage import CoverageConfig, CoverageTracker
from spec_tools.verification.models import (
    CompilationResult,
    CompilationStatus,
    CoverageMetrics,
    Issue,
    IssueCategory,
    IssueId,
    IssueSeverity,
)


class TestCoverageConfig:
    def test_defaults(self):
        config = CoverageConfig()
        assert config.spec_point_threshold == 1
        assert "Spec.lean" in config.required_files
        assert config.success_criteria["file_coverage"] == 95.0


class TestCoverageTracker:
    def _make_issue(self, category, severity, description="test"):
        return Issue(
            issue_id=IssueId(category, 1),
            category=category,
            severity=severity,
            spec_name="S",
            file_path=Path("f.lean"),
            description=description,
        )

    def test_init(self):
        tracker = CoverageTracker()
        assert len(tracker._verified_files) == 0
        assert len(tracker._verified_specs) == 0

    def test_track_compilation_result_success(self):
        tracker = CoverageTracker()
        result = CompilationResult(
            file_path=Path("TestSpec/Spec.lean"),
            status=CompilationStatus.SUCCESS,
        )
        tracker.track_compilation_result(result)
        assert Path("TestSpec/Spec.lean") in tracker._verified_files
        assert "TestSpec" in tracker._verified_specs

    def test_track_compilation_result_non_spec_file(self):
        tracker = CoverageTracker()
        result = CompilationResult(
            file_path=Path("TestSpec/Other.lean"),
            status=CompilationStatus.SUCCESS,
        )
        tracker.track_compilation_result(result)
        assert Path("TestSpec/Other.lean") in tracker._verified_files
        assert "TestSpec" not in tracker._verified_specs

    def test_track_compilation_result_failure(self):
        tracker = CoverageTracker()
        result = CompilationResult(
            file_path=Path("TestSpec/Spec.lean"),
            status=CompilationStatus.FAILED,
        )
        tracker.track_compilation_result(result)
        assert Path("TestSpec/Spec.lean") not in tracker._verified_files

    def test_track_issue(self):
        tracker = CoverageTracker()
        issue = self._make_issue(IssueCategory.USP, IssueSeverity.MEDIUM)
        tracker.track_issue(issue)
        assert len(tracker._issues_by_category[IssueCategory.USP]) == 1
        assert len(tracker._issues_by_severity[IssueSeverity.MEDIUM]) == 1

    def test_track_issue_multiple(self):
        tracker = CoverageTracker()
        tracker.track_issue(self._make_issue(IssueCategory.USP, IssueSeverity.MEDIUM))
        tracker.track_issue(self._make_issue(IssueCategory.LCF, IssueSeverity.CRITICAL))
        tracker.track_issue(self._make_issue(IssueCategory.USP, IssueSeverity.HIGH))
        assert len(tracker._issues_by_category[IssueCategory.USP]) == 2
        assert len(tracker._issues_by_category[IssueCategory.LCF]) == 1

    def test_track_directory(self, temp_dir):
        (temp_dir / "a.lean").write_text("content")
        (temp_dir / "b.lean").write_text("content")
        tracker = CoverageTracker()
        tracker.track_directory(temp_dir)
        assert len(tracker._verified_files) == 0

    def test_get_coverage_metrics(self, temp_dir):
        spec_dir = temp_dir / "TestSpec"
        spec_dir.mkdir()
        (spec_dir / "Spec.lean").write_text("content")
        (spec_dir / "Examples.lean").write_text("content")

        config = CoverageConfig(specs_root=temp_dir)
        tracker = CoverageTracker(config)
        tracker.track_compilation_result(CompilationResult(
            file_path=spec_dir / "Spec.lean",
            status=CompilationStatus.SUCCESS,
        ))
        metrics = tracker.get_coverage_metrics()
        assert metrics.total_specs == 1
        assert metrics.verified_specs == 1
        assert metrics.total_files == 2
        assert metrics.verified_files == 1

    def test_generate_coverage_report(self, temp_dir):
        spec_dir = temp_dir / "TestSpec"
        spec_dir.mkdir()
        (spec_dir / "Spec.lean").write_text("content")
        (spec_dir / "Examples.lean").write_text("content")

        config = CoverageConfig(specs_root=temp_dir)
        tracker = CoverageTracker(config)
        tracker.track_compilation_result(CompilationResult(
            file_path=spec_dir / "Spec.lean",
            status=CompilationStatus.SUCCESS,
        ))
        report = tracker.generate_coverage_report()
        assert report.total_issues == 0
        assert len(report.uncovered_files) == 1

    def test_validate_success_criteria_pass(self, temp_dir):
        spec_dir = temp_dir / "TestSpec"
        spec_dir.mkdir()
        (spec_dir / "Spec.lean").write_text("content")

        config = CoverageConfig(specs_root=temp_dir)
        tracker = CoverageTracker(config)
        tracker.track_compilation_result(CompilationResult(
            file_path=spec_dir / "Spec.lean",
            status=CompilationStatus.SUCCESS,
        ))
        all_passed, criteria = tracker.validate_success_criteria()
        assert "file_coverage" in criteria
        assert "spec_coverage" in criteria
        assert "overall_success" in criteria

    def test_validate_success_criteria_fail(self, temp_dir):
        spec_dir = temp_dir / "TestSpec"
        spec_dir.mkdir()
        (spec_dir / "Spec.lean").write_text("content")

        config = CoverageConfig(specs_root=temp_dir)
        tracker = CoverageTracker(config)
        all_passed, criteria = tracker.validate_success_criteria()
        assert criteria["file_coverage"].startswith("FAILED")
        assert criteria["overall_success"] == "FAILED"

    def test_get_progress_summary(self, temp_dir):
        spec_dir = temp_dir / "TestSpec"
        spec_dir.mkdir()
        (spec_dir / "Spec.lean").write_text("content")

        config = CoverageConfig(specs_root=temp_dir)
        tracker = CoverageTracker(config)
        summary = tracker.get_progress_summary()
        assert "Verification Progress Summary" in summary
        assert "Total Specs:" in summary
        assert "Issues by Category" in summary
        assert "Success Criteria" in summary

    def test_generate_markdown_report(self, temp_dir):
        spec_dir = temp_dir / "TestSpec"
        spec_dir.mkdir()
        (spec_dir / "Spec.lean").write_text("content")

        output_file = temp_dir / "report.md"
        config = CoverageConfig(specs_root=temp_dir)
        tracker = CoverageTracker(config)
        tracker.generate_markdown_report(output_file)
        assert output_file.exists()
        content = output_file.read_text()
        assert "Verification Coverage Report" in content

    def test_reset_tracking(self):
        tracker = CoverageTracker()
        tracker.track_issue(self._make_issue(IssueCategory.USP, IssueSeverity.MEDIUM))
        tracker.reset_tracking()
        assert len(tracker._verified_files) == 0
        assert len(tracker._verified_specs) == 0
        assert len(tracker._issues_by_category[IssueCategory.USP]) == 0

    def test_get_uncovered_files(self, temp_dir):
        spec_dir = temp_dir / "TestSpec"
        spec_dir.mkdir()
        (spec_dir / "Spec.lean").write_text("content")
        (spec_dir / "Examples.lean").write_text("content")

        config = CoverageConfig(specs_root=temp_dir)
        tracker = CoverageTracker(config)
        uncovered = tracker._get_uncovered_files()
        assert len(uncovered) == 2

    def test_get_uncovered_specs(self, temp_dir):
        spec_dir = temp_dir / "TestSpec"
        spec_dir.mkdir()
        (spec_dir / "Spec.lean").write_text("content")

        config = CoverageConfig(specs_root=temp_dir)
        tracker = CoverageTracker(config)
        uncovered = tracker._get_uncovered_specs()
        assert "TestSpec" in uncovered

    def test_track_specs_with_verified(self, temp_dir):
        spec_dir = temp_dir / "TestSpec"
        spec_dir.mkdir()
        (spec_dir / "Spec.lean").write_text("content")
        (spec_dir / "Examples.lean").write_text("content")
        (spec_dir / "Lemmas.lean").write_text("content")

        config = CoverageConfig(specs_root=temp_dir)
        tracker = CoverageTracker(config)
        tracker.track_compilation_result(CompilationResult(
            file_path=spec_dir / "Spec.lean",
            status=CompilationStatus.SUCCESS,
        ))
        tracker.track_specs(temp_dir)
        assert "TestSpec" in tracker._verified_specs
