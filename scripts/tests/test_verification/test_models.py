"""Tests for verification data models."""

from datetime import datetime
from pathlib import Path

from spec_tools.verification.models import (
    CompilationError,
    CompilationResult,
    CompilationStatus,
    CoverageMetrics,
    CoverageReport,
    Issue,
    IssueCategory,
    IssueId,
    IssueSeverity,
)


class TestCompilationStatus:
    def test_values(self):
        assert CompilationStatus.SUCCESS.value == "SUCCESS"
        assert CompilationStatus.FAILED.value == "FAILED"
        assert CompilationStatus.TIMEOUT.value == "TIMEOUT"
        assert CompilationStatus.MEMORY_ERROR.value == "MEMORY_ERROR"
        assert CompilationStatus.DEPENDENCY_ERROR.value == "DEPENDENCY_ERROR"


class TestIssueCategory:
    def test_values(self):
        assert IssueCategory.USP.value == "USP"
        assert IssueCategory.LCF.value == "LCF"
        assert IssueCategory.ISR.value == "ISR"
        assert IssueCategory.MEL.value == "MEL"
        assert IssueCategory.IBF.value == "IBF"


class TestIssueSeverity:
    def test_values(self):
        assert IssueSeverity.CRITICAL.value == "CRITICAL"
        assert IssueSeverity.HIGH.value == "HIGH"
        assert IssueSeverity.MEDIUM.value == "MEDIUM"
        assert IssueSeverity.LOW.value == "LOW"


class TestIssueId:
    def test_str_format(self):
        issue_id = IssueId(IssueCategory.USP, 1)
        assert str(issue_id) == "USP-001"

    def test_str_format_large_number(self):
        issue_id = IssueId(IssueCategory.LCF, 42)
        assert str(issue_id) == "LCF-042"


class TestCompilationError:
    def test_str_basic(self):
        error = CompilationError(
            file_path=Path("test.lean"),
            line_number=10,
            error_type="type error",
            error_message="expected Nat, got String",
        )
        result = str(error)
        assert "test.lean:10" in result
        assert "type error" in result
        assert "expected Nat, got String" in result

    def test_str_with_column(self):
        error = CompilationError(
            file_path=Path("test.lean"),
            line_number=10,
            column_number=5,
            error_type="syntax error",
            error_message="unexpected token",
        )
        result = str(error)
        assert "test.lean:10:5" in result

    def test_str_with_suggestion(self):
        error = CompilationError(
            file_path=Path("test.lean"),
            line_number=10,
            error_type="type error",
            error_message="unknown identifier",
            suggestion="Check imports",
        )
        result = str(error)
        assert "Suggestion: Check imports" in result

    def test_str_without_suggestion(self):
        error = CompilationError(
            file_path=Path("test.lean"),
            line_number=10,
            error_type="type error",
            error_message="unknown identifier",
        )
        result = str(error)
        assert "Suggestion:" not in result


class TestCompilationResult:
    def test_success_property(self):
        result = CompilationResult(
            file_path=Path("test.lean"),
            status=CompilationStatus.SUCCESS,
        )
        assert result.success is True
        assert result.error_count == 0

    def test_failed_property(self):
        result = CompilationResult(
            file_path=Path("test.lean"),
            status=CompilationStatus.FAILED,
            errors=[CompilationError(Path("test.lean"), 1, error_type="e")],
        )
        assert result.success is False
        assert result.error_count == 1

    def test_multiple_errors(self):
        errors = [
            CompilationError(Path("a.lean"), 1, error_type="e1"),
            CompilationError(Path("a.lean"), 2, error_type="e2"),
            CompilationError(Path("a.lean"), 3, error_type="e3"),
        ]
        result = CompilationResult(
            file_path=Path("a.lean"),
            status=CompilationStatus.FAILED,
            errors=errors,
        )
        assert result.error_count == 3


class TestIssue:
    def test_str_representation(self):
        issue = Issue(
            issue_id=IssueId(IssueCategory.USP, 1),
            category=IssueCategory.USP,
            severity=IssueSeverity.MEDIUM,
            spec_name="TestSpec",
            file_path=Path("Spec.lean"),
            description="Unclear specification point",
        )
        result = str(issue)
        assert "[MEDIUM]" in result
        assert "USP-001" in result
        assert "Unclear specification point" in result
        assert "TestSpec" in result
        assert "OPEN" in result

    def test_defaults(self):
        issue = Issue(
            issue_id=IssueId(IssueCategory.LCF, 1),
            category=IssueCategory.LCF,
            severity=IssueSeverity.CRITICAL,
            spec_name="Spec",
            file_path=Path("file.lean"),
        )
        assert issue.line_numbers == []
        assert issue.description == ""
        assert issue.status == "OPEN"
        assert issue.discovered_at is not None


class TestCoverageMetrics:
    def test_zero_division_spec_coverage(self):
        metrics = CoverageMetrics(total_specs=0)
        assert metrics.spec_coverage == 0.0

    def test_zero_division_file_coverage(self):
        metrics = CoverageMetrics(total_files=0)
        assert metrics.file_coverage == 0.0

    def test_zero_division_spec_point_coverage(self):
        metrics = CoverageMetrics(total_spec_points=0)
        assert metrics.spec_point_coverage == 0.0

    def test_spec_coverage(self):
        metrics = CoverageMetrics(total_specs=10, verified_specs=7)
        assert metrics.spec_coverage == 70.0

    def test_file_coverage(self):
        metrics = CoverageMetrics(total_files=20, verified_files=15)
        assert metrics.file_coverage == 75.0

    def test_spec_point_coverage(self):
        metrics = CoverageMetrics(total_spec_points=10, verified_spec_points=3)
        assert metrics.spec_point_coverage == 30.0


class TestCoverageReport:
    def test_total_issues(self):
        metrics = CoverageMetrics(
            issues_by_severity={
                IssueSeverity.CRITICAL: 2,
                IssueSeverity.HIGH: 3,
                IssueSeverity.MEDIUM: 5,
                IssueSeverity.LOW: 1,
            }
        )
        report = CoverageReport(metrics=metrics)
        assert report.total_issues == 11

    def test_critical_issues(self):
        metrics = CoverageMetrics(issues_by_severity={IssueSeverity.CRITICAL: 5})
        report = CoverageReport(metrics=metrics)
        assert report.critical_issues == 5

    def test_critical_issues_missing(self):
        metrics = CoverageMetrics(issues_by_severity={})
        report = CoverageReport(metrics=metrics)
        assert report.critical_issues == 0

    def test_high_issues(self):
        metrics = CoverageMetrics(issues_by_severity={IssueSeverity.HIGH: 3})
        report = CoverageReport(metrics=metrics)
        assert report.high_issues == 3

    def test_medium_issues(self):
        metrics = CoverageMetrics(issues_by_severity={IssueSeverity.MEDIUM: 4})
        report = CoverageReport(metrics=metrics)
        assert report.medium_issues == 4

    def test_low_issues(self):
        metrics = CoverageMetrics(issues_by_severity={IssueSeverity.LOW: 2})
        report = CoverageReport(metrics=metrics)
        assert report.low_issues == 2
