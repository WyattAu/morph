"""Tests for performance spec check."""

from pathlib import Path

from spec_tools.validation.checks.performance import PerformanceSpecCheck
from spec_tools.models import Severity


class TestPerformanceSpecCheck:
    def test_description(self):
        check = PerformanceSpecCheck()
        assert "performance" in check.description.lower()

    def test_missing_section(self):
        check = PerformanceSpecCheck()
        errors = check.validate("# Spec\n\nNothing here.\n", Path("test.md"))
        assert len(errors) == 1
        assert errors[0].rule_id == "PERFORMANCE-001"
        assert errors[0].severity == Severity.ERROR

    def test_missing_performance_metrics(self):
        check = PerformanceSpecCheck()
        content = "## Performance Specifications\n\nSome text.\n"
        errors = check.validate(content, Path("test.md"))
        assert any(e.rule_id == "PERFORMANCE-002" for e in errors)

    def test_empty_performance_metrics(self):
        check = PerformanceSpecCheck()
        content = (
            "## Performance Specifications\n\n"
            "### Performance Metrics\n\n"
            "### Measurement Methods\n- Benchmark\n"
        )
        errors = check.validate(content, Path("test.md"))
        assert any(e.rule_id == "PERFORMANCE-003" for e in errors)

    def test_metrics_table_too_short(self):
        check = PerformanceSpecCheck()
        content = (
            "## Performance Specifications\n\n"
            "### Performance Metrics\n\n"
            "| Metric |\n"
            "|--------|\n"
            "### Measurement Methods\n- Methods\n"
        )
        errors = check.validate(content, Path("test.md"))
        assert any(e.rule_id == "PERFORMANCE-004" for e in errors)

    def test_metrics_table_missing_columns(self):
        check = PerformanceSpecCheck()
        content = (
            "## Performance Specifications\n\n"
            "### Performance Metrics\n\n"
            "| Name | Value |\n"
            "|------|-------|\n"
            "| RT | 200ms |\n"
            "### Measurement Methods\n- Methods\n"
        )
        errors = check.validate(content, Path("test.md"))
        assert any(e.rule_id == "PERFORMANCE-005" for e in errors)

    def test_metrics_table_empty_target(self):
        check = PerformanceSpecCheck()
        content = (
            "## Performance Specifications\n\n"
            "### Performance Metrics\n\n"
            "| Metric | Target |\n"
            "|--------|--------|\n"
            "| RT | |\n"
            "### Measurement Methods\n- Methods\n"
        )
        errors = check.validate(content, Path("test.md"))
        assert any(e.rule_id == "PERFORMANCE-006" for e in errors)
        assert any(e.severity == Severity.WARNING for e in errors if e.rule_id == "PERFORMANCE-006")

    def test_missing_performance_targets(self):
        check = PerformanceSpecCheck()
        content = (
            "## Performance Specifications\n\n"
            "### Performance Metrics\n- Response time < 200ms\n"
            "### Measurement Methods\n- Benchmark\n"
        )
        errors = check.validate(content, Path("test.md"))
        assert any(e.rule_id == "PERFORMANCE-007" for e in errors)

    def test_empty_performance_targets(self):
        check = PerformanceSpecCheck()
        content = (
            "## Performance Specifications\n\n"
            "### Performance Metrics\n- RT < 200ms\n"
            "### Performance Targets\n\n"
            "### Measurement Methods\n- Methods\n"
        )
        errors = check.validate(content, Path("test.md"))
        assert any(e.rule_id == "PERFORMANCE-008" for e in errors)

    def test_missing_measurement_methods(self):
        check = PerformanceSpecCheck()
        content = (
            "## Performance Specifications\n\n"
            "### Performance Metrics\n- RT < 200ms\n"
            "### Performance Targets\n- p95 latency\n"
        )
        errors = check.validate(content, Path("test.md"))
        assert any(e.rule_id == "PERFORMANCE-009" for e in errors)

    def test_empty_measurement_methods(self):
        check = PerformanceSpecCheck()
        content = (
            "## Performance Specifications\n\n"
            "### Performance Metrics\n- RT < 200ms\n"
            "### Performance Targets\n- p95 latency\n"
            "### Measurement Methods\n\n"
        )
        errors = check.validate(content, Path("test.md"))
        assert any(e.rule_id == "PERFORMANCE-010" for e in errors)

    def test_complete_performance_with_table(self):
        check = PerformanceSpecCheck()
        content = (
            "## Performance Specifications\n\n"
            "### Performance Metrics\n\n"
            "| Metric | Target |\n"
            "|--------|--------|\n"
            "| RT | < 200ms |\n"
            "| Throughput | > 10000 RPS |\n"
            "### Performance Targets\n- p95 latency\n- Peak throughput\n"
            "### Measurement Methods\n- Load testing\n- Benchmarking\n"
        )
        errors = check.validate(content, Path("test.md"))
        assert len(errors) == 0

    def test_complete_performance_with_list(self):
        check = PerformanceSpecCheck()
        content = (
            "## Performance Specifications\n\n"
            "### Performance Metrics\n- RT < 200ms\n- Throughput > 10k\n"
            "### Performance Targets\n- p95\n"
            "### Measurement Methods\n- Load test\n"
        )
        errors = check.validate(content, Path("test.md"))
        assert len(errors) == 0

    def test_suggestions_provided(self):
        check = PerformanceSpecCheck()
        errors = check.validate("# Spec\n", Path("test.md"))
        assert all(e.suggestion is not None for e in errors)
