"""Tests for maintainability spec check."""

from pathlib import Path

from spec_tools.validation.checks.maintainability import MaintainabilitySpecCheck
from spec_tools.models import Severity


class TestMaintainabilitySpecCheck:
    def test_description(self):
        check = MaintainabilitySpecCheck()
        assert "maintainability" in check.description.lower()

    def test_missing_section(self):
        check = MaintainabilitySpecCheck()
        errors = check.validate("# Spec\n\nNothing here.\n", Path("test.md"))
        assert len(errors) == 1
        assert errors[0].rule_id == "MAINTAINABILITY-001"
        assert errors[0].severity == Severity.ERROR

    def test_missing_code_quality_metrics(self):
        check = MaintainabilitySpecCheck()
        content = "## Maintainability Specifications\n\nSome text.\n"
        errors = check.validate(content, Path("test.md"))
        assert any(e.rule_id == "MAINTAINABILITY-002" for e in errors)

    def test_empty_code_quality_metrics(self):
        check = MaintainabilitySpecCheck()
        content = (
            "## Maintainability Specifications\n\n"
            "### Code Quality Metrics\n\n"
            "### Documentation Standards\n- Docstrings required\n"
            "### Evolution Strategy\n- Versioning approach\n"
        )
        errors = check.validate(content, Path("test.md"))
        assert any(e.rule_id == "MAINTAINABILITY-003" for e in errors)

    def test_metrics_table_too_short(self):
        check = MaintainabilitySpecCheck()
        content = (
            "## Maintainability Specifications\n\n"
            "### Code Quality Metrics\n\n"
            "| Metric |\n"
            "|--------|\n"
            "### Documentation Standards\n- Docs\n"
            "### Evolution Strategy\n- Strategy\n"
        )
        errors = check.validate(content, Path("test.md"))
        assert any(e.rule_id == "MAINTAINABILITY-004" for e in errors)

    def test_metrics_table_missing_columns(self):
        check = MaintainabilitySpecCheck()
        content = (
            "## Maintainability Specifications\n\n"
            "### Code Quality Metrics\n\n"
            "| Name | Value |\n"
            "|------|-------|\n"
            "| CC | 10 |\n"
            "### Documentation Standards\n- Docs\n"
            "### Evolution Strategy\n- Strategy\n"
        )
        errors = check.validate(content, Path("test.md"))
        assert any(e.rule_id == "MAINTAINABILITY-005" for e in errors)

    def test_metrics_table_empty_target(self):
        check = MaintainabilitySpecCheck()
        content = (
            "## Maintainability Specifications\n\n"
            "### Code Quality Metrics\n\n"
            "| Metric | Target |\n"
            "|--------|--------|\n"
            "| CC | |\n"
            "### Documentation Standards\n- Docs\n"
            "### Evolution Strategy\n- Strategy\n"
        )
        errors = check.validate(content, Path("test.md"))
        assert any(e.rule_id == "MAINTAINABILITY-006" for e in errors)
        assert any(e.severity == Severity.WARNING for e in errors if e.rule_id == "MAINTAINABILITY-006")

    def test_missing_documentation_standards(self):
        check = MaintainabilitySpecCheck()
        content = (
            "## Maintainability Specifications\n\n"
            "### Code Quality Metrics\n- Coverage > 80%\n"
            "### Evolution Strategy\n- Versioning\n"
        )
        errors = check.validate(content, Path("test.md"))
        assert any(e.rule_id == "MAINTAINABILITY-007" for e in errors)

    def test_empty_documentation_standards(self):
        check = MaintainabilitySpecCheck()
        content = (
            "## Maintainability Specifications\n\n"
            "### Code Quality Metrics\n- Coverage > 80%\n"
            "### Documentation Standards\n\n"
            "### Evolution Strategy\n- Strategy\n"
        )
        errors = check.validate(content, Path("test.md"))
        assert any(e.rule_id == "MAINTAINABILITY-008" for e in errors)

    def test_missing_evolution_strategy(self):
        check = MaintainabilitySpecCheck()
        content = (
            "## Maintainability Specifications\n\n"
            "### Code Quality Metrics\n- Coverage > 80%\n"
            "### Documentation Standards\n- Docstrings\n"
        )
        errors = check.validate(content, Path("test.md"))
        assert any(e.rule_id == "MAINTAINABILITY-009" for e in errors)

    def test_empty_evolution_strategy(self):
        check = MaintainabilitySpecCheck()
        content = (
            "## Maintainability Specifications\n\n"
            "### Code Quality Metrics\n- Coverage > 80%\n"
            "### Documentation Standards\n- Docstrings\n"
            "### Evolution Strategy\n\n"
        )
        errors = check.validate(content, Path("test.md"))
        assert any(e.rule_id == "MAINTAINABILITY-010" for e in errors)

    def test_complete_maintainability_with_table(self):
        check = MaintainabilitySpecCheck()
        content = (
            "## Maintainability Specifications\n\n"
            "### Code Quality Metrics\n\n"
            "| Metric | Target |\n"
            "|--------|--------|\n"
            "| CC | < 10 |\n"
            "| Coverage | > 80% |\n"
            "### Documentation Standards\n- Docstrings required\n- API docs\n"
            "### Evolution Strategy\n- Semantic versioning\n"
        )
        errors = check.validate(content, Path("test.md"))
        assert len(errors) == 0

    def test_complete_maintainability_with_list(self):
        check = MaintainabilitySpecCheck()
        content = (
            "## Maintainability Specifications\n\n"
            "### Code Quality Metrics\n- Coverage > 80%\n- CC < 10\n"
            "### Documentation Standards\n- Docstrings\n"
            "### Evolution Strategy\n- Versioning\n"
        )
        errors = check.validate(content, Path("test.md"))
        assert len(errors) == 0

    def test_suggestions_provided(self):
        check = MaintainabilitySpecCheck()
        errors = check.validate("# Spec\n", Path("test.md"))
        assert all(e.suggestion is not None for e in errors)
