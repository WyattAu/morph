"""Tests for risk assessment check."""

from pathlib import Path

from spec_tools.validation.checks.risk_assessment import RiskAssessmentCheck
from spec_tools.models import Severity


class TestRiskAssessmentCheck:
    def test_description(self):
        check = RiskAssessmentCheck()
        assert "risk" in check.description.lower()

    def test_missing_section(self):
        check = RiskAssessmentCheck()
        errors = check.validate("# Spec\n\nNothing here.\n", Path("test.md"))
        assert len(errors) == 1
        assert errors[0].rule_id == "RISK-001"
        assert errors[0].severity == Severity.ERROR

    def test_missing_identified_risks(self):
        check = RiskAssessmentCheck()
        content = "## Risk Assessment\n\nSome text.\n"
        errors = check.validate(content, Path("test.md"))
        assert any(e.rule_id == "RISK-002" for e in errors)

    def test_empty_identified_risks(self):
        check = RiskAssessmentCheck()
        content = (
            "## Risk Assessment\n\n"
            "### Identified Risks\n\n"
            "### Mitigation Strategies\n- Strategy\n"
        )
        errors = check.validate(content, Path("test.md"))
        assert any(e.rule_id == "RISK-003" for e in errors)

    def test_risks_table_too_short(self):
        check = RiskAssessmentCheck()
        content = (
            "## Risk Assessment\n\n"
            "### Identified Risks\n\n"
            "| Risk |\n"
            "|------|\n"
            "### Mitigation Strategies\n- Strategy\n"
        )
        errors = check.validate(content, Path("test.md"))
        assert any(e.rule_id == "RISK-004" for e in errors)

    def test_risks_table_missing_columns(self):
        check = RiskAssessmentCheck()
        content = (
            "## Risk Assessment\n\n"
            "### Identified Risks\n\n"
            "| Name | Value |\n"
            "|------|-------|\n"
            "| DB fail | high |\n"
            "### Mitigation Strategies\n- Strategy\n"
        )
        errors = check.validate(content, Path("test.md"))
        assert any(e.rule_id == "RISK-005" for e in errors)

    def test_risks_table_empty_probability(self):
        check = RiskAssessmentCheck()
        content = (
            "## Risk Assessment\n\n"
            "### Identified Risks\n\n"
            "| Risk | Probability | Impact |\n"
            "|------|-------------|--------|\n"
            "| DB fail | | High |\n"
            "### Mitigation Strategies\n- Strategy\n"
        )
        errors = check.validate(content, Path("test.md"))
        assert any(e.rule_id == "RISK-006" for e in errors)
        assert any(e.severity == Severity.WARNING for e in errors if e.rule_id == "RISK-006")

    def test_risks_table_empty_impact(self):
        check = RiskAssessmentCheck()
        content = (
            "## Risk Assessment\n\n"
            "### Identified Risks\n\n"
            "| Risk | Probability | Impact |\n"
            "|------|-------------|--------|\n"
            "| DB fail | Medium | |\n"
            "### Mitigation Strategies\n- Strategy\n"
        )
        errors = check.validate(content, Path("test.md"))
        assert any(e.rule_id == "RISK-007" for e in errors)

    def test_missing_mitigation_strategies(self):
        check = RiskAssessmentCheck()
        content = (
            "## Risk Assessment\n\n"
            "### Identified Risks\n- DB failure\n"
        )
        errors = check.validate(content, Path("test.md"))
        assert any(e.rule_id == "RISK-008" for e in errors)

    def test_empty_mitigation_strategies(self):
        check = RiskAssessmentCheck()
        content = (
            "## Risk Assessment\n\n"
            "### Identified Risks\n- DB failure\n"
            "### Mitigation Strategies\n\n"
        )
        errors = check.validate(content, Path("test.md"))
        assert any(e.rule_id == "RISK-009" for e in errors)

    def test_complete_risk_assessment_with_table(self):
        check = RiskAssessmentCheck()
        content = (
            "## Risk Assessment\n\n"
            "### Identified Risks\n\n"
            "| Risk | Probability | Impact |\n"
            "|------|-------------|--------|\n"
            "| DB fail | Medium | High |\n"
            "### Mitigation Strategies\n- Replication\n- Backups\n"
        )
        errors = check.validate(content, Path("test.md"))
        assert len(errors) == 0

    def test_complete_risk_assessment_with_list(self):
        check = RiskAssessmentCheck()
        content = (
            "## Risk Assessment\n\n"
            "### Identified Risks\n- DB failure\n- Network issues\n"
            "### Mitigation Strategies\n- Replication\n"
        )
        errors = check.validate(content, Path("test.md"))
        assert len(errors) == 0

    def test_suggestions_provided(self):
        check = RiskAssessmentCheck()
        errors = check.validate("# Spec\n", Path("test.md"))
        assert all(e.suggestion is not None for e in errors)
