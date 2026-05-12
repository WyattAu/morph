"""Tests for severity assessment."""

import pytest

from spec_tools.verification.models import (
    Issue,
    IssueCategory,
    IssueId,
    IssueSeverity,
)
from spec_tools.verification.severity import SeverityAssessor, SeverityConfig


class TestSeverityConfig:
    def test_defaults(self):
        config = SeverityConfig()
        assert config.strict_mode is False
        assert config.require_rationale is True
        assert config.enable_peer_review is True
        assert IssueSeverity.CRITICAL in config.resource_allocation
        assert config.resource_allocation[IssueSeverity.CRITICAL] == 0.50


class TestSeverityAssessor:
    def _make_issue(self, category, severity, description="test issue"):
        return Issue(
            issue_id=IssueId(category, 1),
            category=category,
            severity=severity,
            spec_name="TestSpec",
            file_path=__import__("pathlib").Path("test.lean"),
            description=description,
        )

    def test_assess_with_override(self):
        assessor = SeverityAssessor()
        issue = self._make_issue(IssueCategory.USP, IssueSeverity.MEDIUM)
        severity, rationale = assessor.assess_severity(issue, override_severity=IssueSeverity.CRITICAL)
        assert severity == IssueSeverity.CRITICAL
        assert "overridden" in rationale.lower()

    def test_assess_by_category_lcf(self):
        assessor = SeverityAssessor()
        issue = self._make_issue(IssueCategory.LCF, IssueSeverity.MEDIUM, "blocks_compilation error")
        severity, rationale = assessor.assess_severity(issue)
        assert severity == IssueSeverity.CRITICAL

    def test_assess_by_category_ibf_critical(self):
        assessor = SeverityAssessor()
        issue = self._make_issue(IssueCategory.IBF, IssueSeverity.MEDIUM, "contradiction found")
        severity, rationale = assessor.assess_severity(issue)
        assert severity == IssueSeverity.CRITICAL

    def test_assess_by_category_ibf_high(self):
        assessor = SeverityAssessor()
        issue = self._make_issue(IssueCategory.IBF, IssueSeverity.MEDIUM, "different definition detected")
        severity, rationale = assessor.assess_severity(issue)
        assert severity == IssueSeverity.HIGH

    def test_assess_by_category_mel_critical(self):
        assessor = SeverityAssessor()
        issue = self._make_issue(IssueCategory.MEL, IssueSeverity.MEDIUM, "empty file content")
        severity, rationale = assessor.assess_severity(issue)
        assert severity == IssueSeverity.CRITICAL

    def test_assess_by_category_mel_high(self):
        assessor = SeverityAssessor()
        issue = self._make_issue(IssueCategory.MEL, IssueSeverity.MEDIUM, "missing key lemma")
        severity, rationale = assessor.assess_severity(issue)
        assert severity == IssueSeverity.HIGH

    def test_assess_by_category_isr_high(self):
        assessor = SeverityAssessor()
        issue = self._make_issue(IssueCategory.ISR, IssueSeverity.MEDIUM, "informal description")
        severity, rationale = assessor.assess_severity(issue)
        assert severity == IssueSeverity.HIGH

    def test_assess_by_category_usp_high(self):
        assessor = SeverityAssessor()
        issue = self._make_issue(IssueCategory.USP, IssueSeverity.MEDIUM, "ambiguous specification")
        severity, rationale = assessor.assess_severity(issue)
        assert severity == IssueSeverity.HIGH

    def test_assess_compilation_error_blocks(self):
        assessor = SeverityAssessor()
        severity = assessor.assess_compilation_error("syntax", blocks_compilation=True)
        assert severity == IssueSeverity.CRITICAL

    def test_assess_compilation_error_type(self):
        assessor = SeverityAssessor()
        severity = assessor.assess_compilation_error("type error", blocks_compilation=False)
        assert severity == IssueSeverity.HIGH

    def test_assess_compilation_error_import(self):
        assessor = SeverityAssessor()
        severity = assessor.assess_compilation_error("import error", blocks_compilation=False)
        assert severity == IssueSeverity.HIGH

    def test_assess_compilation_error_other(self):
        assessor = SeverityAssessor()
        severity = assessor.assess_compilation_error("warning", blocks_compilation=False)
        assert severity == IssueSeverity.MEDIUM

    def test_assess_missing_content_zero(self):
        assessor = SeverityAssessor()
        severity = assessor.assess_missing_content("examples", "Examples.lean", 0)
        assert severity == IssueSeverity.CRITICAL

    def test_assess_missing_content_few(self):
        assessor = SeverityAssessor()
        severity = assessor.assess_missing_content("examples", "Examples.lean", 2)
        assert severity == IssueSeverity.HIGH

    def test_assess_missing_content_moderate(self):
        assessor = SeverityAssessor()
        severity = assessor.assess_missing_content("examples", "Examples.lean", 4)
        assert severity == IssueSeverity.MEDIUM

    def test_assess_missing_content_sufficient(self):
        assessor = SeverityAssessor()
        severity = assessor.assess_missing_content("examples", "Examples.lean", 6)
        assert severity == IssueSeverity.LOW

    def test_assess_inconsistency_contradiction(self):
        assessor = SeverityAssessor()
        severity = assessor.assess_inconsistency("type", "fundamental contradiction")
        assert severity == IssueSeverity.CRITICAL

    def test_assess_inconsistency_conflict(self):
        assessor = SeverityAssessor()
        severity = assessor.assess_inconsistency("def", "conflict detected")
        assert severity == IssueSeverity.CRITICAL

    def test_assess_inconsistency_core_spec(self):
        assessor = SeverityAssessor()
        severity = assessor.assess_inconsistency("def", "minor issue", affects_core_specification=True)
        assert severity == IssueSeverity.HIGH

    def test_assess_inconsistency_minor(self):
        assessor = SeverityAssessor()
        severity = assessor.assess_inconsistency("def", "minor mismatch")
        assert severity == IssueSeverity.MEDIUM

    def test_assess_ambiguity_affects_spec(self):
        assessor = SeverityAssessor()
        severity = assessor.assess_ambiguity("term", affects_specification=True)
        assert severity == IssueSeverity.HIGH

    def test_assess_ambiguity_not_affects_spec(self):
        assessor = SeverityAssessor()
        severity = assessor.assess_ambiguity("term", affects_specification=False)
        assert severity == IssueSeverity.MEDIUM

    def test_get_priority_order(self):
        assessor = SeverityAssessor()
        issues = [
            self._make_issue(IssueCategory.USP, IssueSeverity.LOW),
            self._make_issue(IssueCategory.LCF, IssueSeverity.CRITICAL),
            self._make_issue(IssueCategory.IBF, IssueSeverity.HIGH),
        ]
        sorted_issues = assessor.get_priority_order(issues)
        assert sorted_issues[0].severity == IssueSeverity.CRITICAL
        assert sorted_issues[-1].severity == IssueSeverity.LOW

    def test_get_resource_allocation_empty(self):
        assessor = SeverityAssessor()
        allocation = assessor.get_resource_allocation([])
        for severity in IssueSeverity:
            assert allocation[severity] == 0

    def test_get_resource_allocation_with_issues(self):
        assessor = SeverityAssessor()
        issues = [self._make_issue(IssueCategory.USP, IssueSeverity.CRITICAL) for _ in range(10)]
        allocation = assessor.get_resource_allocation(issues)
        assert allocation[IssueSeverity.CRITICAL] == 5

    def test_get_severity_statistics_empty(self):
        assessor = SeverityAssessor()
        stats = assessor.get_severity_statistics([])
        assert stats["total_issues"] == 0
        assert stats["critical_priority"] is False
        assert stats["high_priority"] is False

    def test_get_severity_statistics_with_issues(self):
        assessor = SeverityAssessor()
        issues = [
            self._make_issue(IssueCategory.LCF, IssueSeverity.CRITICAL),
            self._make_issue(IssueCategory.USP, IssueSeverity.HIGH),
        ]
        stats = assessor.get_severity_statistics(issues)
        assert stats["total_issues"] == 2
        assert stats["CRITICAL_count"] == 1
        assert stats["HIGH_percentage"] == 50.0
        assert stats["critical_priority"] is True
        assert stats["high_priority"] is True

    def test_validate_severity_valid(self):
        assessor = SeverityAssessor(SeverityConfig(require_rationale=False))
        issue = self._make_issue(IssueCategory.USP, IssueSeverity.MEDIUM)
        issue.notes = "rationale"
        is_valid, messages = assessor.validate_severity(issue)
        assert is_valid is True
        assert len(messages) == 0

    def test_validate_severity_strict_lcf(self):
        assessor = SeverityAssessor(SeverityConfig(
            strict_mode=True, require_rationale=False,
        ))
        issue = self._make_issue(IssueCategory.LCF, IssueSeverity.HIGH)
        issue.notes = "rationale"
        is_valid, messages = assessor.validate_severity(issue)
        assert is_valid is False
        assert any("LCF" in m for m in messages)

    def test_validate_severity_missing_rationale(self):
        assessor = SeverityAssessor(SeverityConfig(require_rationale=True))
        issue = self._make_issue(IssueCategory.USP, IssueSeverity.MEDIUM)
        issue.notes = None
        is_valid, messages = assessor.validate_severity(issue)
        assert is_valid is False
        assert any("Rationale" in m for m in messages)

    def test_generate_rationale_lcf_critical(self):
        assessor = SeverityAssessor()
        issue = self._make_issue(IssueCategory.LCF, IssueSeverity.CRITICAL, "blocks_compilation detected")
        severity, rationale = assessor.assess_severity(issue)
        assert "immediate attention" in rationale.lower()

    def test_generate_rationale_ibf_critical(self):
        assessor = SeverityAssessor()
        issue = self._make_issue(IssueCategory.IBF, IssueSeverity.CRITICAL, "fundamental contradiction")
        severity, rationale = assessor.assess_severity(issue)
        assert "contradiction" in rationale.lower()

    def test_generate_rationale_mel_critical(self):
        assessor = SeverityAssessor()
        issue = self._make_issue(IssueCategory.MEL, IssueSeverity.CRITICAL, "empty content")
        severity, rationale = assessor.assess_severity(issue)
        assert "missing critical content" in rationale.lower()

    def test_generate_rationale_isr_high(self):
        assessor = SeverityAssessor()
        issue = self._make_issue(IssueCategory.ISR, IssueSeverity.HIGH, "informal description")
        severity, rationale = assessor.assess_severity(issue)
        assert "formal rigor" in rationale.lower()

    def test_generate_rationale_usp_high(self):
        assessor = SeverityAssessor()
        issue = self._make_issue(IssueCategory.USP, IssueSeverity.HIGH, "ambiguous specification")
        severity, rationale = assessor.assess_severity(issue)
        assert "multiple interpretation" in rationale.lower()
