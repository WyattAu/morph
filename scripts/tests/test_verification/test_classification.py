"""Tests for issue classification."""

import pytest

from spec_tools.verification.classification import (
    ClassificationConfig,
    IssueClassifier,
)
from spec_tools.verification.models import (
    Issue,
    IssueCategory,
    IssueId,
    IssueSeverity,
)


class TestClassificationConfig:
    def test_defaults(self):
        config = ClassificationConfig()
        assert config.strict_mode is False
        assert config.require_rationale is True
        assert config.allow_secondary_categories is True
        assert config.default_severity == IssueSeverity.MEDIUM


class TestIssueClassifier:
    def _make_issue(self, category, severity, description="test"):
        return Issue(
            issue_id=IssueId(category, 1),
            category=category,
            severity=severity,
            spec_name="S",
            file_path=__import__("pathlib").Path("f.lean"),
            description=description,
        )

    def test_classify_issue_with_category_hint(self):
        classifier = IssueClassifier()
        category, severity, rationale = classifier.classify_issue(
            "test", category_hint=IssueCategory.LCF,
        )
        assert category == IssueCategory.LCF
        assert "hint" in rationale.lower()

    def test_classify_issue_auto_lcf(self):
        classifier = IssueClassifier()
        category, severity, rationale = classifier.classify_issue(
            "compilation error: type mismatch",
        )
        assert category == IssueCategory.LCF

    def test_classify_issue_auto_ibf(self):
        classifier = IssueClassifier()
        category, severity, rationale = classifier.classify_issue(
            "inconsistent definition between files",
        )
        assert category == IssueCategory.IBF

    def test_classify_issue_auto_mel(self):
        classifier = IssueClassifier()
        category, severity, rationale = classifier.classify_issue(
            "missing examples in file",
        )
        assert category == IssueCategory.MEL

    def test_classify_issue_auto_isr(self):
        classifier = IssueClassifier()
        category, severity, rationale = classifier.classify_issue(
            "informal description of property",
        )
        assert category == IssueCategory.ISR

    def test_classify_issue_auto_usp_default(self):
        classifier = IssueClassifier()
        category, severity, rationale = classifier.classify_issue(
            "something unusual about the spec",
        )
        assert category == IssueCategory.USP

    def test_classify_issue_severity_hint(self):
        classifier = IssueClassifier()
        category, severity, rationale = classifier.classify_issue(
            "test", severity_hint=IssueSeverity.CRITICAL,
        )
        assert severity == IssueSeverity.CRITICAL

    def test_classify_issue_critical_indicators(self):
        classifier = IssueClassifier()
        category, severity, rationale = classifier.classify_issue(
            "blocks compilation completely",
        )
        assert severity == IssueSeverity.CRITICAL

    def test_classify_issue_high_indicators(self):
        classifier = IssueClassifier()
        category, severity, rationale = classifier.classify_issue(
            "significant gap in specification",
        )
        assert severity == IssueSeverity.HIGH

    def test_classify_issue_medium_indicators(self):
        classifier = IssueClassifier()
        category, severity, rationale = classifier.classify_issue(
            "ambiguous requirement in section",
        )
        assert severity == IssueSeverity.MEDIUM

    def test_classify_issue_low_default(self):
        classifier = IssueClassifier()
        category, severity, rationale = classifier.classify_issue(
            "a style improvement needed",
        )
        assert severity == IssueSeverity.LOW

    def test_classify_compilation_error_blocks(self):
        classifier = IssueClassifier()
        category, severity = classifier.classify_compilation_error(
            "syntax error", "error", blocks_compilation=True,
        )
        assert category == IssueCategory.LCF
        assert severity == IssueSeverity.CRITICAL

    def test_classify_compilation_error_type(self):
        classifier = IssueClassifier()
        category, severity = classifier.classify_compilation_error(
            "type error", "type mismatch", blocks_compilation=False,
        )
        assert category == IssueCategory.LCF
        assert severity == IssueSeverity.HIGH

    def test_classify_compilation_error_other(self):
        classifier = IssueClassifier()
        category, severity = classifier.classify_compilation_error(
            "warning", "some warning", blocks_compilation=False,
        )
        assert category == IssueCategory.LCF
        assert severity == IssueSeverity.MEDIUM

    def test_classify_missing_content_zero(self):
        classifier = IssueClassifier()
        category, severity = classifier.classify_missing_content("examples", "Examples.lean", 0)
        assert category == IssueCategory.MEL
        assert severity == IssueSeverity.CRITICAL

    def test_classify_missing_content_few(self):
        classifier = IssueClassifier()
        category, severity = classifier.classify_missing_content("examples", "Examples.lean", 2)
        assert category == IssueCategory.MEL
        assert severity == IssueSeverity.HIGH

    def test_classify_missing_content_moderate(self):
        classifier = IssueClassifier()
        category, severity = classifier.classify_missing_content("examples", "Examples.lean", 4)
        assert category == IssueCategory.MEL
        assert severity == IssueSeverity.MEDIUM

    def test_classify_missing_content_sufficient(self):
        classifier = IssueClassifier()
        category, severity = classifier.classify_missing_content("examples", "Examples.lean", 6)
        assert category == IssueCategory.MEL
        assert severity == IssueSeverity.LOW

    def test_classify_inconsistency_contradiction(self):
        classifier = IssueClassifier()
        category, severity = classifier.classify_inconsistency("type", "contradiction found")
        assert category == IssueCategory.IBF
        assert severity == IssueSeverity.CRITICAL

    def test_classify_inconsistency_fundamental(self):
        classifier = IssueClassifier()
        category, severity = classifier.classify_inconsistency("def", "fundamental issue")
        assert category == IssueCategory.IBF
        assert severity == IssueSeverity.HIGH

    def test_classify_inconsistency_minor(self):
        classifier = IssueClassifier()
        category, severity = classifier.classify_inconsistency("def", "minor mismatch")
        assert category == IssueCategory.IBF
        assert severity == IssueSeverity.MEDIUM

    def test_classify_ambiguity_affects_spec(self):
        classifier = IssueClassifier()
        category, severity = classifier.classify_ambiguity("term", affects_specification=True)
        assert category == IssueCategory.USP
        assert severity == IssueSeverity.HIGH

    def test_classify_ambiguity_not_affects_spec(self):
        classifier = IssueClassifier()
        category, severity = classifier.classify_ambiguity("term", affects_specification=False)
        assert category == IssueCategory.USP
        assert severity == IssueSeverity.MEDIUM

    def test_get_classification_statistics(self):
        classifier = IssueClassifier()
        issues = [
            self._make_issue(IssueCategory.LCF, IssueSeverity.CRITICAL),
            self._make_issue(IssueCategory.USP, IssueSeverity.MEDIUM),
        ]
        stats = classifier.get_classification_statistics(issues)
        assert stats["total_issues"] == 2
        assert stats["LCF_count"] == 1
        assert stats["USP_count"] == 1
        assert stats["CRITICAL_count"] == 1
        assert stats["MEDIUM_count"] == 1
        assert stats["classification_accuracy"] == 100.0

    def test_validate_classification_valid(self):
        classifier = IssueClassifier()
        issue = self._make_issue(IssueCategory.USP, IssueSeverity.MEDIUM, "A clear description")
        is_valid, messages = classifier.validate_classification(issue)
        assert is_valid is True
        assert len(messages) == 0

    def test_validate_classification_short_description(self):
        classifier = IssueClassifier()
        issue = self._make_issue(IssueCategory.USP, IssueSeverity.MEDIUM, "short")
        is_valid, messages = classifier.validate_classification(issue)
        assert is_valid is False
        assert any("too short" in m.lower() for m in messages)

    def test_validate_classification_missing_spec_name(self):
        classifier = IssueClassifier()
        issue = Issue(
            issue_id=IssueId(IssueCategory.USP, 1),
            category=IssueCategory.USP,
            severity=IssueSeverity.MEDIUM,
            spec_name="",
            file_path=__import__("pathlib").Path("f.lean"),
            description="A clear description of the issue",
        )
        is_valid, messages = classifier.validate_classification(issue)
        assert is_valid is False
        assert any("spec name" in m.lower() for m in messages)

    def test_validate_classification_strict_lcf(self):
        classifier = IssueClassifier(ClassificationConfig(
            strict_mode=True, require_rationale=False,
        ))
        issue = self._make_issue(IssueCategory.LCF, IssueSeverity.HIGH, "A clear description of issue")
        is_valid, messages = classifier.validate_classification(issue)
        assert is_valid is False
        assert any("LCF" in m for m in messages)

    def test_generate_rationale(self):
        classifier = IssueClassifier()
        category, severity, rationale = classifier.classify_issue(
            "compilation error blocks compilation",
        )
        assert len(rationale) > 0
        assert "LCF" in rationale
