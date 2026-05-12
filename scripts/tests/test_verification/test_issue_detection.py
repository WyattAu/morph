"""Tests for automated issue detection."""

from pathlib import Path
from typing import List

import pytest

from spec_tools.verification.issue_detection import (
    AutomatedIssueDetector,
    DetectionConfig,
)
from spec_tools.verification.models import (
    Issue,
    IssueCategory,
    IssueId,
    IssueSeverity,
)


class TestDetectionConfig:
    def test_defaults(self):
        config = DetectionConfig()
        assert config.detect_usp is True
        assert config.detect_lcf is True
        assert config.detect_isr is True
        assert config.detect_mel is True
        assert config.detect_ibf is True
        assert config.strict_mode is False


class TestAutomatedIssueDetector:
    def test_init_default_config(self):
        detector = AutomatedIssueDetector()
        assert detector.config is not None
        assert detector.config.detect_usp is True

    def test_init_custom_config(self):
        config = DetectionConfig(detect_usp=False, detect_mel=False)
        detector = AutomatedIssueDetector(config=config)
        assert detector.config.detect_usp is False
        assert detector.config.detect_mel is False

    def test_detect_usp_issues(self, temp_dir):
        content = "def foo : Nat :=\n  appropriate value\n  should be defined\n"
        lean_file = temp_dir / "Spec.lean"
        lean_file.write_text(content)

        detector = AutomatedIssueDetector(DetectionConfig(
            detect_isr=False, detect_mel=False, detect_ibf=False, detect_lcf=False,
        ))
        issues = detector.detect_issues(lean_file)

        usp_issues = [i for i in issues if i.category == IssueCategory.USP]
        assert len(usp_issues) > 0
        for issue in usp_issues:
            assert issue.severity == IssueSeverity.MEDIUM
            assert "USP" in str(issue.issue_id)

    def test_detect_isr_issues(self, temp_dir):
        content = "def bar : Nat :=\n  /* informal description */\n"
        lean_file = temp_dir / "Spec.lean"
        lean_file.write_text(content)

        detector = AutomatedIssueDetector(DetectionConfig(
            detect_usp=False, detect_mel=False, detect_ibf=False, detect_lcf=False,
        ))
        issues = detector.detect_issues(lean_file)

        isr_issues = [i for i in issues if i.category == IssueCategory.ISR]
        assert len(isr_issues) > 0

    def test_detect_mel_empty_file(self, temp_dir):
        lean_file = temp_dir / "Spec.lean"
        lean_file.write_text("-- only comments\n")

        detector = AutomatedIssueDetector(DetectionConfig(
            detect_usp=False, detect_isr=False, detect_ibf=False, detect_lcf=False,
        ))
        issues = detector.detect_issues(lean_file)

        mel_issues = [i for i in issues if i.category == IssueCategory.MEL]
        assert len(mel_issues) >= 1
        assert any("empty" in i.description.lower() or "only comments" in i.description.lower() for i in mel_issues)

    def test_detect_mel_few_examples(self, temp_dir):
        content = "def foo : Nat := 0\nexample : True := trivial\n"
        lean_file = temp_dir / "Examples.lean"
        lean_file.write_text(content)

        detector = AutomatedIssueDetector(DetectionConfig(
            detect_usp=False, detect_isr=False, detect_ibf=False, detect_lcf=False,
        ))
        issues = detector.detect_issues(lean_file)

        mel_issues = [i for i in issues if i.category == IssueCategory.MEL]
        assert any("Insufficient examples" in i.description for i in mel_issues)

    def test_detect_mel_few_lemmas(self, temp_dir):
        content = "def foo : Nat := 0\nlemma bar : True := trivial\n"
        lean_file = temp_dir / "Lemmas.lean"
        lean_file.write_text(content)

        detector = AutomatedIssueDetector(DetectionConfig(
            detect_usp=False, detect_isr=False, detect_ibf=False, detect_lcf=False,
        ))
        issues = detector.detect_issues(lean_file)

        mel_issues = [i for i in issues if i.category == IssueCategory.MEL]
        assert any("Insufficient lemmas" in i.description for i in mel_issues)

    def test_detect_ibf_duplicate_definitions(self, temp_dir):
        content = "def foo : Nat := 0\ndef bar : Nat := 1\ndef foo : Nat := 2\n"
        lean_file = temp_dir / "Spec.lean"
        lean_file.write_text(content)

        detector = AutomatedIssueDetector(DetectionConfig(
            detect_usp=False, detect_isr=False, detect_mel=False, detect_lcf=False,
        ))
        issues = detector.detect_issues(lean_file)

        ibf_issues = [i for i in issues if i.category == IssueCategory.IBF]
        assert len(ibf_issues) >= 1
        assert any("Duplicate" in i.description for i in ibf_issues)

    def test_detect_file_read_error(self, temp_dir):
        non_existent = temp_dir / "nonexistent.lean"
        detector = AutomatedIssueDetector()
        issues = detector.detect_issues(non_existent)
        assert len(issues) >= 1
        assert any("Error reading file" in i.description for i in issues)

    def test_detect_directory(self, temp_dir):
        (temp_dir / "a.lean").write_text("def foo : Nat := 0\n")
        (temp_dir / "b.lean").write_text("-- only comments\n")

        detector = AutomatedIssueDetector(DetectionConfig(
            detect_usp=False, detect_isr=False, detect_ibf=False, detect_lcf=False,
        ))
        issues = detector.detect_directory(temp_dir)
        assert len(issues) >= 1

    def test_detect_cross_file_inconsistencies(self, temp_dir):
        spec_dir = temp_dir / "TestSpec"
        spec_dir.mkdir()
        (spec_dir / "Spec.lean").write_text("def MyDef : Nat := 0\n")
        (spec_dir / "Examples.lean").write_text("example : True := trivial\n")
        (spec_dir / "Lemmas.lean").write_text("lemma test : True := trivial\n")

        detector = AutomatedIssueDetector()
        issues = detector.detect_cross_file_inconsistencies(spec_dir)
        assert isinstance(issues, list)

    def test_detect_cross_file_missing_examples_references(self, temp_dir):
        spec_dir = temp_dir / "TestSpec"
        spec_dir.mkdir()
        (spec_dir / "Spec.lean").write_text("def MyDef : Nat := 0\n")
        (spec_dir / "Examples.lean").write_text("#check UndefinedRef\n")

        detector = AutomatedIssueDetector()
        issues = detector.detect_cross_file_inconsistencies(spec_dir)
        ibf_issues = [i for i in issues if i.category == IssueCategory.IBF]
        assert len(ibf_issues) >= 1

    def test_detect_cross_file_missing_lemmas_references(self, temp_dir):
        spec_dir = temp_dir / "TestSpec"
        spec_dir.mkdir()
        (spec_dir / "Spec.lean").write_text("def MyDef : Nat := 0\n")
        (spec_dir / "Lemmas.lean").write_text("#check UndefinedRef\n")

        detector = AutomatedIssueDetector()
        issues = detector.detect_cross_file_inconsistencies(spec_dir)
        ibf_issues = [i for i in issues if i.category == IssueCategory.IBF]
        assert len(ibf_issues) >= 1

    def test_extract_definitions(self):
        detector = AutomatedIssueDetector()
        content = "def foo : Nat := 0\nstructure Bar where\n  x : Nat\ninductive Baz\n  | a\n  | b\nclass MyClass where\n"
        defs = detector._extract_definitions(content)
        assert "foo" in defs
        assert "Bar" in defs
        assert "Baz" in defs
        assert "MyClass" in defs

    def test_extract_examples(self):
        detector = AutomatedIssueDetector()
        content = "example : ex1_trivial := trivial\ntheorem thm1 : 1 + 1 = 2 := rfl\nlemma lem1 : True := trivial\n"
        examples = detector._extract_examples(content)
        assert "ex1_trivial" in examples
        assert "thm1" in examples
        assert "lem1" in examples

    def test_extract_lemmas(self):
        detector = AutomatedIssueDetector()
        content = "lemma lem1 : True := trivial\nlemma lem2 : False := absurd\n"
        lemmas = detector._extract_lemmas(content)
        assert "lem1" in lemmas
        assert "lem2" in lemmas

    def test_extract_references(self):
        detector = AutomatedIssueDetector()
        content = "def foo : Nat := 0\n#check Bar\n#eval Baz"
        refs = detector._extract_references(content)
        assert "Bar" in refs
        assert "Baz" in refs

    def test_get_statistics(self):
        detector = AutomatedIssueDetector()
        issues = [
            Issue(
                issue_id=IssueId(IssueCategory.USP, 1),
                category=IssueCategory.USP,
                severity=IssueSeverity.MEDIUM,
                spec_name="S",
                file_path=Path("f"),
            ),
            Issue(
                issue_id=IssueId(IssueCategory.LCF, 1),
                category=IssueCategory.LCF,
                severity=IssueSeverity.CRITICAL,
                spec_name="S",
                file_path=Path("f"),
            ),
        ]
        stats = detector.get_statistics(issues)
        assert stats["total_issues"] == 2
        assert stats["USP_count"] == 1
        assert stats["LCF_count"] == 1
        assert stats["CRITICAL_count"] == 1
        assert stats["MEDIUM_count"] == 1
        assert stats["HIGH_count"] == 0

    def test_skip_comments_usp(self, temp_dir):
        content = "-- this should be appropriate\n/- this is a block comment -/\ndef foo : Nat := 0\n"
        lean_file = temp_dir / "Spec.lean"
        lean_file.write_text(content)

        detector = AutomatedIssueDetector(DetectionConfig(
            detect_isr=False, detect_mel=False, detect_ibf=False, detect_lcf=False,
        ))
        issues = detector.detect_issues(lean_file)
        usp_issues = [i for i in issues if i.category == IssueCategory.USP]
        assert len(usp_issues) == 0

    def test_no_issues_clean_file(self, temp_dir):
        content = "def foo : Nat := 0\ndef bar : Nat := 1\ntheorem baz : True := trivial\n"
        lean_file = temp_dir / "Spec.lean"
        lean_file.write_text(content)

        detector = AutomatedIssueDetector(DetectionConfig(
            detect_usp=False, detect_isr=False, detect_ibf=False, detect_lcf=False,
        ))
        issues = detector.detect_issues(lean_file)
        mel_issues = [i for i in issues if i.category == IssueCategory.MEL]
        assert len(mel_issues) == 0
