"""Tests for SectionStructureRule."""

from pathlib import Path

from spec_tools.linting.rules.sections import SectionStructureRule

FULL_SPEC = """# Sample Specification

- Version: 1.0.0
- Status: Draft
- Author: Jane Doe
- Last Modified: 2024-01-01

---

## 1. Introduction

Purpose of this spec.

## 2. Formal Definitions

Key terms.

## 3. Requirements

What must hold.
"""


def check(content, filename="test.md"):
    rule = SectionStructureRule()
    return rule.check(content, content.split("\n"), Path(filename))


class TestSectionStructureRule:
    def test_init(self):
        rule = SectionStructureRule()
        assert "section" in rule.description.lower()

    def test_full_spec_passes(self):
        assert check(FULL_SPEC) == []

    def test_unnumbered_mandatory_sections_pass(self):
        content = "# Spec\n\n## Purpose and Scope\n\n## Definitions\n\n## Requirements\n"
        assert check(content) == []

    def test_missing_requirements_flagged(self):
        content = "# Spec\n\n## 1. Introduction\n\n## 2. Formal Definitions\n"
        errors = check(content)
        assert len(errors) == 1
        assert "requirements" in errors[0].message

    def test_future_research_exempt(self):
        content = "# Sketch\n\nSome exploratory text.\n"
        errors = check(content, filename="spec/tooling/_future_research/sketch_spec.md")
        assert [e for e in errors if "Mandatory" in e.message or "mandatory" in e.message] == []

    def test_numbering_decrease_warns(self):
        content = (
            "# Spec\n\n## 1. Introduction\n\n## 2. Formal Definitions\n\n"
            "## 2.7 Later Addition\n\n## 2.2 Earlier Topic\n\n## 3. Requirements\n"
        )
        errors = check(content)
        assert any("numbering decreased" in e.message.lower() for e in errors)

    def test_normalize_heading(self):
        rule = SectionStructureRule()
        assert rule._normalize_heading("1. Purpose and Scope") == "purpose and scope"
        assert rule._normalize_heading("10. Change Log") == "change log"
