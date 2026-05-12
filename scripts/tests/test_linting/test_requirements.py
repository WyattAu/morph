"""Tests for EARSValidationRule."""

from pathlib import Path

from spec_tools.linting.rules.requirements import EARSValidationRule
from spec_tools.models import Severity


class TestEARSValidationRule:
    def test_init(self):
        rule = EARSValidationRule()
        assert rule.description == "Validates requirements against EARS pattern"

    def test_valid_requirement(self):
        rule = EARSValidationRule()
        content = "REQ-001: The system shall provide authentication. Priority: High Verification Method: Test\n"
        lines = content.split("\n")
        errors = rule.check(content, lines, Path("test.md"))
        assert len(errors) == 0

    def test_duplicate_requirement_ids(self):
        rule = EARSValidationRule()
        content = (
            "REQ-001: The system shall do X. Priority: High Verification Method: Test\n"
            "REQ-001: The system shall do Y. Priority: High Verification Method: Test\n"
        )
        lines = content.split("\n")
        errors = rule.check(content, lines, Path("test.md"))
        dup_errors = [e for e in errors if "Duplicate" in e.message]
        assert len(dup_errors) == 1
        assert "REQ-001" in dup_errors[0].message

    def test_invalid_requirement_id_never_extracted(self):
        rule = EARSValidationRule()
        content = "BAD-ID: The system shall do X.\n"
        lines = content.split("\n")
        errors = rule.check(content, lines, Path("test.md"))
        assert len(errors) == 0  # non-matching pattern is not extracted

    def test_valid_req_id_always_passes(self):
        rule = EARSValidationRule()
        content = "REQ-001: The system shall do X.\n"
        lines = content.split("\n")
        errors = rule.check(content, lines, Path("test.md"))
        id_errors = [e for e in errors if "Invalid requirement ID" in e.message]
        assert len(id_errors) == 0

    def test_missing_ears_pattern(self):
        rule = EARSValidationRule()
        content = "REQ-001: The system does something.\n"
        lines = content.split("\n")
        errors = rule.check(content, lines, Path("test.md"))
        ears_errors = [e for e in errors if "EARS pattern" in e.message]
        assert len(ears_errors) == 1
        assert ears_errors[0].severity == Severity.WARNING

    def test_missing_priority(self):
        rule = EARSValidationRule()
        content = "REQ-001: The system shall do X. Verification Method: Test\n"
        lines = content.split("\n")
        errors = rule.check(content, lines, Path("test.md"))
        priority_errors = [e for e in errors if "Priority" in e.message]
        assert len(priority_errors) == 1
        assert priority_errors[0].severity == Severity.WARNING

    def test_missing_verification_method(self):
        rule = EARSValidationRule()
        content = "REQ-001: The system shall do X. Priority: High\n"
        lines = content.split("\n")
        errors = rule.check(content, lines, Path("test.md"))
        vm_errors = [e for e in errors if "Verification Method" in e.message]
        assert len(vm_errors) == 1
        assert vm_errors[0].severity == Severity.WARNING

    def test_missing_both_priority_and_verification(self):
        rule = EARSValidationRule()
        content = "REQ-001: The system shall do X.\n"
        lines = content.split("\n")
        errors = rule.check(content, lines, Path("test.md"))
        assert len(errors) == 2

    def test_ears_when_pattern(self):
        rule = EARSValidationRule()
        content = "REQ-001: The system shall, when triggered, process data. Priority: High Verification Method: Test\n"
        lines = content.split("\n")
        errors = rule.check(content, lines, Path("test.md"))
        ears_errors = [e for e in errors if "EARS" in e.message]
        assert len(ears_errors) == 0

    def test_ears_if_pattern(self):
        rule = EARSValidationRule()
        content = "REQ-001: The system shall, if enabled, activate. Priority: High Verification Method: Test\n"
        lines = content.split("\n")
        errors = rule.check(content, lines, Path("test.md"))
        ears_errors = [e for e in errors if "EARS" in e.message]
        assert len(ears_errors) == 0

    def test_ears_where_pattern(self):
        rule = EARSValidationRule()
        content = "REQ-001: The system shall, where configured, start. Priority: High Verification Method: Test\n"
        lines = content.split("\n")
        errors = rule.check(content, lines, Path("test.md"))
        ears_errors = [e for e in errors if "EARS" in e.message]
        assert len(ears_errors) == 0

    def test_no_requirements(self):
        rule = EARSValidationRule()
        content = "# Title\n\nJust text, no requirements.\n"
        lines = content.split("\n")
        errors = rule.check(content, lines, Path("test.md"))
        assert len(errors) == 0

    def test_find_duplicates(self):
        rule = EARSValidationRule()
        result = rule._find_duplicates(["a", "b", "a", "c", "b", "b"])
        assert result == {"a", "b"}

    def test_find_duplicates_empty(self):
        rule = EARSValidationRule()
        result = rule._find_duplicates([])
        assert result == set()

    def test_find_duplicates_no_dupes(self):
        rule = EARSValidationRule()
        result = rule._find_duplicates(["a", "b", "c"])
        assert result == set()

    def test_extract_requirements(self):
        rule = EARSValidationRule()
        lines = [
            "REQ-001: The system shall do X",
            "Some random text",
            "REQ-002: The system shall do Y",
        ]
        reqs = rule._extract_requirements(lines)
        assert len(reqs) == 2
        assert reqs[0]["id"] == "REQ-001"
        assert reqs[1]["id"] == "REQ-002"
        assert reqs[0]["line_number"] == 1

    def test_long_requirement_text_truncated_in_context(self):
        rule = EARSValidationRule()
        long_text = "X" * 100
        content = f"REQ-001: {long_text}\n"
        lines = content.split("\n")
        errors = rule.check(content, lines, Path("test.md"))
        ears_errors = [e for e in errors if "EARS" in e.message]
        assert len(ears_errors) == 1
        assert "..." in ears_errors[0].context

    def test_duplicate_error_details(self):
        rule = EARSValidationRule()
        content = (
            "REQ-001: The system shall do X. Priority: High Verification Method: Test\n"
            "REQ-001: The system shall do X. Priority: High Verification Method: Test\n"
        )
        lines = content.split("\n")
        errors = rule.check(content, lines, Path("test.md"))
        dup_errors = [e for e in errors if "Duplicate" in e.message]
        assert dup_errors[0].severity == Severity.ERROR
        assert dup_errors[0].rule_id == "ears-validation"
        assert dup_errors[0].suggestion is not None
