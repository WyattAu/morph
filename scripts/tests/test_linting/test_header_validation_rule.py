"""
Unit tests for HeaderValidationRule.

Corpus convention under test: files start with a ``# Title`` heading
followed by a bullet metadata block (``- File:``, ``- Version:``,
``- Context:``, ``- Status:``, ``- Last Modified:``, ``- Author:``,
``- Reviewers:``), terminated by a ``---`` rule or the first section.
"""

from pathlib import Path

from spec_tools.linting.rules.header import HeaderValidationRule
from spec_tools.models import Severity

VALID_HEADER = """# Sample Specification

- File: `test.md`
- Version: 1.0.0
- Status: Draft
- Author: John Doe
- Last Modified: 2024-01-01

---

## 1. Purpose and Scope
"""


def check(content, filename="test.md"):
    rule = HeaderValidationRule()
    return rule.check(content, content.split("\n"), Path(filename))


class TestHeaderValidationRule:
    """Test cases for HeaderValidationRule."""

    def test_init(self):
        """Test HeaderValidationRule initialization."""
        rule = HeaderValidationRule()
        assert rule.description == "Validates specification file header fields"
        assert "Title" in rule._required_fields
        assert "Version" in rule._required_fields
        assert "Status" in rule._required_fields
        assert "Author" in rule._required_fields
        assert "Last Modified" in rule._required_fields

    def test_check_valid_header(self):
        """Test check() with valid header."""
        assert len(check(VALID_HEADER)) == 0

    def test_check_title_from_h1(self):
        """Test check() takes the Title from the H1 heading."""
        content = """# My Great Spec

- Version: 1.0.0
- Status: Draft
- Author: John Doe
- Last Modified: 2024-01-01

---

## 1. Purpose and Scope
"""
        errors = check(content)
        assert not [e for e in errors if "Title" in e.message]

    def test_check_emphasized_bullets(self):
        """Test check() accepts bold/italic bullet fields."""
        content = """# Sample Specification

- **Version:** 1.0.0
- **Status:** Active
- **Author:** John Doe
- **Last Modified:** 2024-01-01

---

## 1. Purpose and Scope
"""
        assert len(check(content)) == 0

    def test_check_missing_block_is_single_warning(self):
        """Test check() with no metadata block gives one advisory warning."""
        content = """# Sample Specification

## 1. Purpose and Scope
"""
        errors = check(content)
        assert len(errors) == 1
        assert errors[0].severity == Severity.WARNING
        assert "metadata header block" in errors[0].message

    def test_check_missing_title(self):
        """Test check() with no H1 and no block gives the advisory warning."""
        content = """- Version: 1.0.0
- Status: Draft
- Author: John Doe
- Last Modified: 2024-01-01

---

## 1. Purpose and Scope
"""
        errors = check(content)
        assert len(errors) == 1
        assert errors[0].severity == Severity.WARNING

    def test_check_missing_version(self):
        """Test check() reports missing Version field."""
        content = VALID_HEADER.replace("- Version: 1.0.0\n", "")
        errors = check(content)
        assert len(errors) == 1
        assert "Missing required header field: Version" in errors[0].message

    def test_check_missing_status(self):
        """Test check() reports missing Status field."""
        content = VALID_HEADER.replace("- Status: Draft\n", "")
        errors = check(content)
        assert len(errors) == 1
        assert "Missing required header field: Status" in errors[0].message

    def test_check_missing_author(self):
        """Test check() reports missing Author field."""
        content = VALID_HEADER.replace("- Author: John Doe\n", "")
        errors = check(content)
        assert len(errors) == 1
        assert "Missing required header field: Author" in errors[0].message

    def test_check_missing_last_modified(self):
        """Test check() reports missing Last Modified field."""
        content = VALID_HEADER.replace("- Last Modified: 2024-01-01\n", "")
        errors = check(content)
        assert len(errors) == 1
        assert "Missing required header field: Last Modified" in errors[0].message

    def test_check_multiple_missing_fields(self):
        """Test check() reports multiple missing fields."""
        content = """# Sample Specification

- File: `test.md`

---

## 1. Purpose and Scope
"""
        errors = check(content)
        assert len(errors) == 4

    def test_check_invalid_version_format(self):
        """Test check() reports invalid version format."""
        content = VALID_HEADER.replace("1.0.0", "1.0")
        errors = check(content)
        assert len(errors) == 1
        assert "Invalid version format" in errors[0].message
        assert "SemVer" in errors[0].message

    def test_check_valid_version_formats(self):
        """Test check() accepts valid version formats."""
        for version in ["1.0.0", "2.3.1", "10.20.30"]:
            content = VALID_HEADER.replace("1.0.0", version)
            version_errors = [e for e in check(content) if "version" in e.message.lower()]
            assert len(version_errors) == 0

    def test_check_invalid_status(self):
        """Test check() reports invalid status."""
        content = VALID_HEADER.replace("Status: Draft", "Status: Invalid")
        errors = check(content)
        assert len(errors) == 1
        assert "Invalid status" in errors[0].message

    def test_check_valid_statuses(self):
        """Test check() accepts valid status values."""
        for status in ["Draft", "Review", "Active", "Approved", "Deprecated"]:
            content = VALID_HEADER.replace("Status: Draft", f"Status: {status}")
            status_errors = [e for e in check(content) if "status" in e.message.lower()]
            assert len(status_errors) == 0

    def test_check_file_path_mismatch(self):
        """Test check() reports file path mismatch."""
        content = VALID_HEADER.replace("`test.md`", "wrong_name.md")
        errors = check(content)
        assert len(errors) == 1
        assert "does not match actual filename" in errors[0].message

    def test_check_file_path_match(self):
        """Test check() accepts matching file path."""
        file_errors = [e for e in check(VALID_HEADER) if "file" in e.message.lower()]
        assert len(file_errors) == 0

    def test_check_multiple_errors(self):
        """Test check() reports multiple errors."""
        content = """# Sample Specification

- Version: 1.0
- Status: Invalid
- Author: John Doe
- Last Modified: 2024-01-01
- File: wrong.md

---

## 1. Purpose and Scope
"""
        assert len(check(content)) == 3

    def test_extract_header_fields(self):
        """Test _extract_header_fields() extracts fields correctly."""
        rule = HeaderValidationRule()
        lines = [
            "# Sample Specification",
            "",
            "- File: `test.md`",
            "- Version: 1.0.0",
            "- Status: Draft",
            "- Author: John Doe",
            "- Last Modified: 2024-01-01",
            "",
            "---",
            "",
            "## 1. Purpose and Scope",
        ]
        fields = rule._extract_header_fields(lines)
        assert fields["Title"] == "Sample Specification"
        assert fields["Version"] == "1.0.0"
        assert fields["Status"] == "Draft"
        assert fields["Author"] == "John Doe"
        assert fields["Last Modified"] == "2024-01-01"

    def test_extract_header_fields_stops_at_rule(self):
        """Test _extract_header_fields() stops at the --- rule."""
        rule = HeaderValidationRule()
        lines = [
            "# Sample Specification",
            "",
            "- Version: 1.0.0",
            "---",
            "- Status: Draft",
        ]
        fields = rule._extract_header_fields(lines)
        assert "Version" in fields
        assert "Status" not in fields

    def test_extract_header_fields_stops_at_section(self):
        """Test _extract_header_fields() stops at the first section."""
        rule = HeaderValidationRule()
        lines = [
            "# Sample Specification",
            "",
            "- Version: 1.0.0",
            "## 1. Purpose and Scope",
            "- Status: Draft",
        ]
        fields = rule._extract_header_fields(lines)
        assert "Version" in fields
        assert "Status" not in fields

    def test_extract_header_fields_title_only_gives_no_block(self):
        """Test a title with no bullets counts as no metadata block."""
        rule = HeaderValidationRule()
        lines = [
            "# Sample Specification",
            "",
            "## 1. Purpose and Scope",
        ]
        assert rule._extract_header_fields(lines) == {}

    def test_find_line_number(self):
        """Test _find_line_number() finds correct line."""
        rule = HeaderValidationRule()
        lines = [
            "# Sample Specification",
            "",
            "- Version: 1.0.0",
            "- Status: Draft",
        ]
        line_num = rule._find_line_number(lines, "Version")
        assert line_num == 3

    def test_find_line_number_not_found(self):
        """Test _find_line_number() returns 1 when not found."""
        rule = HeaderValidationRule()
        lines = [
            "# Sample Specification",
            "",
            "- Version: 1.0.0",
        ]
        line_num = rule._find_line_number(lines, "Status")
        assert line_num == 1

    def test_check_suggestion(self):
        """Test check() provides helpful suggestions."""
        errors = check("# Sample Specification\n\n## 1. Purpose and Scope\n")
        assert len(errors) > 0
        for error in errors:
            assert error.suggestion is not None
            assert error.suggestion != ""

    def test_check_context(self):
        """Test check() provides context for errors."""
        content = VALID_HEADER.replace("1.0.0", "1.0")
        errors = check(content)
        version_errors = [e for e in errors if "version" in e.message.lower()]
        assert len(version_errors) == 1
        assert version_errors[0].context is not None

    def test_check_backticked_convention_block(self):
        """Test check() accepts the backticked convention block format."""
        content = r"""# Concurrency & Process Algebra Specification

- `File:* `concurrency\concurrency_process_algebra_spec.md`
- `Version:* 2.0.0
- `Context:* Layer 3 (Runtime Scheduler)
- `Formalism:* pi-calculus
- `Status:* Active
- Last Modified:* 2026-01-01
- `Author:* Kilo Code
- `Reviewers:* Pending

---

## 1. Purpose and Scope
"""
        errors = check(content, filename="concurrency_process_algebra_spec.md")
        assert len(errors) == 0, [e.message for e in errors]

    def test_check_file_suffix_match(self):
        """Test check() accepts repo-relative File paths."""
        content = VALID_HEADER.replace("- File: `test.md`", "- File: `spec/test.md`")
        file_errors = [e for e in check(content) if "file" in e.message.lower()]
        assert len(file_errors) == 0
