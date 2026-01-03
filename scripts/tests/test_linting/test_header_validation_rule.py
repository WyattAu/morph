"""
Unit tests for HeaderValidationRule.
"""

from pathlib import Path

from spec_tools.linting.rules.header import HeaderValidationRule
from spec_tools.models import Severity


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
        rule = HeaderValidationRule()
        content = """Title: Sample Specification
Version: 1.0.0
Status: Draft
Author: John Doe
Last Modified: 2024-01-01

# Content
"""
        lines = content.split("\n")
        errors = rule.check(content, lines, Path("test.md"))
        assert len(errors) == 0

    def test_check_missing_title(self):
        """Test check() reports missing Title field."""
        rule = HeaderValidationRule()
        content = """Version: 1.0.0
Status: Draft
Author: John Doe
Last Modified: 2024-01-01

# Content
"""
        lines = content.split("\n")
        errors = rule.check(content, lines, Path("test.md"))
        assert len(errors) == 1
        assert errors[0].severity == Severity.ERROR
        assert errors[0].rule_id == "header-validation"
        assert "Missing required header field: Title" in errors[0].message

    def test_check_missing_version(self):
        """Test check() reports missing Version field."""
        rule = HeaderValidationRule()
        content = """Title: Sample Specification
Status: Draft
Author: John Doe
Last Modified: 2024-01-01

# Content
"""
        lines = content.split("\n")
        errors = rule.check(content, lines, Path("test.md"))
        assert len(errors) == 1
        assert "Missing required header field: Version" in errors[0].message

    def test_check_missing_status(self):
        """Test check() reports missing Status field."""
        rule = HeaderValidationRule()
        content = """Title: Sample Specification
Version: 1.0.0
Author: John Doe
Last Modified: 2024-01-01

# Content
"""
        lines = content.split("\n")
        errors = rule.check(content, lines, Path("test.md"))
        assert len(errors) == 1
        assert "Missing required header field: Status" in errors[0].message

    def test_check_missing_author(self):
        """Test check() reports missing Author field."""
        rule = HeaderValidationRule()
        content = """Title: Sample Specification
Version: 1.0.0
Status: Draft
Last Modified: 2024-01-01

# Content
"""
        lines = content.split("\n")
        errors = rule.check(content, lines, Path("test.md"))
        assert len(errors) == 1
        assert "Missing required header field: Author" in errors[0].message

    def test_check_missing_last_modified(self):
        """Test check() reports missing Last Modified field."""
        rule = HeaderValidationRule()
        content = """Title: Sample Specification
Version: 1.0.0
Status: Draft
Author: John Doe

# Content
"""
        lines = content.split("\n")
        errors = rule.check(content, lines, Path("test.md"))
        assert len(errors) == 1
        assert "Missing required header field: Last Modified" in errors[0].message

    def test_check_multiple_missing_fields(self):
        """Test check() reports multiple missing fields."""
        rule = HeaderValidationRule()
        content = """Title: Sample Specification

# Content
"""
        lines = content.split("\n")
        errors = rule.check(content, lines, Path("test.md"))
        assert len(errors) == 4

    def test_check_invalid_version_format(self):
        """Test check() reports invalid version format."""
        rule = HeaderValidationRule()
        content = """Title: Sample Specification
Version: 1.0
Status: Draft
Author: John Doe
Last Modified: 2024-01-01

# Content
"""
        lines = content.split("\n")
        errors = rule.check(content, lines, Path("test.md"))
        assert len(errors) == 1
        assert "Invalid version format" in errors[0].message
        assert "SemVer" in errors[0].message

    def test_check_valid_version_formats(self):
        """Test check() accepts valid version formats."""
        rule = HeaderValidationRule()
        for version in ["1.0.0", "2.3.1", "10.20.30"]:
            content = f"""Title: Sample Specification
Version: {version}
Status: Draft
Author: John Doe
Last Modified: 2024-01-01

# Content
"""
            lines = content.split("\n")
            errors = rule.check(content, lines, Path("test.md"))
            version_errors = [e for e in errors if "version" in e.message.lower()]
            assert len(version_errors) == 0

    def test_check_invalid_status(self):
        """Test check() reports invalid status."""
        rule = HeaderValidationRule()
        content = """Title: Sample Specification
Version: 1.0.0
Status: Invalid
Author: John Doe
Last Modified: 2024-01-01

# Content
"""
        lines = content.split("\n")
        errors = rule.check(content, lines, Path("test.md"))
        assert len(errors) == 1
        assert "Invalid status" in errors[0].message

    def test_check_valid_statuses(self):
        """Test check() accepts valid status values."""
        rule = HeaderValidationRule()
        for status in ["Draft", "Review", "Approved", "Deprecated"]:
            content = f"""Title: Sample Specification
Version: 1.0.0
Status: {status}
Author: John Doe
Last Modified: 2024-01-01

# Content
"""
            lines = content.split("\n")
            errors = rule.check(content, lines, Path("test.md"))
            status_errors = [e for e in errors if "status" in e.message.lower()]
            assert len(status_errors) == 0

    def test_check_file_path_mismatch(self):
        """Test check() reports file path mismatch."""
        rule = HeaderValidationRule()
        content = """Title: Sample Specification
Version: 1.0.0
Status: Draft
Author: John Doe
Last Modified: 2024-01-01
File: wrong_name.md

# Content
"""
        lines = content.split("\n")
        errors = rule.check(content, lines, Path("test.md"))
        assert len(errors) == 1
        assert "does not match actual filename" in errors[0].message

    def test_check_file_path_match(self):
        """Test check() accepts matching file path."""
        rule = HeaderValidationRule()
        content = """Title: Sample Specification
Version: 1.0.0
Status: Draft
Author: John Doe
Last Modified: 2024-01-01
File: test.md

# Content
"""
        lines = content.split("\n")
        errors = rule.check(content, lines, Path("test.md"))
        file_errors = [e for e in errors if "file" in e.message.lower()]
        assert len(file_errors) == 0

    def test_check_multiple_errors(self):
        """Test check() reports multiple errors."""
        rule = HeaderValidationRule()
        content = """Title: Sample Specification
Version: 1.0
Status: Invalid
Author: John Doe
Last Modified: 2024-01-01
File: wrong.md

# Content
"""
        lines = content.split("\n")
        errors = rule.check(content, lines, Path("test.md"))
        assert len(errors) == 3

    def test_extract_header_fields(self):
        """Test _extract_header_fields() extracts fields correctly."""
        rule = HeaderValidationRule()
        lines = [
            "Title: Sample Specification",
            "Version: 1.0.0",
            "Status: Draft",
            "Author: John Doe",
            "Last Modified: 2024-01-01",
            "",
            "# Content",
        ]
        fields = rule._extract_header_fields(lines)
        assert fields["Title"] == "Sample Specification"
        assert fields["Version"] == "1.0.0"
        assert fields["Status"] == "Draft"
        assert fields["Author"] == "John Doe"
        assert fields["Last Modified"] == "2024-01-01"

    def test_extract_header_fields_stops_at_empty_line(self):
        """Test _extract_header_fields() stops at empty line."""
        rule = HeaderValidationRule()
        lines = [
            "Title: Sample Specification",
            "Version: 1.0.0",
            "",
            "Status: Draft",
        ]
        fields = rule._extract_header_fields(lines)
        assert "Title" in fields
        assert "Version" in fields
        assert "Status" not in fields

    def test_extract_header_fields_stops_at_heading(self):
        """Test _extract_header_fields() stops at heading."""
        rule = HeaderValidationRule()
        lines = [
            "Title: Sample Specification",
            "Version: 1.0.0",
            "# Content",
            "Status: Draft",
        ]
        fields = rule._extract_header_fields(lines)
        assert "Title" in fields
        assert "Version" in fields
        assert "Status" not in fields

    def test_find_line_number(self):
        """Test _find_line_number() finds correct line."""
        rule = HeaderValidationRule()
        lines = [
            "Title: Sample Specification",
            "Version: 1.0.0",
            "Status: Draft",
        ]
        line_num = rule._find_line_number(lines, "Version")
        assert line_num == 2

    def test_find_line_number_not_found(self):
        """Test _find_line_number() returns 1 when not found."""
        rule = HeaderValidationRule()
        lines = [
            "Title: Sample Specification",
            "Version: 1.0.0",
        ]
        line_num = rule._find_line_number(lines, "Status")
        assert line_num == 1

    def test_check_suggestion(self):
        """Test check() provides helpful suggestions."""
        rule = HeaderValidationRule()
        content = """Title: Sample Specification

# Content
"""
        lines = content.split("\n")
        errors = rule.check(content, lines, Path("test.md"))
        assert len(errors) > 0
        for error in errors:
            assert error.suggestion is not None
            assert error.suggestion != ""

    def test_check_context(self):
        """Test check() provides context for errors."""
        rule = HeaderValidationRule()
        content = """Title: Sample Specification
Version: 1.0

# Content
"""
        lines = content.split("\n")
        errors = rule.check(content, lines, Path("test.md"))
        version_errors = [e for e in errors if "version" in e.message.lower()]
        assert len(version_errors) == 1
        assert version_errors[0].context is not None
