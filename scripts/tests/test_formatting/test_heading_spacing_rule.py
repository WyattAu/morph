"""
Unit tests for HeadingSpacingRule.
"""

from pathlib import Path

from spec_tools.formatting.rules.headings import HeadingSpacingRule
from spec_tools.models import Severity


class TestHeadingSpacingRule:
    """Test cases for HeadingSpacingRule."""

    def test_init_default(self):
        """Test HeadingSpacingRule initialization with default enabled."""
        rule = HeadingSpacingRule()
        assert rule.enabled is True

    def test_init_disabled(self):
        """Test HeadingSpacingRule initialization with disabled."""
        rule = HeadingSpacingRule(enabled=False)
        assert rule.enabled is False

    def test_apply_correct_spacing(self):
        """Test apply() with correctly spaced headings."""
        rule = HeadingSpacingRule()
        content = "# Heading 1\n## Heading 2\n### Heading 3"
        result = rule.apply(content)
        assert result == content

    def test_apply_missing_space(self):
        """Test apply() adds space after # when missing."""
        rule = HeadingSpacingRule()
        content = "#Heading 1\n##Heading 2\n###Heading 3"
        result = rule.apply(content)
        assert result == "# Heading 1\n## Heading 2\n### Heading 3"

    def test_apply_multiple_spaces(self):
        """Test apply() reduces multiple spaces to one."""
        rule = HeadingSpacingRule()
        content = "#  Heading 1\n##   Heading 2\n###    Heading 3"
        result = rule.apply(content)
        assert result == "# Heading 1\n## Heading 2\n### Heading 3"

    def test_apply_mixed_spacing(self):
        """Test apply() handles mixed spacing issues."""
        rule = HeadingSpacingRule()
        content = "#Heading 1\n##  Heading 2\n###Heading 3"
        result = rule.apply(content)
        assert result == "# Heading 1\n## Heading 2\n### Heading 3"

    def test_apply_disabled(self):
        """Test apply() does nothing when disabled."""
        rule = HeadingSpacingRule(enabled=False)
        content = "#Heading 1\n##  Heading 2"
        result = rule.apply(content)
        assert result == content

    def test_apply_empty_content(self):
        """Test apply() with empty content."""
        rule = HeadingSpacingRule()
        content = ""
        result = rule.apply(content)
        assert result == ""

    def test_apply_non_heading_lines(self):
        """Test apply() preserves non-heading lines."""
        rule = HeadingSpacingRule()
        content = "#Heading 1\nRegular text\n##Heading 2\nMore text"
        result = rule.apply(content)
        assert result == "# Heading 1\nRegular text\n## Heading 2\nMore text"

    def test_apply_preserves_heading_text(self):
        """Test apply() preserves heading text content."""
        rule = HeadingSpacingRule()
        content = "#  This is a heading with text"
        result = rule.apply(content)
        assert result == "# This is a heading with text"

    def test_check_no_violations(self):
        """Test check() with content that has no violations."""
        rule = HeadingSpacingRule()
        content = "# Heading 1\n## Heading 2\n### Heading 3"
        errors = rule.check(content, Path("test.md"))
        assert len(errors) == 0

    def test_check_missing_space(self):
        """Test check() reports missing space after #."""
        rule = HeadingSpacingRule()
        content = "#Heading 1\n## Heading 2"
        errors = rule.check(content, Path("test.md"))
        assert len(errors) == 1
        assert errors[0].severity == Severity.WARNING
        assert errors[0].rule_id == "heading-spacing"
        assert "missing space" in errors[0].message

    def test_check_multiple_spaces(self):
        """Test check() reports multiple spaces after #."""
        rule = HeadingSpacingRule()
        content = "#  Heading 1\n## Heading 2"
        errors = rule.check(content, Path("test.md"))
        assert len(errors) == 1
        assert "spaces after" in errors[0].message

    def test_check_multiple_violations(self):
        """Test check() reports multiple violations."""
        rule = HeadingSpacingRule()
        content = "#Heading 1\n##  Heading 2\n###Heading 3"
        errors = rule.check(content, Path("test.md"))
        assert len(errors) == 3

    def test_check_disabled(self):
        """Test check() returns no errors when disabled."""
        rule = HeadingSpacingRule(enabled=False)
        content = "#Heading 1\n##  Heading 2"
        errors = rule.check(content, Path("test.md"))
        assert len(errors) == 0

    def test_check_empty_content(self):
        """Test check() with empty content."""
        rule = HeadingSpacingRule()
        content = ""
        errors = rule.check(content, Path("test.md"))
        assert len(errors) == 0

    def test_check_line_number(self):
        """Test check() reports correct line numbers."""
        rule = HeadingSpacingRule()
        content = "# Heading 1\n#Heading 2\n## Heading 3"
        errors = rule.check(content, Path("test.md"))
        assert len(errors) == 1
        assert errors[0].line_number == 2

    def test_check_column_number(self):
        """Test check() reports correct column numbers."""
        rule = HeadingSpacingRule()
        content = "#Heading 1"
        errors = rule.check(content, Path("test.md"))
        assert len(errors) == 1
        assert errors[0].column_number == 2

    def test_check_suggestion_missing_space(self):
        """Test check() provides suggestion for missing space."""
        rule = HeadingSpacingRule()
        content = "#Heading 1"
        errors = rule.check(content, Path("test.md"))
        assert len(errors) == 1
        assert errors[0].suggestion is not None
        assert "Add a space" in errors[0].suggestion

    def test_check_suggestion_multiple_spaces(self):
        """Test check() provides suggestion for multiple spaces."""
        rule = HeadingSpacingRule()
        content = "#  Heading 1"
        errors = rule.check(content, Path("test.md"))
        assert len(errors) == 1
        assert errors[0].suggestion is not None
        assert "exactly one space" in errors[0].suggestion

    def test_check_context(self):
        """Test check() provides context for violations."""
        rule = HeadingSpacingRule()
        content = "#Heading 1"
        errors = rule.check(content, Path("test.md"))
        assert len(errors) == 1
        assert errors[0].context is not None

    def test_check_all_heading_levels(self):
        """Test check() works with all heading levels."""
        rule = HeadingSpacingRule()
        content = "#H1\n##H2\n###H3\n####H4\n#####H5\n######H6"
        errors = rule.check(content, Path("test.md"))
        assert len(errors) == 6

    def test_apply_all_heading_levels(self):
        """Test apply() works with all heading levels."""
        rule = HeadingSpacingRule()
        content = "#H1\n##H2\n###H3\n####H4\n#####H5\n######H6"
        result = rule.apply(content)
        assert result == "# H1\n## H2\n### H3\n#### H4\n##### H5\n###### H6"
