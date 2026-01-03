"""
Unit tests for TrailingWhitespaceRule.
"""

from pathlib import Path

from spec_tools.formatting.rules.whitespace import TrailingWhitespaceRule
from spec_tools.models import Severity


class TestTrailingWhitespaceRule:
    """Test cases for TrailingWhitespaceRule."""

    def test_init_default(self):
        """Test TrailingWhitespaceRule initialization with default enabled."""
        rule = TrailingWhitespaceRule()
        assert rule.enabled is True

    def test_init_disabled(self):
        """Test TrailingWhitespaceRule initialization with disabled."""
        rule = TrailingWhitespaceRule(enabled=False)
        assert rule.enabled is False

    def test_apply_no_trailing_whitespace(self):
        """Test apply() with content that has no trailing whitespace."""
        rule = TrailingWhitespaceRule()
        content = "Line 1\nLine 2\nLine 3"
        result = rule.apply(content)
        assert result == content

    def test_apply_trailing_spaces(self):
        """Test apply() removes trailing spaces."""
        rule = TrailingWhitespaceRule()
        content = "Line 1   \nLine 2  \nLine 3 "
        result = rule.apply(content)
        assert result == "Line 1\nLine 2\nLine 3"

    def test_apply_trailing_tabs(self):
        """Test apply() removes trailing tabs."""
        rule = TrailingWhitespaceRule()
        content = "Line 1\t\t\nLine 2\t\nLine 3"
        result = rule.apply(content)
        assert result == "Line 1\nLine 2\nLine 3"

    def test_apply_mixed_whitespace(self):
        """Test apply() removes mixed trailing whitespace."""
        rule = TrailingWhitespaceRule()
        content = "Line 1 \t \nLine 2\t \nLine 3"
        result = rule.apply(content)
        assert result == "Line 1\nLine 2\nLine 3"

    def test_apply_empty_lines(self):
        """Test apply() handles empty lines correctly."""
        rule = TrailingWhitespaceRule()
        content = "Line 1\n   \nLine 2\n\t\t\nLine 3"
        result = rule.apply(content)
        assert result == "Line 1\n\nLine 2\n\nLine 3"

    def test_apply_disabled(self):
        """Test apply() does nothing when disabled."""
        rule = TrailingWhitespaceRule(enabled=False)
        content = "Line 1   \nLine 2  \nLine 3 "
        result = rule.apply(content)
        assert result == content

    def test_apply_empty_content(self):
        """Test apply() with empty content."""
        rule = TrailingWhitespaceRule()
        content = ""
        result = rule.apply(content)
        assert result == ""

    def test_apply_single_line(self):
        """Test apply() with a single line."""
        rule = TrailingWhitespaceRule()
        content = "Single line with trailing spaces   "
        result = rule.apply(content)
        assert result == "Single line with trailing spaces"

    def test_apply_preserves_internal_whitespace(self):
        """Test apply() preserves internal whitespace."""
        rule = TrailingWhitespaceRule()
        content = "Line  with  internal  whitespace   "
        result = rule.apply(content)
        assert result == "Line  with  internal  whitespace"

    def test_check_no_violations(self):
        """Test check() with content that has no violations."""
        rule = TrailingWhitespaceRule()
        content = "Line 1\nLine 2\nLine 3"
        errors = rule.check(content, Path("test.md"))
        assert len(errors) == 0

    def test_check_trailing_spaces(self):
        """Test check() reports trailing spaces."""
        rule = TrailingWhitespaceRule()
        content = "Line 1   \nLine 2\nLine 3"
        errors = rule.check(content, Path("test.md"))
        assert len(errors) == 1
        assert errors[0].severity == Severity.WARNING
        assert errors[0].rule_id == "trailing-whitespace"
        assert "trailing whitespace" in errors[0].message

    def test_check_multiple_violations(self):
        """Test check() reports multiple violations."""
        rule = TrailingWhitespaceRule()
        content = "Line 1   \nLine 2  \nLine 3 "
        errors = rule.check(content, Path("test.md"))
        assert len(errors) == 3

    def test_check_trailing_tabs(self):
        """Test check() reports trailing tabs."""
        rule = TrailingWhitespaceRule()
        content = "Line 1\t\t\nLine 2\nLine 3"
        errors = rule.check(content, Path("test.md"))
        assert len(errors) == 1

    def test_check_mixed_whitespace(self):
        """Test check() reports mixed trailing whitespace."""
        rule = TrailingWhitespaceRule()
        content = "Line 1 \t \nLine 2\nLine 3"
        errors = rule.check(content, Path("test.md"))
        assert len(errors) == 1

    def test_check_disabled(self):
        """Test check() returns no errors when disabled."""
        rule = TrailingWhitespaceRule(enabled=False)
        content = "Line 1   \nLine 2  \nLine 3 "
        errors = rule.check(content, Path("test.md"))
        assert len(errors) == 0

    def test_check_empty_content(self):
        """Test check() with empty content."""
        rule = TrailingWhitespaceRule()
        content = ""
        errors = rule.check(content, Path("test.md"))
        assert len(errors) == 0

    def test_check_line_number(self):
        """Test check() reports correct line numbers."""
        rule = TrailingWhitespaceRule()
        content = "Line 1\nLine 2   \nLine 3"
        errors = rule.check(content, Path("test.md"))
        assert len(errors) == 1
        assert errors[0].line_number == 2

    def test_check_column_number(self):
        """Test check() reports correct column numbers."""
        rule = TrailingWhitespaceRule()
        content = "Line 2   "
        errors = rule.check(content, Path("test.md"))
        assert len(errors) == 1
        assert errors[0].column_number == 7

    def test_check_suggestion(self):
        """Test check() provides helpful suggestions."""
        rule = TrailingWhitespaceRule()
        content = "Line 2   "
        errors = rule.check(content, Path("test.md"))
        assert len(errors) == 1
        assert errors[0].suggestion is not None
        assert "Remove trailing whitespace" in errors[0].suggestion

    def test_check_context(self):
        """Test check() provides context for violations."""
        rule = TrailingWhitespaceRule()
        content = "Line 2   "
        errors = rule.check(content, Path("test.md"))
        assert len(errors) == 1
        assert errors[0].context is not None

    def test_check_trailing_char_count(self):
        """Test check() reports correct number of trailing characters."""
        rule = TrailingWhitespaceRule()
        content = "Line 2   "
        errors = rule.check(content, Path("test.md"))
        assert len(errors) == 1
        assert "3 trailing whitespace" in errors[0].message
