"""
Unit tests for ListNormalizationRule.
"""

from pathlib import Path

from spec_tools.formatting.rules.lists import ListNormalizationRule
from spec_tools.models import Severity


class TestListNormalizationRule:
    """Test cases for ListNormalizationRule."""

    def test_init_default(self):
        """Test ListNormalizationRule initialization with default enabled."""
        rule = ListNormalizationRule()
        assert rule.enabled is True

    def test_init_disabled(self):
        """Test ListNormalizationRule initialization with disabled."""
        rule = ListNormalizationRule(enabled=False)
        assert rule.enabled is False

    def test_apply_correct_formatting(self):
        """Test apply() with correctly formatted lists."""
        rule = ListNormalizationRule()
        content = "- Item 1\n- Item 2\n- Item 3"
        result = rule.apply(content)
        assert result == content

    def test_apply_asterisk_bullets(self):
        """Test apply() converts * bullets to -."""
        rule = ListNormalizationRule()
        content = "* Item 1\n* Item 2\n* Item 3"
        result = rule.apply(content)
        assert result == "- Item 1\n- Item 2\n- Item 3"

    def test_apply_plus_bullets(self):
        """Test apply() converts + bullets to -."""
        rule = ListNormalizationRule()
        content = "+ Item 1\n+ Item 2\n+ Item 3"
        result = rule.apply(content)
        assert result == "- Item 1\n- Item 2\n- Item 3"

    def test_apply_missing_space(self):
        """Test apply() adds space after bullet when missing."""
        rule = ListNormalizationRule()
        content = "-Item 1\n-Item 2\n-Item 3"
        result = rule.apply(content)
        assert result == "- Item 1\n- Item 2\n- Item 3"

    def test_apply_multiple_spaces(self):
        """Test apply() reduces multiple spaces to one."""
        rule = ListNormalizationRule()
        content = "-  Item 1\n-   Item 2\n-    Item 3"
        result = rule.apply(content)
        assert result == "- Item 1\n- Item 2\n- Item 3"

    def test_apply_mixed_bullets(self):
        """Test apply() normalizes mixed bullet types."""
        rule = ListNormalizationRule()
        content = "* Item 1\n- Item 2\n+ Item 3"
        result = rule.apply(content)
        assert result == "- Item 1\n- Item 2\n- Item 3"

    def test_apply_nested_lists(self):
        """Test apply() preserves nested list indentation."""
        rule = ListNormalizationRule()
        content = "- Item 1\n  - Nested item\n- Item 2"
        result = rule.apply(content)
        assert result == "- Item 1\n  - Nested item\n- Item 2"

    def test_apply_disabled(self):
        """Test apply() does nothing when disabled."""
        rule = ListNormalizationRule(enabled=False)
        content = "* Item 1\n+ Item 2\n-Item 3"
        result = rule.apply(content)
        assert result == content

    def test_apply_empty_content(self):
        """Test apply() with empty content."""
        rule = ListNormalizationRule()
        content = ""
        result = rule.apply(content)
        assert result == ""

    def test_apply_non_list_lines(self):
        """Test apply() preserves non-list lines."""
        rule = ListNormalizationRule()
        content = "Regular text\n* Item 1\nMore text\n- Item 2"
        result = rule.apply(content)
        assert result == "Regular text\n- Item 1\nMore text\n- Item 2"

    def test_apply_preserves_item_text(self):
        """Test apply() preserves list item text content."""
        rule = ListNormalizationRule()
        content = "*  This is a list item with text"
        result = rule.apply(content)
        assert result == "- This is a list item with text"

    def test_check_no_violations(self):
        """Test check() with content that has no violations."""
        rule = ListNormalizationRule()
        content = "- Item 1\n- Item 2\n- Item 3"
        errors = rule.check(content, Path("test.md"))
        assert len(errors) == 0

    def test_check_asterisk_bullets(self):
        """Test check() reports * bullet violations."""
        rule = ListNormalizationRule()
        content = "* Item 1\n- Item 2"
        errors = rule.check(content, Path("test.md"))
        assert len(errors) == 1
        assert errors[0].severity == Severity.WARNING
        assert errors[0].rule_id == "list-normalization"
        assert "uses '*'" in errors[0].message

    def test_check_plus_bullets(self):
        """Test check() reports + bullet violations."""
        rule = ListNormalizationRule()
        content = "+ Item 1\n- Item 2"
        errors = rule.check(content, Path("test.md"))
        assert len(errors) == 1
        assert "uses '+'" in errors[0].message

    def test_check_missing_space(self):
        """Test check() reports missing space violations."""
        rule = ListNormalizationRule()
        content = "-Item 1\n- Item 2"
        errors = rule.check(content, Path("test.md"))
        assert len(errors) == 1
        assert "missing space" in errors[0].message

    def test_check_multiple_spaces(self):
        """Test check() reports multiple space violations."""
        rule = ListNormalizationRule()
        content = "-  Item 1\n- Item 2"
        errors = rule.check(content, Path("test.md"))
        assert len(errors) == 1
        assert "spaces after" in errors[0].message

    def test_check_multiple_violations(self):
        """Test check() reports multiple violations."""
        rule = ListNormalizationRule()
        content = "* Item 1\n+ Item 2\n-Item 3"
        errors = rule.check(content, Path("test.md"))
        assert len(errors) == 3

    def test_check_disabled(self):
        """Test check() returns no errors when disabled."""
        rule = ListNormalizationRule(enabled=False)
        content = "* Item 1\n+ Item 2\n-Item 3"
        errors = rule.check(content, Path("test.md"))
        assert len(errors) == 0

    def test_check_empty_content(self):
        """Test check() with empty content."""
        rule = ListNormalizationRule()
        content = ""
        errors = rule.check(content, Path("test.md"))
        assert len(errors) == 0

    def test_check_line_number(self):
        """Test check() reports correct line numbers."""
        rule = ListNormalizationRule()
        content = "- Item 1\n* Item 2\n- Item 3"
        errors = rule.check(content, Path("test.md"))
        assert len(errors) == 1
        assert errors[0].line_number == 2

    def test_check_column_number_bullet(self):
        """Test check() reports correct column numbers for bullet violations."""
        rule = ListNormalizationRule()
        content = "* Item 1"
        errors = rule.check(content, Path("test.md"))
        assert len(errors) == 1
        assert errors[0].column_number == 1

    def test_check_column_number_space(self):
        """Test check() reports correct column numbers for space violations."""
        rule = ListNormalizationRule()
        content = "-Item 1"
        errors = rule.check(content, Path("test.md"))
        assert len(errors) == 1
        assert errors[0].column_number == 2

    def test_check_suggestion_bullet(self):
        """Test check() provides suggestion for bullet violations."""
        rule = ListNormalizationRule()
        content = "* Item 1"
        errors = rule.check(content, Path("test.md"))
        assert len(errors) == 1
        assert errors[0].suggestion is not None
        assert "Use '-'" in errors[0].suggestion

    def test_check_suggestion_space(self):
        """Test check() provides suggestion for space violations."""
        rule = ListNormalizationRule()
        content = "-Item 1"
        errors = rule.check(content, Path("test.md"))
        assert len(errors) == 1
        assert errors[0].suggestion is not None
        assert "Add a space" in errors[0].suggestion

    def test_check_context(self):
        """Test check() provides context for violations."""
        rule = ListNormalizationRule()
        content = "* Item 1"
        errors = rule.check(content, Path("test.md"))
        assert len(errors) == 1
        assert errors[0].context is not None

    def test_check_nested_lists(self):
        """Test check() works with nested lists."""
        rule = ListNormalizationRule()
        content = "- Item 1\n  * Nested item\n- Item 2"
        errors = rule.check(content, Path("test.md"))
        assert len(errors) == 1
