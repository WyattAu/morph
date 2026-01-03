"""
Unit tests for EmphasisNormalizationRule.
"""

from pathlib import Path

from spec_tools.formatting.rules.emphasis import EmphasisNormalizationRule
from spec_tools.models import Severity


class TestEmphasisNormalizationRule:
    """Test cases for EmphasisNormalizationRule."""

    def test_init_default(self):
        """Test EmphasisNormalizationRule initialization with default enabled."""
        rule = EmphasisNormalizationRule()
        assert rule.enabled is True

    def test_init_disabled(self):
        """Test EmphasisNormalizationRule initialization with disabled."""
        rule = EmphasisNormalizationRule(enabled=False)
        assert rule.enabled is False

    def test_apply_correct_formatting(self):
        """Test apply() with correctly formatted emphasis."""
        rule = EmphasisNormalizationRule()
        content = "*italic* and **bold** text"
        result = rule.apply(content)
        assert result == content

    def test_apply_italic_underscores(self):
        """Test apply() converts _italic_ to *italic*."""
        rule = EmphasisNormalizationRule()
        content = "_italic_ text"
        result = rule.apply(content)
        assert result == "*italic* text"

    def test_apply_bold_underscores(self):
        """Test apply() converts __bold__ to **bold**."""
        rule = EmphasisNormalizationRule()
        content = "__bold__ text"
        result = rule.apply(content)
        assert result == "**bold** text"

    def test_apply_mixed_emphasis(self):
        """Test apply() normalizes mixed emphasis markers."""
        rule = EmphasisNormalizationRule()
        content = "_italic_ and __bold__ text"
        result = rule.apply(content)
        assert result == "*italic* and **bold** text"

    def test_apply_preserves_latex_inline(self):
        """Test apply() preserves inline LaTeX math."""
        rule = EmphasisNormalizationRule()
        content = "The value is $x = \\sqrt{y^2 + z^2}$"
        result = rule.apply(content)
        assert result == content

    def test_apply_preserves_latex_block(self):
        """Test apply() preserves block LaTeX math."""
        rule = EmphasisNormalizationRule()
        content = "The equation is $$P = \\frac{1}{n} \\sum_{i=1}^{n} x_i$$"
        result = rule.apply(content)
        assert result == content

    def test_apply_underscores_in_latex(self):
        """Test apply() preserves underscores in LaTeX."""
        rule = EmphasisNormalizationRule()
        content = "The value is $x_i$ and $y_j$"
        result = rule.apply(content)
        assert result == content

    def test_apply_disabled(self):
        """Test apply() does nothing when disabled."""
        rule = EmphasisNormalizationRule(enabled=False)
        content = "_italic_ and __bold__ text"
        result = rule.apply(content)
        assert result == content

    def test_apply_empty_content(self):
        """Test apply() with empty content."""
        rule = EmphasisNormalizationRule()
        content = ""
        result = rule.apply(content)
        assert result == ""

    def test_apply_no_emphasis(self):
        """Test apply() with text that has no emphasis."""
        rule = EmphasisNormalizationRule()
        content = "Regular text with no emphasis"
        result = rule.apply(content)
        assert result == content

    def test_apply_multiple_occurrences(self):
        """Test apply() handles multiple emphasis occurrences."""
        rule = EmphasisNormalizationRule()
        content = "_italic1_ and _italic2_ and __bold1__ and __bold2__"
        result = rule.apply(content)
        assert result == "*italic1* and *italic2* and **bold1** and **bold2**"

    def test_check_no_violations(self):
        """Test check() with content that has no violations."""
        rule = EmphasisNormalizationRule()
        content = "*italic* and **bold** text"
        errors = rule.check(content, Path("test.md"))
        assert len(errors) == 0

    def test_check_italic_underscores(self):
        """Test check() reports italic underscore violations."""
        rule = EmphasisNormalizationRule()
        content = "_italic_ text"
        errors = rule.check(content, Path("test.md"))
        assert len(errors) == 1
        assert errors[0].severity == Severity.INFO
        assert errors[0].rule_id == "emphasis-normalization"
        assert "underscores instead of asterisks" in errors[0].message

    def test_check_bold_underscores(self):
        """Test check() reports bold underscore violations."""
        rule = EmphasisNormalizationRule()
        content = "__bold__ text"
        errors = rule.check(content, Path("test.md"))
        assert len(errors) == 1
        assert "double underscores" in errors[0].message

    def test_check_multiple_violations(self):
        """Test check() reports multiple violations."""
        rule = EmphasisNormalizationRule()
        content = "_italic1_ and _italic2_ and __bold1__ and __bold2__"
        errors = rule.check(content, Path("test.md"))
        assert len(errors) == 4

    def test_check_ignores_latex_inline(self):
        """Test check() ignores underscores in inline LaTeX."""
        rule = EmphasisNormalizationRule()
        content = "The value is $x_i$ and $y_j$"
        errors = rule.check(content, Path("test.md"))
        assert len(errors) == 0

    def test_check_ignores_latex_block(self):
        """Test check() ignores underscores in block LaTeX."""
        rule = EmphasisNormalizationRule()
        content = "The equation is $$P = \\frac{1}{n} \\sum_{i=1}^{n} x_i$$"
        errors = rule.check(content, Path("test.md"))
        assert len(errors) == 0

    def test_check_disabled(self):
        """Test check() returns no errors when disabled."""
        rule = EmphasisNormalizationRule(enabled=False)
        content = "_italic_ and __bold__ text"
        errors = rule.check(content, Path("test.md"))
        assert len(errors) == 0

    def test_check_empty_content(self):
        """Test check() with empty content."""
        rule = EmphasisNormalizationRule()
        content = ""
        errors = rule.check(content, Path("test.md"))
        assert len(errors) == 0

    def test_check_line_number(self):
        """Test check() reports correct line numbers."""
        rule = EmphasisNormalizationRule()
        content = "Line 1\n_italic_ text\nLine 3"
        errors = rule.check(content, Path("test.md"))
        assert len(errors) == 1
        assert errors[0].line_number == 2

    def test_check_column_number(self):
        """Test check() reports correct column numbers."""
        rule = EmphasisNormalizationRule()
        content = "_italic_ text"
        errors = rule.check(content, Path("test.md"))
        assert len(errors) == 1
        assert errors[0].column_number == 1

    def test_check_suggestion_italic(self):
        """Test check() provides suggestion for italic violations."""
        rule = EmphasisNormalizationRule()
        content = "_italic_ text"
        errors = rule.check(content, Path("test.md"))
        assert len(errors) == 1
        assert errors[0].suggestion is not None
        assert "*italic*" in errors[0].suggestion

    def test_check_suggestion_bold(self):
        """Test check() provides suggestion for bold violations."""
        rule = EmphasisNormalizationRule()
        content = "__bold__ text"
        errors = rule.check(content, Path("test.md"))
        assert len(errors) == 1
        assert errors[0].suggestion is not None
        assert "**bold**" in errors[0].suggestion

    def test_check_context(self):
        """Test check() provides context for violations."""
        rule = EmphasisNormalizationRule()
        content = "_italic_ text"
        errors = rule.check(content, Path("test.md"))
        assert len(errors) == 1
        assert errors[0].context is not None

    def test_check_mixed_content(self):
        """Test check() with mixed content and LaTeX."""
        rule = EmphasisNormalizationRule()
        content = "Text with _italic_ and $x_i$ and __bold__"
        errors = rule.check(content, Path("test.md"))
        assert len(errors) == 2

    def test_apply_preserves_asterisks(self):
        """Test apply() preserves asterisk emphasis."""
        rule = EmphasisNormalizationRule()
        content = "*italic* and **bold** text"
        result = rule.apply(content)
        assert result == content

    def test_check_ignores_asterisks(self):
        """Test check() ignores asterisk emphasis."""
        rule = EmphasisNormalizationRule()
        content = "*italic* and **bold** text"
        errors = rule.check(content, Path("test.md"))
        assert len(errors) == 0
