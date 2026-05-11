"""
Unit tests for LineLengthRule.
"""

from pathlib import Path

from spec_tools.formatting.rules.line_length import LineLengthRule
from spec_tools.models import Severity


class TestLineLengthRule:
    """Test cases for LineLengthRule."""

    def test_init_default(self):
        """Test LineLengthRule initialization with default max_length."""
        rule = LineLengthRule()
        assert rule.max_length == 120

    def test_init_custom(self):
        """Test LineLengthRule initialization with custom max_length."""
        rule = LineLengthRule(max_length=80)
        assert rule.max_length == 80

    def test_apply_short_line(self):
        """Test apply() with a short line that doesn't need wrapping."""
        rule = LineLengthRule(max_length=120)
        content = "This is a short line."
        result = rule.apply(content)
        assert result == content

    def test_apply_long_line_wrapping(self):
        """Test apply() wraps a long line at word boundaries."""
        rule = LineLengthRule(max_length=20)
        content = "This is a very long line that needs to be wrapped at word boundaries."
        result = rule.apply(content)
        lines = result.split("\n")
        assert len(lines) > 1
        assert all(len(line) <= 20 for line in lines)

    def test_apply_preserves_code_blocks(self):
        """Test apply() preserves code blocks without wrapping."""
        rule = LineLengthRule(max_length=20)
        content = """```python
def very_long_function_name_that_exceeds_max_length():
    return "value"
```"""
        result = rule.apply(content)
        assert "def very_long_function_name_that_exceeds_max_length():" in result

    def test_apply_preserves_indented_code(self):
        """Test apply() preserves indented code blocks."""
        rule = LineLengthRule(max_length=20)
        content = """    def very_long_function_name():
        return "value"
"""
        result = rule.apply(content)
        assert "    def very_long_function_name():" in result

    def test_apply_preserves_urls(self):
        """Test apply() preserves lines with URLs."""
        rule = LineLengthRule(max_length=20)
        content = "See https://github.com/morph/spec-tools for more information."
        result = rule.apply(content)
        assert "https://github.com/morph/spec-tools" in result

    def test_apply_preserves_ftp_urls(self):
        """Test apply() preserves lines with FTP URLs."""
        rule = LineLengthRule(max_length=20)
        content = "Download from ftp://example.com/file.txt"
        result = rule.apply(content)
        assert "ftp://example.com/file.txt" in result

    def test_apply_multiple_lines(self):
        """Test apply() with multiple lines."""
        rule = LineLengthRule(max_length=20)
        content = """Short line.
This is a very long line that needs wrapping.
Another short line."""
        result = rule.apply(content)
        lines = result.split("\n")
        assert len(lines) > 3

    def test_apply_empty_content(self):
        """Test apply() with empty content."""
        rule = LineLengthRule(max_length=120)
        content = ""
        result = rule.apply(content)
        assert result == ""

    def test_check_no_violations(self):
        """Test check() with content that has no violations."""
        rule = LineLengthRule(max_length=120)
        content = "This is a short line."
        errors = rule.check(content, Path("test.md"))
        assert len(errors) == 0

    def test_check_long_line_violation(self):
        """Test check() reports long line violations."""
        rule = LineLengthRule(max_length=20)
        content = "This is a very long line that exceeds the maximum length."
        errors = rule.check(content, Path("test.md"))
        assert len(errors) == 1
        assert errors[0].severity == Severity.WARNING
        assert errors[0].rule_id == "line-length"
        assert "exceeds maximum length" in errors[0].message

    def test_check_multiple_violations(self):
        """Test check() reports multiple violations."""
        rule = LineLengthRule(max_length=20)
        content = """This is a very long line that exceeds the maximum length.
Short line.
Another very long line that also exceeds the maximum length."""
        errors = rule.check(content, Path("test.md"))
        assert len(errors) == 2

    def test_check_ignores_code_blocks(self):
        """Test check() ignores lines in code blocks."""
        rule = LineLengthRule(max_length=20)
        content = """```python
def very_long_function_name_that_exceeds_max_length():
    return "value"
```"""
        errors = rule.check(content, Path("test.md"))
        assert len(errors) == 0

    def test_check_ignores_indented_code(self):
        """Test check() ignores indented code blocks."""
        rule = LineLengthRule(max_length=20)
        content = """    def very_long_function_name():
        return "value"
"""
        errors = rule.check(content, Path("test.md"))
        assert len(errors) == 0

    def test_check_ignores_urls(self):
        """Test check() ignores lines with URLs."""
        rule = LineLengthRule(max_length=20)
        content = "See https://github.com/morph/spec-tools for more information."
        errors = rule.check(content, Path("test.md"))
        assert len(errors) == 0

    def test_check_fenced_code_blocks(self):
        """Test check() correctly handles fenced code blocks."""
        rule = LineLengthRule(max_length=20)
        content = """Normal line.
```python
def very_long_function_name():
    pass
```
Another normal line."""
        errors = rule.check(content, Path("test.md"))
        assert len(errors) == 0

    def test_check_line_number(self):
        """Test check() reports correct line numbers."""
        rule = LineLengthRule(max_length=20)
        content = """Short line.
This is a very long line that exceeds the maximum length.
Another short line."""
        errors = rule.check(content, Path("test.md"))
        assert len(errors) == 1
        assert errors[0].line_number == 2

    def test_check_column_number(self):
        """Test check() reports correct column numbers."""
        rule = LineLengthRule(max_length=20)
        content = "This is a very long line that exceeds the maximum length."
        errors = rule.check(content, Path("test.md"))
        assert len(errors) == 1
        assert errors[0].column_number == 21

    def test_check_suggestion(self):
        """Test check() provides helpful suggestions."""
        rule = LineLengthRule(max_length=20)
        content = "This is a very long line that exceeds the maximum length."
        errors = rule.check(content, Path("test.md"))
        assert len(errors) == 1
        assert errors[0].suggestion is not None
        assert "Wrap the line" in errors[0].suggestion

    def test_check_context(self):
        """Test check() provides context for violations."""
        rule = LineLengthRule(max_length=20)
        content = "This is a very long line that exceeds the maximum length."
        errors = rule.check(content, Path("test.md"))
        assert len(errors) == 1
        assert errors[0].context is not None

    def test_wrap_line_empty(self):
        """Test _wrap_line() with empty string."""
        rule = LineLengthRule(max_length=20)
        result = rule._wrap_line("")
        assert result == [""]

    def test_wrap_line_single_word(self):
        """Test _wrap_line() with a single word."""
        rule = LineLengthRule(max_length=20)
        result = rule._wrap_line("word")
        assert result == ["word"]

    def test_wrap_line_multiple_words(self):
        """Test _wrap_line() with multiple words."""
        rule = LineLengthRule(max_length=20)
        result = rule._wrap_line("one two three four five")
        assert len(result) == 2
        assert " ".join(result) == "one two three four five"

    def test_wrap_line_long_word(self):
        """Test _wrap_line() with a word longer than max_length."""
        rule = LineLengthRule(max_length=10)
        result = rule._wrap_line("verylongword")
        assert result == ["verylongword"]

    def test_wrap_line_preserves_order(self):
        """Test _wrap_line() preserves word order."""
        rule = LineLengthRule(max_length=10)
        result = rule._wrap_line("one two three four five six")
        words = " ".join(result).split()
        assert words == ["one", "two", "three", "four", "five", "six"]
