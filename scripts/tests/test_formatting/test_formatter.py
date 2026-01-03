"""
Unit tests for MarkdownFormatter.
"""

import pytest

from spec_tools.formatting.formatter import MarkdownFormatter
from spec_tools.models import FormattingConfig, ValidationResult


class TestMarkdownFormatter:
    """Test cases for MarkdownFormatter."""

    def test_init_default_config(self):
        """Test MarkdownFormatter initialization with default config."""
        config = FormattingConfig()
        formatter = MarkdownFormatter(config)
        assert formatter.config == config
        assert len(formatter.rules) == 5

    def test_init_custom_config(self):
        """Test MarkdownFormatter initialization with custom config."""
        config = FormattingConfig(
            max_line_length=80,
            enforce_trailing_whitespace=False,
            normalize_lists=False,
            fix_heading_spacing=False,
            normalize_emphasis=False,
        )
        formatter = MarkdownFormatter(config)
        assert formatter.config == config
        assert len(formatter.rules) == 5

    def test_load_rules_order(self):
        """Test that rules are loaded in correct order."""
        config = FormattingConfig()
        formatter = MarkdownFormatter(config)
        rule_names = [rule.__class__.__name__ for rule in formatter.rules]
        assert rule_names == [
            "LineLengthRule",
            "TrailingWhitespaceRule",
            "HeadingSpacingRule",
            "ListNormalizationRule",
            "EmphasisNormalizationRule",
        ]

    def test_format_file_no_changes(self, temp_dir):
        """Test format_file() with file that needs no changes."""
        config = FormattingConfig()
        formatter = MarkdownFormatter(config)

        content = "# Heading\n\n- Item 1\n- Item 2"
        filepath = temp_dir / "test.md"
        filepath.write_text(content, encoding="utf-8")

        result = formatter.format_file(filepath)
        assert result is False
        assert filepath.read_text(encoding="utf-8") == content

    def test_format_file_with_changes(self, temp_dir):
        """Test format_file() with file that needs changes."""
        config = FormattingConfig()
        formatter = MarkdownFormatter(config)

        content = "#Heading\n\n* Item 1\n* Item 2  "
        filepath = temp_dir / "test.md"
        filepath.write_text(content, encoding="utf-8")

        result = formatter.format_file(filepath)
        assert result is True
        formatted = filepath.read_text(encoding="utf-8")
        assert formatted == "# Heading\n\n- Item 1\n- Item 2"

    def test_format_file_not_found(self, temp_dir):
        """Test format_file() with non-existent file."""
        config = FormattingConfig()
        formatter = MarkdownFormatter(config)

        filepath = temp_dir / "nonexistent.md"

        with pytest.raises(Exception) as exc_info:
            formatter.format_file(filepath)
        assert "File not found" in str(exc_info.value)

    def test_format_directory_single_file(self, temp_dir):
        """Test format_directory() with single file."""
        config = FormattingConfig()
        formatter = MarkdownFormatter(config)

        content = "#Heading\n\n* Item 1"
        filepath = temp_dir / "test.md"
        filepath.write_text(content, encoding="utf-8")

        result = formatter.format_directory(temp_dir, recursive=False)
        assert result == 1

    def test_format_directory_multiple_files(self, temp_dir):
        """Test format_directory() with multiple files."""
        config = FormattingConfig()
        formatter = MarkdownFormatter(config)

        content = "#Heading\n\n* Item 1"
        (temp_dir / "test1.md").write_text(content, encoding="utf-8")
        (temp_dir / "test2.md").write_text(content, encoding="utf-8")
        (temp_dir / "test3.md").write_text(content, encoding="utf-8")

        result = formatter.format_directory(temp_dir, recursive=False)
        assert result == 3

    def test_format_directory_recursive(self, temp_dir):
        """Test format_directory() with recursive option."""
        config = FormattingConfig()
        formatter = MarkdownFormatter(config)

        content = "#Heading\n\n* Item 1"
        (temp_dir / "test1.md").write_text(content, encoding="utf-8")
        subdir = temp_dir / "subdir"
        subdir.mkdir()
        (subdir / "test2.md").write_text(content, encoding="utf-8")

        result = formatter.format_directory(temp_dir, recursive=True)
        assert result == 2

    def test_format_directory_non_recursive(self, temp_dir):
        """Test format_directory() without recursive option."""
        config = FormattingConfig()
        formatter = MarkdownFormatter(config)

        content = "#Heading\n\n* Item 1"
        (temp_dir / "test1.md").write_text(content, encoding="utf-8")
        subdir = temp_dir / "subdir"
        subdir.mkdir()
        (subdir / "test2.md").write_text(content, encoding="utf-8")

        result = formatter.format_directory(temp_dir, recursive=False)
        assert result == 1

    def test_format_directory_no_changes(self, temp_dir):
        """Test format_directory() with files that need no changes."""
        config = FormattingConfig()
        formatter = MarkdownFormatter(config)

        content = "# Heading\n\n- Item 1"
        (temp_dir / "test1.md").write_text(content, encoding="utf-8")
        (temp_dir / "test2.md").write_text(content, encoding="utf-8")

        result = formatter.format_directory(temp_dir, recursive=False)
        assert result == 0

    def test_format_directory_empty(self, temp_dir):
        """Test format_directory() with empty directory."""
        config = FormattingConfig()
        formatter = MarkdownFormatter(config)

        result = formatter.format_directory(temp_dir, recursive=False)
        assert result == 0

    def test_check_format_no_errors(self, temp_dir):
        """Test check_format() with properly formatted file."""
        config = FormattingConfig()
        formatter = MarkdownFormatter(config)

        content = "# Heading\n\n- Item 1\n- Item 2"
        filepath = temp_dir / "test.md"
        filepath.write_text(content, encoding="utf-8")

        result = formatter.check_format(filepath)
        assert isinstance(result, ValidationResult)
        assert result.passed is True
        assert len(result.errors) == 0

    def test_check_format_with_errors(self, temp_dir):
        """Test check_format() with formatting errors."""
        config = FormattingConfig()
        formatter = MarkdownFormatter(config)

        content = "#Heading\n\n* Item 1\n* Item 2  "
        filepath = temp_dir / "test.md"
        filepath.write_text(content, encoding="utf-8")

        result = formatter.check_format(filepath)
        assert isinstance(result, ValidationResult)
        assert result.passed is False
        assert len(result.errors) > 0

    def test_check_format_file_not_found(self, temp_dir):
        """Test check_format() with non-existent file."""
        config = FormattingConfig()
        formatter = MarkdownFormatter(config)

        filepath = temp_dir / "nonexistent.md"

        with pytest.raises(Exception) as exc_info:
            formatter.check_format(filepath)
        assert "File not found" in str(exc_info.value)

    def test_check_format_error_details(self, temp_dir):
        """Test check_format() provides detailed error information."""
        config = FormattingConfig()
        formatter = MarkdownFormatter(config)

        content = "#Heading\n\n* Item 1\n* Item 2  "
        filepath = temp_dir / "test.md"
        filepath.write_text(content, encoding="utf-8")

        result = formatter.check_format(filepath)
        assert result.file_path == str(filepath)
        assert len(result.errors) > 0

        # Check that errors have required fields
        for error in result.errors:
            assert error.file_path == str(filepath)
            assert error.line_number > 0
            assert error.rule_id != ""
            assert error.message != ""

    def test_format_file_encoding(self, temp_dir):
        """Test format_file() handles UTF-8 encoding correctly."""
        config = FormattingConfig()
        formatter = MarkdownFormatter(config)

        content = "# Heading with unicode: café\n\n- Item with emoji: 🎉"
        filepath = temp_dir / "test.md"
        filepath.write_text(content, encoding="utf-8")

        result = formatter.format_file(filepath)
        assert result is False
        assert filepath.read_text(encoding="utf-8") == content

    def test_format_file_preserves_content(self, temp_dir):
        """Test format_file() preserves non-formatted content."""
        config = FormattingConfig()
        formatter = MarkdownFormatter(config)

        content = """# Heading

Regular paragraph with **bold** and *italic* text.

```python
def function():
    return "value"
```

| Column 1 | Column 2 |
|----------|----------|
| Value 1  | Value 2  |
"""
        filepath = temp_dir / "test.md"
        filepath.write_text(content, encoding="utf-8")

        result = formatter.format_file(filepath)
        assert result is False
        assert filepath.read_text(encoding="utf-8") == content

    def test_format_file_with_long_lines(self, temp_dir):
        """Test format_file() wraps long lines."""
        config = FormattingConfig(max_line_length=40)
        formatter = MarkdownFormatter(config)

        content = "This is a very long line that exceeds the maximum length and should be wrapped."
        filepath = temp_dir / "test.md"
        filepath.write_text(content, encoding="utf-8")

        result = formatter.format_file(filepath)
        assert result is True
        formatted = filepath.read_text(encoding="utf-8")
        lines = formatted.split("\n")
        assert all(len(line) <= 40 for line in lines)

    def test_format_file_with_disabled_rules(self, temp_dir):
        """Test format_file() respects disabled rules."""
        config = FormattingConfig(
            fix_heading_spacing=False,
            normalize_lists=False,
        )
        formatter = MarkdownFormatter(config)

        content = "#Heading\n\n* Item 1\n* Item 2  "
        filepath = temp_dir / "test.md"
        filepath.write_text(content, encoding="utf-8")

        result = formatter.format_file(filepath)
        assert result is True
        formatted = filepath.read_text(encoding="utf-8")
        # Heading and list should not be changed
        assert "#Heading" in formatted
        assert "* Item 1" in formatted
        # But trailing whitespace should be removed
        assert not formatted.endswith("  ")

    def test_check_format_with_disabled_rules(self, temp_dir):
        """Test check_format() respects disabled rules."""
        config = FormattingConfig(
            fix_heading_spacing=False,
            normalize_lists=False,
        )
        formatter = MarkdownFormatter(config)

        content = "#Heading\n\n* Item 1\n* Item 2  "
        filepath = temp_dir / "test.md"
        filepath.write_text(content, encoding="utf-8")

        result = formatter.check_format(filepath)
        # Should only report trailing whitespace error
        assert len(result.errors) == 1
        assert result.errors[0].rule_id == "trailing-whitespace"

    def test_format_file_empty(self, temp_dir):
        """Test format_file() with empty file."""
        config = FormattingConfig()
        formatter = MarkdownFormatter(config)

        filepath = temp_dir / "test.md"
        filepath.write_text("", encoding="utf-8")

        result = formatter.format_file(filepath)
        assert result is False
        assert filepath.read_text(encoding="utf-8") == ""

    def test_check_format_empty(self, temp_dir):
        """Test check_format() with empty file."""
        config = FormattingConfig()
        formatter = MarkdownFormatter(config)

        filepath = temp_dir / "test.md"
        filepath.write_text("", encoding="utf-8")

        result = formatter.check_format(filepath)
        assert result.passed is True
        assert len(result.errors) == 0
