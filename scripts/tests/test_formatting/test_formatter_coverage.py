"""Additional tests for MarkdownFormatter to improve coverage."""

from pathlib import Path
from unittest.mock import patch

import pytest

from spec_tools.formatting.formatter import MarkdownFormatter
from spec_tools.models import FormattingConfig


class TestMarkdownFormatterCoverage:
    def test_format_file_permission_error(self, temp_dir):
        config = FormattingConfig()
        formatter = MarkdownFormatter(config)

        filepath = temp_dir / "test.md"
        filepath.write_text("#Heading\n", encoding="utf-8")

        with patch.object(Path, "read_text", side_effect=PermissionError("denied")):
            with pytest.raises(Exception) as exc_info:
                formatter.format_file(filepath)
            assert "Error formatting file" in str(exc_info.value)

    def test_format_directory_generic_exception(self, temp_dir):
        config = FormattingConfig()
        formatter = MarkdownFormatter(config)

        filepath = temp_dir / "test.md"
        filepath.write_text("#Heading\n", encoding="utf-8")

        with patch.object(Path, "glob", side_effect=RuntimeError("glob error")):
            with pytest.raises(Exception) as exc_info:
                formatter.format_directory(temp_dir)
            assert "Error formatting directory" in str(exc_info.value)

    def test_check_format_permission_error(self, temp_dir):
        config = FormattingConfig()
        formatter = MarkdownFormatter(config)

        filepath = temp_dir / "test.md"
        filepath.write_text("#Heading\n", encoding="utf-8")

        with patch.object(Path, "read_text", side_effect=PermissionError("denied")):
            with pytest.raises(Exception) as exc_info:
                formatter.check_format(filepath)
            assert "Error checking file format" in str(exc_info.value)

    def test_format_directory_non_recursive_no_md_files(self, temp_dir):
        config = FormattingConfig()
        formatter = MarkdownFormatter(config)

        (temp_dir / "not_a_md.txt").write_text("hello\n", encoding="utf-8")

        result = formatter.format_directory(temp_dir, recursive=False)
        assert result == 0
