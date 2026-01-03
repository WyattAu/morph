"""
Unit tests for SpecLinkChecker.
"""

from pathlib import Path

import pytest

from spec_tools.link_checker.checker import SpecLinkChecker
from spec_tools.models import LinkCheckingConfig


class TestSpecLinkChecker:
    """Test cases for SpecLinkChecker."""

    def test_init_default_config(self):
        """Test SpecLinkChecker initialization with default config."""
        config = LinkCheckingConfig()
        checker = SpecLinkChecker(config)
        assert checker.config == config

    def test_init_custom_config(self):
        """Test SpecLinkChecker initialization with custom config."""
        config = LinkCheckingConfig(
            check_broken_links=False,
            check_orphaned_sections=False,
            check_duplicate_links=False,
            check_self_references=False,
        )
        checker = SpecLinkChecker(config)
        assert checker.config == config

    def test_check_file_no_links(self, temp_dir):
        """Test check_file() with file that has no links."""
        config = LinkCheckingConfig()
        checker = SpecLinkChecker(config)

        content = """# Specification

This is a specification with no links.

## Requirements

The system SHALL provide basic functionality.
"""
        filepath = temp_dir / "test.md"
        filepath.write_text(content, encoding="utf-8")

        result = checker.check_file(filepath)
        assert result.passed is True
        assert result.total_links == 0

    def test_check_file_with_valid_links(self, temp_dir):
        """Test check_file() with file that has valid links."""
        config = LinkCheckingConfig()
        checker = SpecLinkChecker(config)

        content = """# Specification

See [Section 2](#section-2) for details.

## Requirements

The system SHALL provide basic functionality.

## Section 2

Details about section 2.
"""
        filepath = temp_dir / "test.md"
        filepath.write_text(content, encoding="utf-8")

        result = checker.check_file(filepath)
        assert result.passed is True
        assert result.total_links > 0

    def test_check_file_with_broken_links(self, temp_dir):
        """Test check_file() with file that has broken links."""
        config = LinkCheckingConfig()
        checker = SpecLinkChecker(config)

        content = """# Specification

See [Non-existent Section](#non-existent-section) for details.

## Requirements

The system SHALL provide basic functionality.
"""
        filepath = temp_dir / "test.md"
        filepath.write_text(content, encoding="utf-8")

        result = checker.check_file(filepath)
        assert result.passed is False
        assert len(result.broken_links) > 0

    def test_check_file_not_found(self, temp_dir):
        """Test check_file() with non-existent file."""
        config = LinkCheckingConfig()
        checker = SpecLinkChecker(config)

        filepath = temp_dir / "nonexistent.md"

        with pytest.raises(Exception) as exc_info:
            checker.check_file(filepath)
        assert "File not found" in str(exc_info.value)

    def test_check_directory_single_file(self, temp_dir):
        """Test check_directory() with single file."""
        config = LinkCheckingConfig()
        checker = SpecLinkChecker(config)

        content = """# Specification

See [Section 2](#section-2) for details.

## Requirements

The system SHALL provide basic functionality.

## Section 2

Details about section 2.
"""
        (temp_dir / "test.md").write_text(content, encoding="utf-8")

        results = checker.check_directory(temp_dir, recursive=False)
        assert len(results) == 1

    def test_check_directory_multiple_files(self, temp_dir):
        """Test check_directory() with multiple files."""
        config = LinkCheckingConfig()
        checker = SpecLinkChecker(config)

        content = """# Specification

See [Section 2](#section-2) for details.

## Requirements

The system SHALL provide basic functionality.

## Section 2

Details about section 2.
"""
        (temp_dir / "test1.md").write_text(content, encoding="utf-8")
        (temp_dir / "test2.md").write_text(content, encoding="utf-8")
        (temp_dir / "test3.md").write_text(content, encoding="utf-8")

        results = checker.check_directory(temp_dir, recursive=False)
        assert len(results) == 3

    def test_check_directory_recursive(self, temp_dir):
        """Test check_directory() with recursive option."""
        config = LinkCheckingConfig()
        checker = SpecLinkChecker(config)

        content = """# Specification

See [Section 2](#section-2) for details.

## Requirements

The system SHALL provide basic functionality.

## Section 2

Details about section 2.
"""
        (temp_dir / "test1.md").write_text(content, encoding="utf-8")
        subdir = temp_dir / "subdir"
        subdir.mkdir()
        (subdir / "test2.md").write_text(content, encoding="utf-8")

        results = checker.check_directory(temp_dir, recursive=True)
        assert len(results) == 2

    def test_check_directory_empty(self, temp_dir):
        """Test check_directory() with empty directory."""
        config = LinkCheckingConfig()
        checker = SpecLinkChecker(config)

        results = checker.check_directory(temp_dir, recursive=False)
        assert len(results) == 0

    def test_check_file_with_disabled_checks(self, temp_dir):
        """Test check_file() respects disabled checks."""
        config = LinkCheckingConfig(
            check_broken_links=False,
            check_orphaned_sections=False,
            check_duplicate_links=False,
            check_self_references=False,
        )
        checker = SpecLinkChecker(config)

        content = """# Specification

See [Non-existent Section](#non-existent-section) for details.

## Requirements

The system SHALL provide basic functionality.
"""
        filepath = temp_dir / "test.md"
        filepath.write_text(content, encoding="utf-8")

        result = checker.check_file(filepath)
        assert result.passed is True

    def test_check_file_encoding(self, temp_dir):
        """Test check_file() handles UTF-8 encoding correctly."""
        config = LinkCheckingConfig()
        checker = SpecLinkChecker(config)

        content = """# Specification with unicode: café

See [Section 2](#section-2) for details with emoji: 🎉.

## Requirements

The system SHALL provide basic functionality.

## Section 2

Details about section 2.
"""
        filepath = temp_dir / "test.md"
        filepath.write_text(content, encoding="utf-8")

        result = checker.check_file(filepath)
        assert result.passed is True

    def test_check_file_empty(self, temp_dir):
        """Test check_file() with empty file."""
        config = LinkCheckingConfig()
        checker = SpecLinkChecker(config)

        filepath = temp_dir / "test.md"
        filepath.write_text("", encoding="utf-8")

        result = checker.check_file(filepath)
        assert result.passed is True
        assert result.total_links == 0

    def test_check_file_with_self_references(self, temp_dir):
        """Test check_file() detects self-references."""
        config = LinkCheckingConfig(check_self_references=True)
        checker = SpecLinkChecker(config)

        content = """# Specification

See [this section](#specification) for details.

## Requirements

The system SHALL provide basic functionality.
"""
        filepath = temp_dir / "test.md"
        filepath.write_text(content, encoding="utf-8")

        result = checker.check_file(filepath)
        assert len(result.self_references) > 0

    def test_check_file_with_duplicate_links(self, temp_dir):
        """Test check_file() detects duplicate links."""
        config = LinkCheckingConfig(check_duplicate_links=True)
        checker = SpecLinkChecker(config)

        content = """# Specification

See [Section 2](#section-2) for details.

Also see [Section 2](#section-2) for more details.

## Requirements

The system SHALL provide basic functionality.

## Section 2

Details about section 2.
"""
        filepath = temp_dir / "test.md"
        filepath.write_text(content, encoding="utf-8")

        result = checker.check_file(filepath)
        assert result.duplicate_count > 0
