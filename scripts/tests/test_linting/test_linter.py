"""
Unit tests for SpecLinter.
"""

from pathlib import Path

import pytest

from spec_tools.linting.linter import SpecLinter
from spec_tools.models import LintingConfig, Severity


class TestSpecLinter:
    """Test cases for SpecLinter."""

    def test_init_default_config(self):
        """Test SpecLinter initialization with default config."""
        config = LintingConfig()
        linter = SpecLinter(config)
        assert linter.config == config
        assert len(linter.rules) == 6

    def test_init_custom_config(self):
        """Test SpecLinter initialization with custom config."""
        config = LintingConfig(
            check_ears_pattern=False,
            check_math_notation=False,
            check_mermaid_syntax=False,
            check_cross_references=False,
        )
        linter = SpecLinter(config)
        assert linter.config == config
        assert len(linter.rules) == 2

    def test_load_rules_all_enabled(self):
        """Test that all rules are loaded when enabled."""
        config = LintingConfig()
        linter = SpecLinter(config)
        rule_names = list(linter.rules.keys())
        assert "header" in rule_names
        assert "sections" in rule_names
        assert "ears" in rule_names
        assert "math" in rule_names
        assert "mermaid" in rule_names
        assert "cross_refs" in rule_names
        assert "change_log" in rule_names

    def test_load_rules_some_disabled(self):
        """Test that only enabled rules are loaded."""
        config = LintingConfig(
            check_ears_pattern=False,
            check_math_notation=False,
        )
        linter = SpecLinter(config)
        rule_names = list(linter.rules.keys())
        assert "header" in rule_names
        assert "sections" in rule_names
        assert "ears" not in rule_names
        assert "math" not in rule_names
        assert "mermaid" in rule_names
        assert "cross_refs" in rule_names
        assert "change_log" in rule_names

    def test_lint_file_no_errors(self, temp_dir):
        """Test lint_file() with file that has no errors."""
        config = LintingConfig()
        linter = SpecLinter(config)

        content = """Title: Sample Specification
Version: 1.0.0
Status: Draft
Author: John Doe
Last Modified: 2024-01-01

# 1. Purpose and Scope

## 2. Definitions

## 3. Requirements

### REQ-001: Basic Requirement

The system SHALL provide basic functionality.

## Change Log

| Version | Date | Author | Description |
|---------|------|--------|-------------|
| 1.0.0 | 2024-01-01 | John Doe | Initial version |
"""
        filepath = temp_dir / "test.md"
        filepath.write_text(content, encoding="utf-8")

        result = linter.lint_file(filepath)
        assert result.passed is True
        assert len(result.errors) == 0

    def test_lint_file_with_errors(self, temp_dir):
        """Test lint_file() with file that has errors."""
        config = LintingConfig()
        linter = SpecLinter(config)

        content = """Title: Sample Specification
Version: 1.0
Status: Invalid
Author: John Doe

# Content
"""
        filepath = temp_dir / "test.md"
        filepath.write_text(content, encoding="utf-8")

        result = linter.lint_file(filepath)
        assert result.passed is False
        assert len(result.errors) > 0

    def test_lint_file_not_found(self, temp_dir):
        """Test lint_file() with non-existent file."""
        config = LintingConfig()
        linter = SpecLinter(config)

        filepath = temp_dir / "nonexistent.md"

        with pytest.raises(Exception) as exc_info:
            linter.lint_file(filepath)
        assert "File not found" in str(exc_info.value)

    def test_lint_directory_single_file(self, temp_dir):
        """Test lint_directory() with single file."""
        config = LintingConfig()
        linter = SpecLinter(config)

        content = """Title: Sample Specification
Version: 1.0.0
Status: Draft
Author: John Doe
Last Modified: 2024-01-01

# Content
"""
        (temp_dir / "test.md").write_text(content, encoding="utf-8")

        results = linter.lint_directory(temp_dir, recursive=False)
        assert len(results) == 1

    def test_lint_directory_multiple_files(self, temp_dir):
        """Test lint_directory() with multiple files."""
        config = LintingConfig()
        linter = SpecLinter(config)

        content = """Title: Sample Specification
Version: 1.0.0
Status: Draft
Author: John Doe
Last Modified: 2024-01-01

# Content
"""
        (temp_dir / "test1.md").write_text(content, encoding="utf-8")
        (temp_dir / "test2.md").write_text(content, encoding="utf-8")
        (temp_dir / "test3.md").write_text(content, encoding="utf-8")

        results = linter.lint_directory(temp_dir, recursive=False)
        assert len(results) == 3

    def test_lint_directory_recursive(self, temp_dir):
        """Test lint_directory() with recursive option."""
        config = LintingConfig()
        linter = SpecLinter(config)

        content = """Title: Sample Specification
Version: 1.0.0
Status: Draft
Author: John Doe
Last Modified: 2024-01-01

# Content
"""
        (temp_dir / "test1.md").write_text(content, encoding="utf-8")
        subdir = temp_dir / "subdir"
        subdir.mkdir()
        (subdir / "test2.md").write_text(content, encoding="utf-8")

        results = linter.lint_directory(temp_dir, recursive=True)
        assert len(results) == 2

    def test_lint_directory_non_recursive(self, temp_dir):
        """Test lint_directory() without recursive option."""
        config = LintingConfig()
        linter = SpecLinter(config)

        content = """Title: Sample Specification
Version: 1.0.0
Status: Draft
Author: John Doe
Last Modified: 2024-01-01

# Content
"""
        (temp_dir / "test1.md").write_text(content, encoding="utf-8")
        subdir = temp_dir / "subdir"
        subdir.mkdir()
        (subdir / "test2.md").write_text(content, encoding="utf-8")

        results = linter.lint_directory(temp_dir, recursive=False)
        assert len(results) == 1

    def test_lint_directory_empty(self, temp_dir):
        """Test lint_directory() with empty directory."""
        config = LintingConfig()
        linter = SpecLinter(config)

        results = linter.lint_directory(temp_dir, recursive=False)
        assert len(results) == 0

    def test_get_rules(self):
        """Test get_rules() returns rule descriptions."""
        config = LintingConfig()
        linter = SpecLinter(config)

        rules = linter.get_rules()
        assert isinstance(rules, dict)
        assert len(rules) > 0

        # Check that all values are strings (descriptions)
        for rule_id, description in rules.items():
            assert isinstance(rule_id, str)
            assert isinstance(description, str)

    def test_lint_file_error_details(self, temp_dir):
        """Test lint_file() provides detailed error information."""
        config = LintingConfig()
        linter = SpecLinter(config)

        content = """Title: Sample Specification
Version: 1.0
Status: Invalid
Author: John Doe

# Content
"""
        filepath = temp_dir / "test.md"
        filepath.write_text(content, encoding="utf-8")

        result = linter.lint_file(filepath)
        assert result.file_path == str(filepath)
        assert len(result.errors) > 0

        # Check that errors have required fields
        for error in result.errors:
            assert error.file_path == str(filepath)
            assert error.line_number > 0
            assert error.rule_id != ""
            assert error.message != ""

    def test_lint_file_encoding(self, temp_dir):
        """Test lint_file() handles UTF-8 encoding correctly."""
        config = LintingConfig()
        linter = SpecLinter(config)

        content = """Title: Sample Specification with unicode: café
Version: 1.0.0
Status: Draft
Author: John Doe
Last Modified: 2024-01-01

# Content with emoji: 🎉
"""
        filepath = temp_dir / "test.md"
        filepath.write_text(content, encoding="utf-8")

        result = linter.lint_file(filepath)
        assert result.passed is True

    def test_lint_file_with_disabled_rules(self, temp_dir):
        """Test lint_file() respects disabled rules."""
        config = LintingConfig(
            check_ears_pattern=False,
            check_math_notation=False,
            check_mermaid_syntax=False,
            check_cross_references=False,
        )
        linter = SpecLinter(config)

        content = """Title: Sample Specification
Version: 1.0.0
Status: Draft
Author: John Doe
Last Modified: 2024-01-01

# Content
"""
        filepath = temp_dir / "test.md"
        filepath.write_text(content, encoding="utf-8")

        result = linter.lint_file(filepath)
        assert result.passed is True

    def test_lint_file_empty(self, temp_dir):
        """Test lint_file() with empty file."""
        config = LintingConfig()
        linter = SpecLinter(config)

        filepath = temp_dir / "test.md"
        filepath.write_text("", encoding="utf-8")

        result = linter.lint_file(filepath)
        assert result.passed is False
        assert len(result.errors) > 0

    def test_lint_file_with_warnings_only(self, temp_dir):
        """Test lint_file() with warnings only (no errors)."""
        config = LintingConfig()
        linter = SpecLinter(config)

        content = """Title: Sample Specification
Version: 1.0.0
Status: Draft
Author: John Doe
Last Modified: 2024-01-01

## 2. Definitions

### 4. Requirements

The system SHALL provide basic functionality.
"""
        filepath = temp_dir / "test.md"
        filepath.write_text(content, encoding="utf-8")

        result = linter.lint_file(filepath)
        # Should pass if only warnings (no ERROR severity)
        error_count = sum(1 for e in result.errors if e.severity == Severity.ERROR)
        assert error_count == 0
