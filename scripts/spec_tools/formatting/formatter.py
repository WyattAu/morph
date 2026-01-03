"""
Markdown formatter for spec-tools package.

This module implements the MarkdownFormatter class which applies
formatting rules to markdown files.
"""

from pathlib import Path
from typing import List

from spec_tools.formatting.rules import FormattingRule
from spec_tools.formatting.rules.emphasis import EmphasisNormalizationRule
from spec_tools.formatting.rules.headings import HeadingSpacingRule
from spec_tools.formatting.rules.line_length import LineLengthRule
from spec_tools.formatting.rules.lists import ListNormalizationRule
from spec_tools.formatting.rules.whitespace import TrailingWhitespaceRule
from spec_tools.models import FormattingConfig, ValidationResult


class MarkdownFormatter:
    """Formats markdown files according to specification convention.

    This class implements the FormatterInterface and applies a series of
    formatting rules to markdown files. Rules are applied in a specific
    order to ensure consistent results.

    The formatter can:
    - Format individual files or entire directories
    - Check formatting without modifying files
    - Report formatting violations with suggestions
    """

    def __init__(self, config: FormattingConfig):
        """Initialize the markdown formatter.

        Args:
            config: Formatting configuration
        """
        self.config = config
        self.rules: List[FormattingRule] = self._load_rules()

    def _load_rules(self) -> List[FormattingRule]:
        """Load all formatting rules based on configuration.

        Returns:
            List of formatting rules to apply
        """
        rules = []

        # Load rules in order of application
        rules.append(LineLengthRule(self.config.max_line_length))
        rules.append(TrailingWhitespaceRule(self.config.enforce_trailing_whitespace))
        rules.append(HeadingSpacingRule(self.config.fix_heading_spacing))
        rules.append(ListNormalizationRule(self.config.normalize_lists))
        rules.append(EmphasisNormalizationRule(self.config.normalize_emphasis))

        return rules

    def format_file(self, filepath: Path) -> bool:
        """Format a single file.

        Applies all formatting rules to the file and writes the result
        back to disk if any changes were made.

        Args:
            filepath: Path to the file to format

        Returns:
            True if file was modified, False otherwise

        Raises:
            FormattingError: If the file cannot be read or written
        """
        try:
            content = filepath.read_text(encoding="utf-8")
            original_content = content

            # Apply all rules in order
            for rule in self.rules:
                content = rule.apply(content)

            # Write back if content changed
            if content != original_content:
                filepath.write_text(content, encoding="utf-8")
                return True

            return False
        except FileNotFoundError as e:
            from spec_tools.exceptions import FormattingError

            raise FormattingError(
                f"File not found: {filepath}",
                file_path=str(filepath),
            ) from e
        except Exception as e:
            from spec_tools.exceptions import FormattingError

            raise FormattingError(
                f"Error formatting file: {filepath}",
                file_path=str(filepath),
                details={"error": str(e)},
            ) from e

    def format_directory(self, directory: Path, recursive: bool = True) -> int:
        """Format all files in a directory.

        Applies formatting rules to all markdown files in the specified
        directory, optionally including subdirectories.

        Args:
            directory: Path to the directory
            recursive: Whether to process subdirectories (default: True)

        Returns:
            Number of files modified

        Raises:
            FormattingError: If the directory cannot be accessed
        """
        try:
            pattern = "**/*.md" if recursive else "*.md"
            files = list(directory.glob(pattern))

            modified_count = 0
            for filepath in files:
                if self.format_file(filepath):
                    modified_count += 1

            return modified_count
        except Exception as e:
            from spec_tools.exceptions import FormattingError

            raise FormattingError(
                f"Error formatting directory: {directory}",
                file_path=str(directory),
                details={"error": str(e)},
            ) from e

    def check_format(self, filepath: Path) -> ValidationResult:
        """Check if a file is properly formatted.

        Runs all formatting rules in check mode to report violations
        without modifying the file.

        Args:
            filepath: Path to the file to check

        Returns:
            Validation result with any formatting issues

        Raises:
            FormattingError: If the file cannot be read
        """
        try:
            content = filepath.read_text(encoding="utf-8")
            errors = []

            # Check all rules
            for rule in self.rules:
                rule_errors = rule.check(content, filepath)
                errors.extend(rule_errors)

            return ValidationResult(
                file_path=str(filepath),
                errors=errors,
                passed=len(errors) == 0,
            )
        except FileNotFoundError as e:
            from spec_tools.exceptions import FormattingError

            raise FormattingError(
                f"File not found: {filepath}",
                file_path=str(filepath),
            ) from e
        except Exception as e:
            from spec_tools.exceptions import FormattingError

            raise FormattingError(
                f"Error checking file format: {filepath}",
                file_path=str(filepath),
                details={"error": str(e)},
            ) from e
