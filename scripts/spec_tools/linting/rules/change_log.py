"""
Change log validation rule.

This module implements the ChangeLogRule which validates
the change log section in specification files.
"""

import re
from pathlib import Path
from typing import List

from spec_tools.linting.rules import LintingRule
from spec_tools.models import LintError, Severity


class ChangeLogRule(LintingRule):
    """Validates change log section in specification files.

    This rule checks that:
    - Change log section exists
    - Change log is formatted as a table
    - Required columns are present (Version, Date, Author, Changes)

    Expected format:
    | Version | Date | Author | Changes |
    |---------|-------|--------|---------|
    | 1.0.0   | ...    | ...    | ...     |
    """

    @property
    def description(self) -> str:
        """Get rule description."""
        return "Validates change log section"

    def __init__(self) -> None:
        """Initialize change log rule."""
        self._required_columns = ["Version", "Date", "Author", "Changes"]
        self._table_pattern = re.compile(r"^\|(.+)\|$")
        self._heading_pattern = re.compile(r"^#+\s*Change\s*Log", re.IGNORECASE)

    def check(self, content: str, lines: List[str], filepath: Path) -> List[LintError]:
        """Check if content has valid change log.

        Args:
            content: Full content of file
            lines: List of lines in file
            filepath: File path for error reporting

        Returns:
            List of change log validation errors
        """
        errors = []

        # Find change log section
        change_log_line = self._find_change_log_section(lines)

        if change_log_line is None:
            errors.append(
                LintError(
                    file_path=str(filepath),
                    line_number=1,
                    severity=Severity.WARNING,
                    rule_id="change-log",
                    message="Missing change log section",
                    suggestion="Add a '## Change Log' section with a table of changes",
                )
            )
            return errors

        # Validate table format
        self._validate_table_format(lines, change_log_line, filepath, errors)

        return errors

    def _find_change_log_section(self, lines: List[str]) -> int | None:
        """Find the line number of the change log section.

        Args:
            lines: List of lines in file

        Returns:
            Line number of change log section, or None if not found
        """
        for line_num, line in enumerate(lines, start=1):
            if self._heading_pattern.match(line):
                return line_num
        return None

    def _validate_table_format(
        self, lines: List[str], start_line: int, filepath: Path, errors: List[LintError]
    ) -> None:
        """Validate the change log table format.

        Args:
            lines: List of lines in file
            start_line: Starting line number of change log section
            filepath: File path for error reporting
            errors: List to append errors to
        """
        # Find the first table row after the heading
        table_start = None
        for i in range(start_line, len(lines)):
            if self._table_pattern.match(lines[i]):
                table_start = i
                break

        if table_start is None:
            errors.append(
                LintError(
                    file_path=str(filepath),
                    line_number=start_line,
                    severity=Severity.ERROR,
                    rule_id="change-log",
                    message="Change log section does not contain a table",
                    suggestion="Add a table with columns: Version, Date, Author, Changes",
                )
            )
            return

        # Extract header row
        header_line = lines[table_start]
        header_match = self._table_pattern.match(header_line)

        if not header_match:
            return

        # Parse header columns
        header_text = header_match.group(1)
        columns = [col.strip() for col in header_text.split("|") if col.strip()]

        # Check for required columns
        for required in self._required_columns:
            if required not in columns:
                errors.append(
                    LintError(
                        file_path=str(filepath),
                        line_number=table_start + 1,
                        severity=Severity.ERROR,
                        rule_id="change-log",
                        message=f"Missing required column in change log table: {required}",
                        suggestion=f"Add '{required}' column to the table",
                        context=header_line,
                    )
                )

        # Check for separator row (should be next line)
        if table_start + 1 < len(lines):
            separator_line = lines[table_start + 1]
            if not self._table_pattern.match(separator_line):
                errors.append(
                    LintError(
                        file_path=str(filepath),
                        line_number=table_start + 2,
                        severity=Severity.WARNING,
                        rule_id="change-log",
                        message="Change log table missing separator row",
                        suggestion="Add a separator row with dashes after the header",
                        context=separator_line,
                    )
                )
