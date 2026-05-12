"""
Header validation rule.

This module implements the HeaderValidationRule which validates
the header fields in specification files.
"""

import re
from pathlib import Path
from typing import List

from spec_tools.linting.rules import LintingRule
from spec_tools.models import LintError, Severity


class HeaderValidationRule(LintingRule):
    """Validates specification file headers.

    This rule checks that:
    - All required header fields are present
    - Version follows SemVer format (X.Y.Z)
    - Status is one of the allowed values
    - File path in header matches actual filename

    Required header fields:
    - Title
    - Version
    - Status
    - Author
    - Last Modified
    """

    @property
    def description(self) -> str:
        """Get rule description."""
        return "Validates specification file header fields"

    def __init__(self) -> None:
        """Initialize the header validation rule."""
        self._required_fields = ["Title", "Version", "Status", "Author", "Last Modified"]
        self._valid_statuses = ["Draft", "Review", "Approved", "Deprecated"]
        self._semver_pattern = re.compile(r"^\d+\.\d+\.\d+$")
        self._header_pattern = re.compile(r"^(\*?\*?)([A-Za-z\s]+?)(\*?\*?):\s*(.+)$")

    def check(self, content: str, lines: List[str], filepath: Path) -> List[LintError]:
        """Check if content has valid header.

        Args:
            content: Full content of file
            lines: List of lines in file
            filepath: File path for error reporting

        Returns:
            List of header validation errors
        """
        errors = []
        header_fields = self._extract_header_fields(lines)

        # Check for missing required fields
        for field in self._required_fields:
            if field not in header_fields:
                errors.append(
                    LintError(
                        file_path=str(filepath),
                        line_number=1,
                        severity=Severity.ERROR,
                        rule_id="header-validation",
                        message=f"Missing required header field: {field}",
                        suggestion=f"Add '{field}: <value>' to the header",
                    )
                )

        # Validate version format
        if "Version" in header_fields:
            version = header_fields["Version"]
            if not self._semver_pattern.match(version):
                errors.append(
                    LintError(
                        file_path=str(filepath),
                        line_number=self._find_line_number(lines, "Version"),
                        severity=Severity.ERROR,
                        rule_id="header-validation",
                        message=f"Invalid version format: {version} (must be SemVer: X.Y.Z)",
                        suggestion="Use semantic versioning format (e.g., 1.0.0)",
                        context=f"Version: {version}",
                    )
                )

        # Validate status value
        if "Status" in header_fields:
            status = header_fields["Status"]
            if status not in self._valid_statuses:
                errors.append(
                    LintError(
                        file_path=str(filepath),
                        line_number=self._find_line_number(lines, "Status"),
                        severity=Severity.ERROR,
                        rule_id="header-validation",
                        message=f"Invalid status: {status} (must be one of: {', '.join(self._valid_statuses)})",
                        suggestion=f"Use one of: {', '.join(self._valid_statuses)}",
                        context=f"Status: {status}",
                    )
                )

        # Validate file path matches filename
        if "File" in header_fields:
            header_file = header_fields["File"]
            actual_file = filepath.name
            if header_file != actual_file:
                errors.append(
                    LintError(
                        file_path=str(filepath),
                        line_number=self._find_line_number(lines, "File"),
                        severity=Severity.ERROR,
                        rule_id="header-validation",
                        message=f"File path in header '{header_file}' does not match actual filename '{actual_file}'",
                        suggestion=f"Update File field to: {actual_file}",
                        context=f"File: {header_file}",
                    )
                )

        return errors

    def _extract_header_fields(self, lines: List[str]) -> dict:
        """Extract header fields from file lines.

        Args:
            lines: List of lines in file

        Returns:
            Dictionary mapping field names to values
        """
        fields = {}
        in_header = True

        for line in lines:
            # Stop at first empty line or heading
            if not line.strip() or line.startswith("#"):
                in_header = False

            if not in_header:
                break

            # Try to match header field pattern
            match = self._header_pattern.match(line)
            if match:
                field_name = match.group(2).strip()
                field_value = match.group(4).strip()
                fields[field_name] = field_value

        return fields

    def _find_line_number(self, lines: List[str], field_name: str) -> int:
        """Find the line number for a header field.

        Args:
            lines: List of lines in file
            field_name: Name of field to find

        Returns:
            Line number (1-indexed)
        """
        for i, line in enumerate(lines, start=1):
            match = self._header_pattern.match(line)
            if match and match.group(2).strip() == field_name:
                return i
        return 1
