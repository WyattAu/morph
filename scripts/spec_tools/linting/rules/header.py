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
    - Title (taken from the leading `#` heading when no Title field exists)
    - Version
    - Status
    - Author
    - Last Modified

    Corpus convention: files start with a `# Title` heading followed by a
    bullet metadata block (``- File:``, ``- Version:``, ``- Context:``,
    ``- Status:``, ``- Last Modified:``, ``- Author:``, ``- Reviewers:``).
    A file with no metadata block at all gets one advisory warning instead
    of five errors, so that adding honest metadata stays an authoring task
    rather than a fabrication task.
    """

    @property
    def description(self) -> str:
        """Get rule description."""
        return "Validates specification file header fields"

    def __init__(self) -> None:
        """Initialize the header validation rule."""
        self._required_fields = ["Title", "Version", "Status", "Author", "Last Modified"]
        self._valid_statuses = ["Draft", "Review", "Active", "Approved", "Deprecated"]
        self._semver_pattern = re.compile(r"^\d+\.\d+\.\d+$")
        self._bullet_pattern = re.compile(r"^\s*-\s+(.+)$")
        self._heading_pattern = re.compile(r"^(#{1,6})\s+(.+)$")

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

        # No metadata block at all: one advisory warning, not five errors.
        if not header_fields:
            errors.append(
                LintError(
                    file_path=str(filepath),
                    line_number=1,
                    severity=Severity.WARNING,
                    rule_id="header-validation",
                    message="Missing metadata header block (File/Version/Status/Author/Last Modified)",
                    suggestion="Add a bullet metadata block after the title heading",
                )
            )
            return errors

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

        # Validate file path matches filename. The convention writes the
        # repo-relative path (`spec/dir/file.md`); bare filenames and
        # directory-relative paths are accepted when they name this file.
        if "File" in header_fields:
            header_file = header_fields["File"]
            actual_file = filepath.name
            if header_file != actual_file and not header_file.endswith("/" + actual_file):
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

        The leading `#` heading supplies the Title; the bullet list that
        follows it (up to the first `---` rule or `##` section) supplies
        the remaining fields. Both plain (``- Version: 1.0.0``) and
        emphasized (``- **Status:** Active``, ``* Reviewers:* x``) bullets
        are accepted.

        Args:
            lines: List of lines in file

        Returns:
            Dictionary mapping field names to values
        """
        fields: dict = {}

        # Title comes from the first H1 heading.
        for line in lines:
            match = self._heading_pattern.match(line)
            if match:
                if match.group(1) == "#":
                    fields["Title"] = match.group(2).strip()
                break

        # Metadata bullets follow the title, ending at a rule or section.
        in_block = False
        for line in lines:
            stripped = line.strip()
            if not in_block:
                if self._heading_pattern.match(line):
                    in_block = True
                continue
            if stripped in ("---", "***", "___") or stripped.startswith("## "):
                break
            bullet = self._bullet_pattern.match(line)
            if not bullet:
                continue
            parsed = self._parse_bullet_field(bullet.group(1))
            if parsed is not None:
                field_name, field_value = parsed
                fields[field_name] = field_value

        # A file whose only header content is its title has no block.
        if list(fields) == ["Title"]:
            return {}
        return fields

    def _parse_bullet_field(self, text: str) -> tuple | None:
        """Parse one metadata bullet into (name, value).

        Accepts the corpus variants: ``- File: x``, ``- File:* x``,
        ``- `File:* `x` ``, ``- **Status:** Active``. Quoted values are
        unquoted; Windows-style ``dir\\file`` separators in ``File`` are
        normalized to ``/``.

        Args:
            text: Bullet content without the leading dash.

        Returns:
            ``(name, value)`` or ``None`` when the bullet is not a field.
        """
        content = text.strip()
        # Leading emphasis markers (`` `Version:* x``, ``**Status:** x``).
        # Only the name side is stripped here; value-side markup belongs to
        # the value and is cleaned below, so a value's own backticks (as in
        # `` `File:* `x` ``) survive intact.
        if content.startswith("`"):
            content = content[1:]
        content = content.lstrip("*")
        field_match = re.match(r"^([A-Za-z][A-Za-z ]*):\*?\s*(.*)$", content)
        if not field_match:
            return None
        field_name = field_match.group(1).strip()
        field_value = self._clean_value(field_match.group(2))
        if field_name == "File":
            field_value = field_value.replace("\\", "/")
        return field_name, field_value

    @staticmethod
    def _clean_value(value: str) -> str:
        """Strip markup quotes around a metadata value.

        Removes matched quote pairs (`` `x` ``), then lone leading or
        trailing backticks left over from whole-bullet code spans.
        """
        quotes = "`\"'"
        value = value.strip().strip("*").strip()
        while len(value) >= 2 and value[0] in quotes and value[-1] == value[0]:
            value = value[1:-1].strip()
        if value.startswith("`"):
            value = value[1:].strip()
        if len(value) >= 2 and value[0].isalnum() and value.endswith("`"):
            value = value[:-1].strip()
        return value

    def _find_line_number(self, lines: List[str], field_name: str) -> int:
        """Find the line number for a header field.

        Args:
            lines: List of lines in file
            field_name: Name of field to find

        Returns:
            Line number (1-indexed)
        """
        for i, line in enumerate(lines, start=1):
            bullet = self._bullet_pattern.match(line)
            candidate = bullet.group(1) if bullet else line
            parsed = self._parse_bullet_field(candidate)
            if parsed is not None and parsed[0] == field_name:
                return i
        return 1
