"""
Section structure validation rule.

This module implements the SectionStructureRule which validates
the structure and organization of sections in specification files.
"""

import re
from pathlib import Path
from typing import List, Set

from spec_tools.linting.rules import LintingRule
from spec_tools.models import LintError, Severity


class SectionStructureRule(LintingRule):
    """Validates section structure in specification files.

    This rule checks that:
    - Mandatory sections are present
    - Section numbering is sequential
    - Heading level hierarchy is correct (no skipping levels)

    Mandatory sections:
    - 1. Purpose and Scope
    - 2. Definitions
    - 3. Requirements
    """

    @property
    def description(self) -> str:
        """Get rule description."""
        return "Validates section structure and organization"

    def __init__(self):
        """Initialize section structure rule."""
        self._mandatory_sections = {
            "1. Purpose and Scope",
            "2. Definitions",
            "3. Requirements",
        }
        self._heading_pattern = re.compile(r"^(#{1,6})\s+(.+)$")

    def check(self, content: str, lines: List[str], filepath: Path) -> List[LintError]:
        """Check if content has valid section structure.

        Args:
            content: Full content of file
            lines: List of lines in file
            filepath: File path for error reporting

        Returns:
            List of section structure errors
        """
        errors = []
        sections = self._extract_sections(lines)

        # Check for mandatory sections
        found_sections = {section["text"] for section in sections}
        for mandatory in self._mandatory_sections:
            if mandatory not in found_sections:
                errors.append(
                    LintError(
                        file_path=str(filepath),
                        line_number=1,
                        severity=Severity.ERROR,
                        rule_id="section-structure",
                        message=f"Missing mandatory section: {mandatory}",
                        suggestion=f"Add section '{mandatory}' to the specification",
                    )
                )

        # Check section numbering for numbered sections
        numbered_sections = [s for s in sections if self._is_numbered_section(s["text"])]
        self._check_section_numbering(numbered_sections, filepath, errors)

        # Check heading level hierarchy
        self._check_heading_hierarchy(sections, filepath, errors)

        return errors

    def _extract_sections(self, lines: List[str]) -> List[dict]:
        """Extract all sections from file lines.

        Args:
            lines: List of lines in file

        Returns:
            List of section dictionaries with 'level', 'text', 'line_number'
        """
        sections = []

        for line_num, line in enumerate(lines, start=1):
            match = self._heading_pattern.match(line)
            if match:
                level = len(match.group(1))
                text = match.group(2).strip()
                sections.append(
                    {
                        "level": level,
                        "text": text,
                        "line_number": line_num,
                    }
                )

        return sections

    def _is_numbered_section(self, text: str) -> bool:
        """Check if section text starts with a number.

        Args:
            text: Section text

        Returns:
            True if section is numbered
        """
        return bool(re.match(r"^\d+\.", text))

    def _check_section_numbering(
        self, sections: List[dict], filepath: Path, errors: List[LintError]
    ) -> None:
        """Check that numbered sections are sequential.

        Args:
            sections: List of numbered sections
            filepath: File path for error reporting
            errors: List to append errors to
        """
        expected_number = 1

        for section in sections:
            match = re.match(r"^(\d+)\.", section["text"])
            if match:
                actual_number = int(match.group(1))
                if actual_number != expected_number:
                    errors.append(
                        LintError(
                            file_path=str(filepath),
                            line_number=section["line_number"],
                            severity=Severity.WARNING,
                            rule_id="section-structure",
                            message=f"Section numbering is not sequential: expected {expected_number}, found {actual_number}",
                            suggestion=f"Renumber section to {expected_number}",
                            context=section["text"],
                        )
                    )
                expected_number = actual_number + 1

    def _check_heading_hierarchy(
        self, sections: List[dict], filepath: Path, errors: List[LintError]
    ) -> None:
        """Check that heading levels follow proper hierarchy.

        Args:
            sections: List of all sections
            filepath: File path for error reporting
            errors: List to append errors to
        """
        if not sections:
            return

        # Check that first heading is level 1
        if sections[0]["level"] != 1:
            errors.append(
                LintError(
                    file_path=str(filepath),
                    line_number=sections[0]["line_number"],
                    severity=Severity.WARNING,
                    rule_id="section-structure",
                    message=f"First heading should be level 1, found level {sections[0]['level']}",
                    suggestion="Use a single # for the main heading",
                    context=sections[0]["text"],
                )
            )

        # Check for skipped heading levels
        for i in range(1, len(sections)):
            prev_level = sections[i - 1]["level"]
            curr_level = sections[i]["level"]

            # Heading level should not increase by more than 1
            if curr_level > prev_level + 1:
                errors.append(
                    LintError(
                        file_path=str(filepath),
                        line_number=sections[i]["line_number"],
                        severity=Severity.WARNING,
                        rule_id="section-structure",
                        message=f"Heading level skipped from {prev_level} to {curr_level}",
                        suggestion=f"Use heading level {prev_level + 1} instead of {curr_level}",
                        context=sections[i]["text"],
                    )
                )
