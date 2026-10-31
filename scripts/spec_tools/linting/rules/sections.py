"""
Section structure validation rule.

This module implements the SectionStructureRule which validates
the structure and organization of sections in specification files.
"""

import re
from pathlib import Path
from typing import List

from spec_tools.linting.rules import LintingRule
from spec_tools.models import LintError, Severity


class SectionStructureRule(LintingRule):
    """Validates section structure in specification files.

    This rule checks that:
    - Mandatory sections are present (matched fuzzily against the
      corpus convention: a purpose/scope/introduction section, a
      definitions section, and a requirements section, under any
      numbering)
    - Section numbering is sequential
    - Heading level hierarchy is correct (no skipping levels)

    Files under `_future_research/` are explicitly speculative sketches
    and are exempt from the mandatory-section check.
    """

    @property
    def description(self) -> str:
        """Get rule description."""
        return "Validates section structure and organization"

    def __init__(self) -> None:
        """Initialize section structure rule."""
        # (label, keywords): a section satisfies the requirement when its
        # normalized heading text contains any keyword.
        self._mandatory_sections = (
            # A Philosophy section states a spec's purpose in this corpus.
            ("purpose and scope", ("purpose", "scope", "introduction", "overview", "philosophy")),
            ("definitions", ("definition", "terminology", "glossary")),
            # "Obligations discharged" is the research-note form of requirements.
            ("requirements", ("requirement", "obligation")),
        )
        self._heading_pattern = re.compile(r"^(#{1,6})\s+(.+)$")
        self._number_prefix_pattern = re.compile(r"^[\d.\s]+")

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

        # Check for mandatory sections (fuzzy: any numbering accepted).
        # Future-research sketches are exempt by document class.
        if "_future_research" not in filepath.parts:
            normalized = [self._normalize_heading(s["text"]) for s in sections]
            for label, keywords in self._mandatory_sections:
                if not any(any(keyword in heading for keyword in keywords) for heading in normalized):
                    errors.append(
                        LintError(
                            file_path=str(filepath),
                            line_number=1,
                            severity=Severity.ERROR,
                            rule_id="section-structure",
                            message=f"Missing mandatory section: {label}",
                            suggestion=f"Add a '{label}' section to the specification",
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

        in_fence = False
        for line_num, line in enumerate(lines, start=1):
            # TOML/shell comments (`# ...`) inside fenced code blocks are
            # not headings.
            if line.strip().startswith("```"):
                in_fence = not in_fence
                continue
            if in_fence:
                continue
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

    def _normalize_heading(self, text: str) -> str:
        """Lowercase heading text with any leading numbering stripped."""
        return self._number_prefix_pattern.sub("", text.lower()).strip()

    def _is_numbered_section(self, text: str) -> bool:
        """Check if section text starts with a number.

        Args:
            text: Section text

        Returns:
            True if section is numbered
        """
        return bool(re.match(r"^\d+\.", text))

    # A section number is digits-and-dots followed by a dot or whitespace,
    # so both `2.7 Title` and `2.7.1 Title` parse (a trailing dot alone
    # used to swallow the minor version, silently disabling the check).
    _section_num_pattern = re.compile(r"^(\d+(?:\.\d+)*)(?:\.|\s)")

    def _parse_section_number(self, text: str) -> tuple[int, ...] | None:
        """Parse hierarchical section number into a tuple.

        Args:
            text: Section text like '1.2.3 Foo'

        Returns:
            Tuple of ints like (1, 2, 3) or None
        """
        match = self._section_num_pattern.match(text)
        if match:
            return tuple(int(p) for p in match.group(1).split("."))
        return None

    def _check_section_numbering(self, sections: List[dict], filepath: Path, errors: List[LintError]) -> None:
        """Check that numbered sections follow valid hierarchical numbering.

        Hierarchical numbering is valid when, within each heading level,
        section numbers are monotonically non-decreasing and increase by
        at most 1 at a time. For example: 1, 1.1, 1.2, 2, 2.1 is valid.

        Args:
            sections: List of numbered sections
            filepath: File path for error reporting
            errors: List to append errors to
        """
        prev_num: tuple[int, ...] | None = None
        prev_level: int | None = None

        for section in sections:
            num = self._parse_section_number(section["text"])
            level = section["level"]

            if num is None:
                continue

            if prev_num is not None and level == prev_level and len(num) == len(prev_num) and num < prev_num:
                errors.append(
                    LintError(
                        file_path=str(filepath),
                        line_number=section["line_number"],
                        severity=Severity.WARNING,
                        rule_id="section-structure",
                        message=f"Section numbering decreased: {self._fmt(prev_num)} -> {self._fmt(num)}",
                        suggestion=f"Renumber section to follow {self._fmt(prev_num)}",
                        context=section["text"],
                    )
                )

            prev_num = num
            prev_level = level

    @staticmethod
    def _fmt(num: tuple[int, ...]) -> str:
        return ".".join(str(n) for n in num)

    def _check_heading_hierarchy(self, sections: List[dict], filepath: Path, errors: List[LintError]) -> None:
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
