"""
Cross-reference validation rule.

This module implements the CrossReferenceRule which validates
cross-references in specification files.
"""

import re
from pathlib import Path
from typing import List

from spec_tools.linting.rules import LintingRule
from spec_tools.models import LintError, Severity


class CrossReferenceRule(LintingRule):
    """Validates cross-references in specification files.

    This rule checks that:
    - Markdown links point to existing files
    - Section references point to existing sections
    - External links are skipped (not validated)

    The rule validates both relative and absolute file paths,
    and checks that referenced sections exist in the target files.
    """

    @property
    def description(self) -> str:
        """Get rule description."""
        return "Validates cross-references and links"

    def __init__(self) -> None:
        """Initialize cross-reference rule."""
        self._markdown_link_pattern = re.compile(r"\[([^\]]+)\]\(([^)]+)\)")
        self._section_ref_pattern = re.compile(r"\[([^\]]+)\]\(#([^)]+)\)")
        self._external_url_pattern = re.compile(r"^(https?://|ftp://|mailto:)")

    def check(self, content: str, lines: List[str], filepath: Path) -> List[LintError]:
        """Check if content has valid cross-references.

        Args:
            content: Full content of file
            lines: List of lines in file
            filepath: File path for error reporting

        Returns:
            List of cross-reference errors
        """
        errors: list[LintError] = []

        # Find all markdown links
        links = self._extract_links(content, filepath)

        # Validate each link
        for link in links:
            self._validate_link(link, filepath, errors)

        return errors

    def _extract_links(self, content: str, filepath: Path) -> List[dict]:
        """Extract all markdown links from content.

        Args:
            content: Full content of file
            filepath: File path for error reporting

        Returns:
            List of link dictionaries
        """
        links = []
        lines = content.split("\n")

        for line_num, line in enumerate(lines, start=1):
            matches = list(self._markdown_link_pattern.finditer(line))
            for match in matches:
                text = match.group(1)
                url = match.group(2)
                column = match.start() + 1

                # Determine link type
                link_type = self._determine_link_type(url)

                links.append(
                    {
                        "text": text,
                        "url": url,
                        "line_number": line_num,
                        "column": column,
                        "type": link_type,
                    }
                )

        return links

    def _determine_link_type(self, url: str) -> str:
        """Determine the type of a link.

        Args:
            url: Link URL

        Returns:
            Link type: 'external', 'section', or 'file'
        """
        if self._external_url_pattern.match(url):
            return "external"
        elif url.startswith("#"):
            return "section"
        else:
            return "file"

    def _validate_link(self, link: dict, filepath: Path, errors: List[LintError]) -> None:
        """Validate a single link.

        Args:
            link: Link dictionary
            filepath: File path for error reporting
            errors: List to append errors to
        """
        # Skip external links
        if link["type"] == "external":
            return

        # Validate file references
        if link["type"] == "file":
            self._validate_file_reference(link, filepath, errors)

        # Validate section references
        if link["type"] == "section":
            self._validate_section_reference(link, filepath, errors)

    def _validate_file_reference(self, link: dict, filepath: Path, errors: List[LintError]) -> None:
        """Validate a file reference.

        Args:
            link: Link dictionary
            filepath: File path for error reporting
            errors: List to append errors to
        """
        url = link["url"]

        # Resolve relative path
        if not url.startswith("/"):
            target_path = filepath.parent / url
        else:
            target_path = Path(url)

        # Check if file exists
        if not target_path.exists():
            errors.append(
                LintError(
                    file_path=str(filepath),
                    line_number=link["line_number"],
                    column_number=link["column"],
                    severity=Severity.ERROR,
                    rule_id="cross-reference",
                    message=f"Broken link: file not found '{url}'",
                    suggestion=f"Check that the file exists at '{target_path}'",
                    context=f"[{link['text']}]({url})",
                )
            )

    def _validate_section_reference(self, link: dict, filepath: Path, errors: List[LintError]) -> None:
        """Validate a section reference.

        Args:
            link: Link dictionary
            filepath: File path for error reporting
            errors: List to append errors to
        """
        url = link["url"]
        section_id = url[1:]  # Remove leading #

        # Read the file and extract sections
        try:
            content = filepath.read_text(encoding="utf-8")
            sections = self._extract_sections(content)

            # Check if section exists
            if section_id not in sections:
                errors.append(
                    LintError(
                        file_path=str(filepath),
                        line_number=link["line_number"],
                        column_number=link["column"],
                        severity=Severity.ERROR,
                        rule_id="cross-reference",
                        message=f"Broken link: section not found '#{section_id}'",
                        suggestion=f"Check that section '#{section_id}' exists in the file",
                        context=f"[{link['text']}]({url})",
                    )
                )
        except Exception:
            # If we can't read the file, skip validation
            pass

    def _extract_sections(self, content: str) -> set:
        """Extract all section IDs from content.

        Args:
            content: Full content of file

        Returns:
            Set of section IDs
        """
        sections = set()
        heading_pattern = re.compile(r"^#{1,6}\s+(.+)$", re.MULTILINE)

        for match in heading_pattern.finditer(content):
            heading_text = match.group(1).strip()
            # Convert to section ID (lowercase, replace spaces with hyphens)
            section_id = heading_text.lower().replace(" ", "-")
            sections.add(section_id)

        return sections
