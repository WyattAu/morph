"""
File reference parser for link checker module.

This module implements FileReferenceParser which extracts
file references from specification files.
"""

import re
from pathlib import Path
from typing import List

from spec_tools.models import LinkInfo, LinkType


class FileReferenceParser:
    """Parses file references from specification files.

    This class extracts file references that are not in markdown
    link format, avoiding double-counting with markdown links.

    File references detected:
    - Direct file paths (e.g., `spec/file.md`)
    - Relative paths (e.g., `../other/file.md`)
    - Absolute paths (e.g., `/path/to/file.md`)
    """

    def __init__(self) -> None:
        """Initialize file reference parser."""
        self._file_ref_pattern = re.compile(r"([a-zA-Z0-9_\-./]+\.md)")
        self._markdown_link_pattern = re.compile(r"\[([^\]]+)\]\(([^)]+)\)")

    def parse(self, content: str, filepath: Path) -> List[LinkInfo]:
        """Parse all file references from content.

        Args:
            content: Content to parse
            filepath: Path to the file being parsed

        Returns:
            List of LinkInfo objects for all found file references
        """
        links = []
        lines = content.split("\n")

        # First, find all markdown links to avoid double-counting
        markdown_link_positions = self._find_markdown_link_positions(content)

        for line_num, line in enumerate(lines, start=1):
            matches = list(self._file_ref_pattern.finditer(line))
            for match in matches:
                file_ref = match.group(1)
                column = match.start() + 1

                # Skip if this is part of a markdown link
                if self._is_in_markdown_link(line_num, column, markdown_link_positions):
                    continue

                links.append(
                    LinkInfo(
                        text=file_ref,
                        url=file_ref,
                        line_number=line_num,
                        column_number=column,
                        file_path=filepath,
                        link_type=LinkType.FILE,
                        is_valid=False,  # Will be validated later
                    )
                )

        return links

    def _find_markdown_link_positions(self, content: str) -> List[tuple]:
        """Find positions of all markdown links in content.

        Args:
            content: Content to search

        Returns:
            List of (line_number, column) tuples
        """
        positions = []
        lines = content.split("\n")

        for line_num, line in enumerate(lines, start=1):
            matches = list(self._markdown_link_pattern.finditer(line))
            for match in matches:
                column = match.start() + 1
                positions.append((line_num, column))

        return positions

    def _is_in_markdown_link(self, line_num: int, column: int, markdown_links: List[tuple]) -> bool:
        """Check if position is within a markdown link.

        Args:
            line_num: Line number to check
            column: Column number to check
            markdown_links: List of markdown link positions

        Returns:
            True if position is within a markdown link, False otherwise
        """
        for link_line, link_col in markdown_links:
            if link_line == line_num and abs(link_col - column) < 10:
                return True
        return False
