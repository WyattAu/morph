"""
Markdown link parser for link checker module.

This module implements MarkdownLinkParser which extracts
markdown links from specification files.
"""

import re
from pathlib import Path
from typing import List

from spec_tools.models import LinkInfo, LinkType


class MarkdownLinkParser:
    """Parses markdown links from specification files.

    This class extracts all markdown-style links from content,
    determining their type and capturing their location.

    Link types detected:
    - MARKDOWN: Link to another markdown file
    - SECTION: Link to a section within a file
    - FILE: Link to a non-markdown file
    - EXTERNAL: Link to an external URL
    """

    def __init__(self):
        """Initialize markdown link parser."""
        self._link_pattern = re.compile(r"\[([^\]]+)\]\(([^)]+)\)")
        self._external_url_pattern = re.compile(r"^(https?://|ftp://|mailto:)")

    def parse(self, content: str, filepath: Path) -> List[LinkInfo]:
        """Parse all markdown links from content.

        Args:
            content: Content to parse
            filepath: Path to the file being parsed

        Returns:
            List of LinkInfo objects for all found links
        """
        links = []
        lines = content.split("\n")

        for line_num, line in enumerate(lines, start=1):
            matches = list(self._link_pattern.finditer(line))
            for match in matches:
                text = match.group(1)
                url = match.group(2)
                column = match.start() + 1

                # Determine link type
                link_type = self._determine_link_type(url)

                links.append(
                    LinkInfo(
                        text=text,
                        url=url,
                        line_number=line_num,
                        column_number=column,
                        file_path=filepath,
                        link_type=link_type,
                        is_valid=False,  # Will be validated later
                    )
                )

        return links

    def _determine_link_type(self, url: str) -> LinkType:
        """Determine the type of a link.

        Args:
            url: Link URL

        Returns:
            LinkType enum value
        """
        # Check for external URLs
        if self._external_url_pattern.match(url):
            return LinkType.EXTERNAL

        # Check for section references
        if url.startswith("#"):
            return LinkType.SECTION

        # Check for markdown files
        if url.endswith(".md"):
            return LinkType.MARKDOWN

        # Default to file type
        return LinkType.FILE
