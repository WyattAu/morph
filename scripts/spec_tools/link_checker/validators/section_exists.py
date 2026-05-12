"""
Section existence validator for link checker module.

This module implements SectionExistsValidator which checks
if referenced sections exist in files.
"""

import re
from pathlib import Path
from typing import Set

from spec_tools.models import LinkInfo


class SectionExistsValidator:
    """Validates that referenced sections exist.

    This class checks if section references in links
    actually exist in the target file. It normalizes
    section names for comparison.

    The validator:
    - Extracts sections from target files
    - Normalizes section names (lowercase, hyphens for spaces)
    - Provides informative error messages
    """

    def __init__(self) -> None:
        """Initialize section existence validator."""
        self._heading_pattern = re.compile(r"^#{1,6}\s+(.+)$", re.MULTILINE)
        self._section_cache: dict[Path, Set[str]] = {}

    def validate(self, link: LinkInfo, sections: Set[str] | None = None) -> bool:
        """Validate that a referenced section exists.

        Args:
            link: Link information to validate
            sections: Optional set of section IDs to check against

        Returns:
            True if section exists, False otherwise
        """
        url = link.url

        # Extract section ID from URL
        if not url.startswith("#"):
            link.is_valid = False
            link.error_message = f"Not a section reference: {url}"
            return False

        section_id = url[1:]  # Remove leading #

        # Normalize section ID for comparison
        normalized_id = self._normalize_section_id(section_id)

        # Check against provided sections
        if sections is not None:
            if normalized_id not in sections:
                link.is_valid = False
                link.error_message = f"Section not found: #{section_id}"
                return False
        else:
            # No sections provided, assume valid
            link.is_valid = True
            link.error_message = None
            return True

        link.is_valid = True
        link.error_message = None
        return True

    def extract_sections(self, filepath: Path) -> Set[str]:
        """Extract all section IDs from a file.

        Args:
            filepath: Path to the file

        Returns:
            Set of normalized section IDs
        """
        # Check cache first
        if filepath in self._section_cache:
            return self._section_cache[filepath]

        try:
            content = filepath.read_text(encoding="utf-8")
            sections = set()

            for match in self._heading_pattern.finditer(content):
                heading_text = match.group(1).strip()
                # Normalize to section ID
                section_id = self._normalize_section_id(heading_text)
                sections.add(section_id)

            # Cache the result
            self._section_cache[filepath] = sections
            return sections
        except Exception:
            # If we can't read the file, return empty set
            return set()

    def _normalize_section_id(self, section_text: str) -> str:
        """Normalize section text to section ID format.

        Args:
            section_text: Raw section heading text

        Returns:
            Normalized section ID (lowercase, hyphens for spaces)
        """
        # Convert to lowercase
        normalized = section_text.lower()
        # Replace spaces with hyphens
        normalized = normalized.replace(" ", "-")
        # Remove special characters except hyphens and alphanumeric
        normalized = re.sub(r"[^a-z0-9-]", "", normalized)
        return normalized

    def clear_cache(self) -> None:
        """Clear the section cache."""
        self._section_cache.clear()
