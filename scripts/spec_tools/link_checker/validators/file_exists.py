"""
File existence validator for link checker module.

This module implements FileExistsValidator which checks
if referenced files exist.
"""

from pathlib import Path
from typing import List, Set

from spec_tools.models import LinkInfo


class FileExistsValidator:
    """Validates that referenced files exist.

    This class checks if files referenced in links
    actually exist on the filesystem. It handles both
    relative and absolute paths.

    The validator:
    - Resolves relative paths from the source file location first
    - Falls back to the enclosing directory roots (spec root, then repo root)
      for references written against those roots, which is how readers of
      prose mentions resolve them
    - Checks if the target file exists
    - Provides informative error messages
    """

    def __init__(self) -> None:
        """Initialize file existence validator."""
        pass

    @staticmethod
    def candidate_paths(link: LinkInfo) -> List[Path]:
        """Candidate filesystem paths a link could resolve to.

        The first candidate is the strict markdown-link semantics: relative
        to the referring file. Later candidates walk up the enclosing
        directories, so a reference written from the repo or spec root
        (`SPEC_GAPS_AND_BASIS.md`, `language/foo_spec.md`) still resolves.

        Args:
            link: Link information to resolve

        Returns:
            Ordered list of candidate paths, most specific first
        """
        url = link.url

        if url.startswith("/"):
            return [Path(url)]

        candidates = []
        directory = link.file_path.parent
        for ancestor in (directory, *directory.parents):
            candidate = ancestor / url
            if candidate not in candidates:
                candidates.append(candidate)
        return candidates

    def validate(self, link: LinkInfo) -> bool:
        """Validate that a referenced file exists.

        Args:
            link: Link information to validate

        Returns:
            True if file exists, False otherwise
        """
        url = link.url

        if not any(candidate.exists() for candidate in self.candidate_paths(link)):
            link.is_valid = False
            link.error_message = f"File not found: {url}"
            return False

        link.is_valid = True
        link.error_message = None
        return True

    def validate_batch(self, links: list[LinkInfo], checked_files: Set[Path] | None = None) -> None:
        """Validate multiple file references.

        Args:
            links: List of links to validate
            checked_files: Optional set to track already checked files
        """
        if checked_files is None:
            checked_files = set()

        for link in links:
            if link.link_type.value in ["markdown", "file"]:
                # Resolve target path (most specific candidate)
                target_path = self.candidate_paths(link)[0]

                # Skip if already checked
                if target_path in checked_files:
                    continue

                # Validate and mark as checked
                self.validate(link)
                checked_files.add(target_path)
