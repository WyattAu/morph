"""
File existence validator for link checker module.

This module implements FileExistsValidator which checks
if referenced files exist.
"""

from pathlib import Path
from typing import Set

from spec_tools.models import LinkInfo


class FileExistsValidator:
    """Validates that referenced files exist.

    This class checks if files referenced in links
    actually exist on the filesystem. It handles both
    relative and absolute paths.

    The validator:
    - Resolves relative paths from the source file location
    - Checks if the target file exists
    - Provides informative error messages
    """

    def __init__(self) -> None:
        """Initialize file existence validator."""
        pass

    def validate(self, link: LinkInfo) -> bool:
        """Validate that a referenced file exists.

        Args:
            link: Link information to validate

        Returns:
            True if file exists, False otherwise
        """
        url = link.url

        # Resolve relative path
        if not url.startswith("/"):
            # Relative path - resolve from link's file parent
            target_path = link.file_path.parent / url
        else:
            # Absolute path
            target_path = Path(url)

        # Check if file exists
        if not target_path.exists():
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
                # Resolve target path
                if not link.url.startswith("/"):
                    target_path = link.file_path.parent / link.url
                else:
                    target_path = Path(link.url)

                # Skip if already checked
                if target_path in checked_files:
                    continue

                # Validate and mark as checked
                self.validate(link)
                checked_files.add(target_path)
