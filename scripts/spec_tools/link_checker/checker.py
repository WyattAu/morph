"""
Specification link checker for spec-tools package.

This module implements a SpecLinkChecker class which checks
links in specification files.
"""

from pathlib import Path
from typing import Dict, Set

from spec_tools.link_checker.cache.link_cache import LinkCache
from spec_tools.link_checker.parsers.file_ref import FileReferenceParser
from spec_tools.link_checker.parsers.markdown_link import MarkdownLinkParser
from spec_tools.link_checker.validators.file_exists import FileExistsValidator
from spec_tools.link_checker.validators.section_exists import SectionExistsValidator
from spec_tools.models import LinkCheckingConfig, LinkInfo, LinkReport


class SpecLinkChecker:
    """Checks links in specification files.

    This class implements the LinkCheckerInterface and validates
    all links in specification files, including:
    - Markdown links to other files
    - Section references within files
    - File references
    - External URLs (skipped)

    The checker uses caching for performance and provides
    detailed reports of broken links.
    """

    def __init__(self, config: LinkCheckingConfig):
        """Initialize specification link checker.

        Args:
            config: Link checking configuration
        """
        self.config = config
        self.link_cache = LinkCache()
        self.markdown_parser = MarkdownLinkParser()
        self.file_ref_parser = FileReferenceParser()
        self.file_validator = FileExistsValidator()
        self.section_validator = SectionExistsValidator()
        self.section_cache: Dict[Path, Set[str]] = {}

    def check_file(self, filepath: Path) -> LinkReport:
        """Check links in a single file.

        Extracts all links from the file and validates
        each one, aggregating results into a report.

        Args:
            filepath: Path to the file to check

        Returns:
            Link report with all link issues

        Raises:
            LinkCheckError: If file cannot be read
        """
        try:
            content = filepath.read_text(encoding="utf-8")

            # Extract sections for validation
            sections = self.section_validator.extract_sections(filepath)
            self.section_cache[filepath] = sections

            # Find all links
            markdown_links = self.markdown_parser.parse(content, filepath)
            file_refs = self.file_ref_parser.parse(content, filepath)

            # Combine all links
            all_links = markdown_links + file_refs

            # Create report
            report = LinkReport(
                file_path=filepath,
                total_links=len(all_links),
            )

            # Validate each link
            for link in all_links:
                is_valid = self.validate_link(link, sections)
                link.is_valid = is_valid

                if is_valid:
                    report.valid_links += 1
                else:
                    if link.link_type == LinkType.SECTION:
                        report.orphaned_sections.append(link)
                    else:
                        report.broken_links.append(link)

            return report
        except FileNotFoundError as e:
            from spec_tools.exceptions import LinkCheckError

            raise LinkCheckError(
                f"File not found: {filepath}",
                file_path=str(filepath),
            ) from e
        except Exception as e:
            from spec_tools.exceptions import LinkCheckError

            raise LinkCheckError(
                f"Error checking links in file: {filepath}",
                file_path=str(filepath),
                details={"error": str(e)},
            ) from e

    def check_directory(
        self, directory: Path, recursive: bool = True
    ) -> LinkReport:
        """Check links in all files in a directory.

        Applies link checking to all markdown files in the specified
        directory, optionally including subdirectories.

        Args:
            directory: Path to the directory
            recursive: Whether to process subdirectories (default: True)

        Returns:
            Aggregated link report for all files

        Raises:
            LinkCheckError: If directory cannot be accessed
        """
        try:
            pattern = "**/*.md" if recursive else "*.md"
            files = list(directory.glob(pattern))

            # Create aggregated report
            aggregated_report = LinkReport(file_path=directory)

            # Check each file
            for filepath in files:
                file_report = self.check_file(filepath)
                aggregated_report.total_links += file_report.total_links
                aggregated_report.valid_links += file_report.valid_links
                aggregated_report.broken_links.extend(file_report.broken_links)
                aggregated_report.orphaned_sections.extend(file_report.orphaned_sections)

            return aggregated_report
        except Exception as e:
            from spec_tools.exceptions import LinkCheckError

            raise LinkCheckError(
                f"Error checking links in directory: {directory}",
                file_path=str(directory),
                details={"error": str(e)},
            ) from e

    def validate_link(self, link: LinkInfo, sections: Set[str] | None = None) -> bool:
        """Validate a single link.

        Checks the link against appropriate validators based on
        its type. Uses caching to avoid redundant checks.

        Args:
            link: Link information to validate
            sections: Optional set of section IDs for section validation

        Returns:
            True if link is valid, False otherwise
        """
        # Check cache first
        cached_result = self.link_cache.get(link.url)
        if cached_result is not None:
            return cached_result

        # Validate based on link type
        is_valid = False

        if link.link_type == LinkType.EXTERNAL:
            # Skip external links
            is_valid = True
        elif link.link_type == LinkType.SECTION:
            # Validate section reference
            is_valid = self.section_validator.validate(link, sections)
        elif link.link_type in [LinkType.MARKDOWN, LinkType.FILE]:
            # Validate file existence
            is_valid = self.file_validator.validate(link)
        else:
            # Unknown link type, mark as invalid
            is_valid = False

        # Cache result
        self.link_cache.set(link.url, is_valid)

        return is_valid

    def clear_cache(self) -> None:
        """Clear the link validation cache."""
        self.link_cache.clear()
        self.section_cache.clear()
