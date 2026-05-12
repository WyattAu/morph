"""
Format Command Handler

This module implements the format command for the spec-tools CLI.
"""

import sys
from pathlib import Path
from typing import Any

from spec_tools.exceptions import SpecToolsError
from spec_tools.formatting import MarkdownFormatter
from spec_tools.models import Config


def run_format_command(args: Any, config: Config) -> int:
    """
    Run the format command.

    Args:
        args: Parsed command-line arguments
        config: Configuration instance

    Returns:
        Exit code (0 for success, 1 for errors)
    """
    path = Path(args.path)

    # Validate path exists
    if not path.exists():
        print(f"Error: Path not found: {path}", file=sys.stderr)
        return 1

    # Create formatter with config
    formatter = MarkdownFormatter(config.formatting)

    # Process file or directory
    if path.is_file():
        return _format_file(formatter, path, args.check)
    elif path.is_dir():
        return _format_directory(formatter, path, args.check)
    else:
        print(f"Error: Not a file or directory: {path}", file=sys.stderr)
        return 1


def _format_file(formatter: MarkdownFormatter, filepath: Path, check_only: bool) -> int:
    """
    Format a single file.

    Args:
        formatter: MarkdownFormatter instance
        filepath: Path to the file
        check_only: If True, only check without modifying

    Returns:
        Exit code (0 for success, 1 if changes needed in check mode)
    """
    try:
        if check_only:
            # Check format without modifying
            result = formatter.check_format(filepath)

            if result.passed:
                print(f"✓ {filepath}: Properly formatted")
                return 0
            else:
                print(f"✗ {filepath}: Formatting issues found")
                for error in result.errors:
                    print(f"  Line {error.line_number}: {error.message}")
                return 1
        else:
            # Format the file
            modified = formatter.format_file(filepath)

            if modified:
                print(f"✓ {filepath}: Formatted")
                return 0
            else:
                print(f"✓ {filepath}: Already formatted")
                return 0

    except SpecToolsError as e:
        print(f"Error formatting {filepath}: {e}", file=sys.stderr)
        return 1
    except Exception as e:
        print(f"Unexpected error formatting {filepath}: {e}", file=sys.stderr)
        return 1


def _format_directory(formatter: MarkdownFormatter, directory: Path, check_only: bool) -> int:
    """
    Format all files in a directory.

    Args:
        formatter: MarkdownFormatter instance
        directory: Path to the directory
        check_only: If True, only check without modifying

    Returns:
        Exit code (0 for success, 1 if any file has issues in check mode)
    """
    try:
        # Find all markdown files
        md_files = list(directory.rglob("*.md"))

        if not md_files:
            print(f"No markdown files found in {directory}")
            return 0

        print(f"Processing {len(md_files)} file(s) in {directory}...")

        if check_only:
            # Check all files
            all_passed = True
            issues_count = 0

            for filepath in md_files:
                result = formatter.check_format(filepath)

                if result.passed:
                    print(f"✓ {filepath.relative_to(directory)}: Properly formatted")
                else:
                    print(f"✗ {filepath.relative_to(directory)}: Formatting issues found")
                    all_passed = False
                    issues_count += len(result.errors)

                    for error in result.errors:
                        print(f"  Line {error.line_number}: {error.message}")

            if all_passed:
                print("\n✓ All files properly formatted")
                return 0
            else:
                print(f"\n✗ Found {issues_count} formatting issue(s)")
                return 1
        else:
            # Format all files
            modified_count = formatter.format_directory(directory, recursive=True)

            if modified_count > 0:
                print(f"\n✓ Formatted {modified_count} file(s)")
            else:
                print("\n✓ All files already formatted")

            return 0

    except SpecToolsError as e:
        print(f"Error formatting directory: {e}", file=sys.stderr)
        return 1
    except Exception as e:
        print(f"Unexpected error formatting directory: {e}", file=sys.stderr)
        return 1
