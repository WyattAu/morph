"""
Check Links Command Handler

This module implements the check-links command for the spec-tools CLI.
"""

import json
import sys
from pathlib import Path
from typing import Any

from spec_tools.link_checker import SpecLinkChecker
from spec_tools.models import Config, LinkReport


def run_check_links_command(args: Any, config: Config) -> int:
    """
    Run the check-links command.

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

    # Create link checker with config
    checker = SpecLinkChecker(config.link_checking)

    # Process file or directory
    if path.is_file():
        report = checker.check_file(path)
    elif path.is_dir():
        report = checker.check_directory(path, recursive=True)
    else:
        print(f"Error: Not a file or directory: {path}", file=sys.stderr)
        return 1

    # Display or save report
    if args.output:
        return _save_report(report, args.output, args.format)
    else:
        return _display_report(report, args.format)


def _display_report(report: LinkReport, output_format: str) -> int:
    """
    Display link checking report.

    Args:
        report: LinkReport instance
        output_format: Output format ('text' or 'json')

    Returns:
        Exit code (0 for success, 1 if issues found)
    """
    if output_format == "json":
        print(json.dumps(_report_to_dict(report), indent=2))
    else:
        _display_text_report(report)

    # Determine exit code
    has_issues = len(report.broken_links) > 0 or len(report.orphaned_sections) > 0 or len(report.self_references) > 0

    return 1 if has_issues else 0


def _display_text_report(report: LinkReport) -> None:
    """
    Display link checking report in text format.

    Args:
        report: LinkReport instance
    """
    print(f"Link Check Report for: {report.file_path}")
    print(f"{'=' * 60}")
    print(f"Total links: {report.total_links}")
    print(f"Valid links: {report.valid_links}")
    print(f"Broken links: {len(report.broken_links)}")
    print(f"Orphaned sections: {len(report.orphaned_sections)}")
    print(f"Self references: {len(report.self_references)}")

    if report.broken_links:
        print(f"\n{'=' * 60}")
        print("Broken Links:")
        for link in report.broken_links:
            print(f"  {link.file_path}:{link.line_number}")
            print(f"    Text: {link.text}")
            print(f"    URL: {link.url}")
            if link.error_message:
                print(f"    Error: {link.error_message}")

    if report.orphaned_sections:
        print(f"\n{'=' * 60}")
        print("Orphaned Sections:")
        for link in report.orphaned_sections:
            print(f"  {link.file_path}:{link.line_number}")
            print(f"    Text: {link.text}")
            print(f"    URL: {link.url}")
            if link.error_message:
                print(f"    Error: {link.error_message}")

    if report.self_references:
        print(f"\n{'=' * 60}")
        print("Self References:")
        for link in report.self_references:
            print(f"  {link.file_path}:{link.line_number}")
            print(f"    Text: {link.text}")
            print(f"    URL: {link.url}")

    if report.duplicate_links:
        print(f"\n{'=' * 60}")
        print("Duplicate Links:")
        for link_tuple in report.duplicate_links:
            print(f"  {link_tuple[0]} appears {link_tuple[1]} times")


def _save_report(report: LinkReport, output_path: str, output_format: str) -> int:
    """
    Save link checking report to file.

    Args:
        report: LinkReport instance
        output_path: Path to output file
        output_format: Output format ('text' or 'json')

    Returns:
        Exit code (0 for success, 1 if issues found)
    """
    try:
        output_file = Path(output_path)

        if output_format == "json":
            with open(output_file, "w", encoding="utf-8") as f:
                json.dump(_report_to_dict(report), f, indent=2)
        else:
            with open(output_file, "w", encoding="utf-8") as f:
                # Capture text output
                import io
                from contextlib import redirect_stdout

                output_buffer = io.StringIO()
                with redirect_stdout(output_buffer):
                    _display_text_report(report)

                f.write(output_buffer.getvalue())

        print(f"Report saved to: {output_path}")

        # Determine exit code
        has_issues = (
            len(report.broken_links) > 0 or len(report.orphaned_sections) > 0 or len(report.self_references) > 0
        )

        return 1 if has_issues else 0

    except Exception as e:
        print(f"Error saving report: {e}", file=sys.stderr)
        return 1


def _report_to_dict(report: LinkReport) -> dict:
    """
    Convert LinkReport to dictionary for JSON serialization.

    Args:
        report: LinkReport instance

    Returns:
        Dictionary representation of the report
    """
    return {
        "file_path": str(report.file_path),
        "total_links": report.total_links,
        "valid_links": report.valid_links,
        "broken_links": [
            {
                "text": link.text,
                "url": link.url,
                "line_number": link.line_number,
                "column_number": link.column_number,
                "file_path": str(link.file_path),
                "link_type": link.link_type.value,
                "error_message": link.error_message,
            }
            for link in report.broken_links
        ],
        "orphaned_sections": [
            {
                "text": link.text,
                "url": link.url,
                "line_number": link.line_number,
                "column_number": link.column_number,
                "file_path": str(link.file_path),
                "link_type": link.link_type.value,
                "error_message": link.error_message,
            }
            for link in report.orphaned_sections
        ],
        "self_references": [
            {
                "text": link.text,
                "url": link.url,
                "line_number": link.line_number,
                "column_number": link.column_number,
                "file_path": str(link.file_path),
                "link_type": link.link_type.value,
            }
            for link in report.self_references
        ],
        "duplicate_links": [{"url": url, "count": count} for url, count in report.duplicate_links],
    }
