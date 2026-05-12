"""
Lint Command Handler

This module implements the lint command for the spec-tools CLI.
"""

import sys
from pathlib import Path
from typing import Any, List

from spec_tools.exceptions import SpecToolsError
from spec_tools.linting import SpecLinter
from spec_tools.models import Config, ValidationResult


def run_lint_command(args: Any, config: Config) -> int:
    """
    Run the lint command.

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

    # Update config with command-line arguments
    if args.strict:
        config.linting.strict = True

    # Create linter with config
    linter = SpecLinter(config.linting)

    # Filter rules if specified
    if args.rules:
        [r.strip() for r in args.rules.split(",")]
        # Note: This would require modifying the linter to support rule filtering
        # For now, we'll use all rules

    # Process file or directory
    if path.is_file():
        return _lint_file(linter, path, args.strict, args.fix)
    elif path.is_dir():
        return _lint_directory(linter, path, args.strict, args.fix)
    else:
        print(f"Error: Not a file or directory: {path}", file=sys.stderr)
        return 1


def _lint_file(linter: SpecLinter, filepath: Path, strict: bool, fix: bool) -> int:
    """
    Lint a single file.

    Args:
        linter: SpecLinter instance
        filepath: Path to the file
        strict: If True, treat warnings as errors
        fix: If True, auto-fix issues where possible

    Returns:
        Exit code (0 for success, 1 for errors)
    """
    try:
        result = linter.lint_file(filepath)

        if fix:
            # Note: Auto-fix functionality would be implemented here
            # For now, we just report issues
            print(f"Auto-fix not yet implemented for {filepath}")

        return _display_lint_result(result, strict)

    except SpecToolsError as e:
        print(f"Error linting {filepath}: {e}", file=sys.stderr)
        return 1
    except Exception as e:
        print(f"Unexpected error linting {filepath}: {e}", file=sys.stderr)
        return 1


def _lint_directory(linter: SpecLinter, directory: Path, strict: bool, fix: bool) -> int:
    """
    Lint all files in a directory.

    Args:
        linter: SpecLinter instance
        directory: Path to the directory
        strict: If True, treat warnings as errors
        fix: If True, auto-fix issues where possible

    Returns:
        Exit code (0 for success, 1 if any file has errors)
    """
    try:
        # Find all markdown files
        md_files = list(directory.rglob("*.md"))

        if not md_files:
            print(f"No markdown files found in {directory}")
            return 0

        print(f"Linting {len(md_files)} file(s) in {directory}...")

        # Lint all files
        results: List[ValidationResult] = linter.lint_directory(directory, recursive=True)

        # Display results
        total_errors = 0
        total_warnings = 0
        failed_files = 0

        for result in results:
            if not result.passed:
                failed_files += 1
                total_errors += result.error_count
                total_warnings += result.warning_count

        # Display individual file results
        for result in results:
            _display_lint_result(result, strict, show_summary=False)

        # Display summary
        print(f"\n{'=' * 60}")
        print("Lint Summary:")
        print(f"  Files processed: {len(results)}")
        print(f"  Files with issues: {failed_files}")
        print(f"  Errors: {total_errors}")
        print(f"  Warnings: {total_warnings}")

        if strict:
            total_issues = total_errors + total_warnings
            if total_issues > 0:
                print(f"\n✗ Linting failed with {total_issues} issue(s) (strict mode)")
                return 1

        if total_errors > 0:
            print(f"\n✗ Linting failed with {total_errors} error(s)")
            return 1
        elif total_warnings > 0:
            print(f"\n✓ Linting passed with {total_warnings} warning(s)")
            return 0
        else:
            print("\n✓ All files passed linting")
            return 0

    except SpecToolsError as e:
        print(f"Error linting directory: {e}", file=sys.stderr)
        return 1
    except Exception as e:
        print(f"Unexpected error linting directory: {e}", file=sys.stderr)
        return 1


def _display_lint_result(result: ValidationResult, strict: bool, show_summary: bool = True) -> int:
    """
    Display linting result for a file.

    Args:
        result: ValidationResult instance
        strict: If True, treat warnings as errors
        show_summary: If True, show summary line

    Returns:
        Exit code (0 for success, 1 for errors)
    """
    if result.passed:
        if show_summary:
            print(f"✓ {result.file_path}: No issues found")
        return 0

    # Display errors and warnings
    print(f"✗ {result.file_path}:")

    for error in result.errors:
        severity_str = error.severity.value
        location = f"Line {error.line_number}"
        if error.column_number > 0:
            location += f":{error.column_number}"

        print(f"  {location} [{severity_str}] {error.rule_id}: {error.message}")

        if error.suggestion:
            print(f"    Suggestion: {error.suggestion}")

    # Determine exit code
    if strict:
        # In strict mode, warnings are errors
        if result.error_count > 0 or result.warning_count > 0:
            return 1
    else:
        # In normal mode, only errors matter
        if result.error_count > 0:
            return 1

    return 0
