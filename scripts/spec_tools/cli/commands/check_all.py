"""
Check All Command Handler

This module implements the check-all command for the spec-tools CLI.
"""

import sys
from pathlib import Path
from typing import Any

from spec_tools.formatting import MarkdownFormatter
from spec_tools.link_checker import SpecLinkChecker
from spec_tools.linting import SpecLinter
from spec_tools.models import Config, LinkReport, ValidationResult
from spec_tools.validation import SpecValidator


def run_check_all_command(args: Any, config: Config) -> int:
    """
    Run the check-all command.

    Args:
        args: Parsed command-line arguments
        config: Configuration instance

    Returns:
        Exit code (0 for success, 1 if any check fails)
    """
    path = Path(args.path)

    # Validate path exists
    if not path.exists():
        print(f"Error: Path not found: {path}", file=sys.stderr)
        return 1

    # Update config with command-line arguments
    if args.strict:
        config.linting.strict = True

    # Create all checkers
    formatter = MarkdownFormatter(config.formatting)
    linter = SpecLinter(config.linting)
    validator = SpecValidator(config.validation)
    link_checker = SpecLinkChecker(config.link_checking)

    # Run all checks
    print(f"Running comprehensive checks on: {path}")
    print(f"{'=' * 60}\n")

    results: dict[str, Any] = {
        "format": None,
        "lint": None,
        "validate": None,
        "links": None,
    }

    # Format check
    print("1. Format Check")
    print("-" * 60)
    results["format"] = _run_format_check(formatter, path, args.verbose)
    print()

    # Lint check
    print("2. Lint Check")
    print("-" * 60)
    results["lint"] = _run_lint_check(linter, path, args.verbose)
    print()

    # Validate check
    print("3. Validation Check")
    print("-" * 60)
    results["validate"] = _run_validate_check(validator, path, args.verbose)
    print()

    # Link check
    print("4. Link Check")
    print("-" * 60)
    results["links"] = _run_link_check(link_checker, path, args.verbose)
    print()

    # Display summary
    return _display_summary(results, args.strict)


def _run_format_check(formatter: MarkdownFormatter, path: Path, verbose: bool) -> dict:
    """
    Run format check.

    Args:
        formatter: MarkdownFormatter instance
        path: Path to check
        verbose: If True, show detailed output

    Returns:
        Dictionary with check results
    """
    try:
        if path.is_file():
            result = formatter.check_format(path)
            if verbose or not result.passed:
                _display_format_result(result)
            return {
                "passed": result.passed,
                "errors": result.error_count,
                "warnings": result.warning_count,
            }
        else:
            md_files = list(path.rglob("*.md"))
            if not md_files:
                print("No markdown files found")
                return {"passed": True, "errors": 0, "warnings": 0}

            all_passed = True
            total_errors = 0
            total_warnings = 0

            for filepath in md_files:
                result = formatter.check_format(filepath)
                if not result.passed:
                    all_passed = False
                    total_errors += result.error_count
                    total_warnings += result.warning_count
                    if verbose:
                        _display_format_result(result)

            if all_passed:
                print(f"✓ All {len(md_files)} file(s) properly formatted")
            else:
                print(f"✗ Found {total_errors} error(s) and {total_warnings} warning(s)")

            return {
                "passed": all_passed,
                "errors": total_errors,
                "warnings": total_warnings,
            }
    except Exception as e:
        print(f"Error during format check: {e}", file=sys.stderr)
        return {"passed": False, "errors": 1, "warnings": 0}


def _run_lint_check(linter: SpecLinter, path: Path, verbose: bool) -> dict:
    """
    Run lint check.

    Args:
        linter: SpecLinter instance
        path: Path to check
        verbose: If True, show detailed output

    Returns:
        Dictionary with check results
    """
    try:
        if path.is_file():
            result = linter.lint_file(path)
            if verbose or not result.passed:
                _display_lint_result(result)
            return {
                "passed": result.passed,
                "errors": result.error_count,
                "warnings": result.warning_count,
            }
        else:
            results = linter.lint_directory(path, recursive=True)
            total_errors = sum(r.error_count for r in results)
            total_warnings = sum(r.warning_count for r in results)
            all_passed = all(r.passed for r in results)

            if verbose:
                for result in results:
                    _display_lint_result(result)

            if all_passed:
                print(f"✓ All {len(results)} file(s) passed linting")
            else:
                print(f"✗ Found {total_errors} error(s) and {total_warnings} warning(s)")

            return {
                "passed": all_passed,
                "errors": total_errors,
                "warnings": total_warnings,
            }
    except Exception as e:
        print(f"Error during lint check: {e}", file=sys.stderr)
        return {"passed": False, "errors": 1, "warnings": 0}


def _run_validate_check(validator: SpecValidator, path: Path, verbose: bool) -> dict:
    """
    Run validation check.

    Args:
        validator: SpecValidator instance
        path: Path to check
        verbose: If True, show detailed output

    Returns:
        Dictionary with check results
    """
    try:
        if path.is_file():
            result = validator.validate_file(path)
            if verbose or not result.passed:
                _display_validation_result(result)
            return {
                "passed": result.passed,
                "errors": result.error_count,
                "warnings": result.warning_count,
            }
        else:
            results = validator.validate_directory(path, recursive=True)
            total_errors = sum(r.error_count for r in results)
            total_warnings = sum(r.warning_count for r in results)
            all_passed = all(r.passed for r in results)

            if verbose:
                for result in results:
                    _display_validation_result(result)

            if all_passed:
                print(f"✓ All {len(results)} file(s) passed validation")
            else:
                print(f"✗ Found {total_errors} error(s) and {total_warnings} warning(s)")

            return {
                "passed": all_passed,
                "errors": total_errors,
                "warnings": total_warnings,
            }
    except Exception as e:
        print(f"Error during validation check: {e}", file=sys.stderr)
        return {"passed": False, "errors": 1, "warnings": 0}


def _run_link_check(link_checker: SpecLinkChecker, path: Path, verbose: bool) -> dict:
    """
    Run link check.

    Args:
        link_checker: SpecLinkChecker instance
        path: Path to check
        verbose: If True, show detailed output

    Returns:
        Dictionary with check results
    """
    try:
        if path.is_file():
            report = link_checker.check_file(path)
        else:
            report = link_checker.check_directory(path, recursive=True)

        if verbose or not _link_report_passed(report):
            _display_link_report(report)
        else:
            print(f"✓ All {report.valid_links}/{report.total_links} link(s) valid")

        return {
            "passed": _link_report_passed(report),
            "broken_links": len(report.broken_links),
            "orphaned_sections": len(report.orphaned_sections),
            "self_references": len(report.self_references),
        }
    except Exception as e:
        print(f"Error during link check: {e}", file=sys.stderr)
        return {"passed": False, "broken_links": 1, "orphaned_sections": 0, "self_references": 0}


def _display_format_result(result: ValidationResult) -> None:
    """Display format check result."""
    if result.passed:
        print(f"✓ {result.file_path}: Properly formatted")
    else:
        print(f"✗ {result.file_path}: Formatting issues found")
        for error in result.errors:
            print(f"  Line {error.line_number}: {error.message}")


def _display_lint_result(result: ValidationResult) -> None:
    """Display lint check result."""
    if result.passed:
        print(f"✓ {result.file_path}: No linting issues")
    else:
        print(f"✗ {result.file_path}: Linting issues found")
        for error in result.errors:
            severity_str = error.severity.value
            print(f"  Line {error.line_number} [{severity_str}] {error.rule_id}: {error.message}")


def _display_validation_result(result: ValidationResult) -> None:
    """Display validation check result."""
    if result.passed:
        print(f"✓ {result.file_path}: Validation passed")
    else:
        print(f"✗ {result.file_path}: Validation issues found")
        for error in result.errors:
            severity_str = error.severity.value
            print(f"  Line {error.line_number} [{severity_str}] {error.rule_id}: {error.message}")


def _display_link_report(report: LinkReport) -> None:
    """Display link check report."""
    print(f"Total links: {report.total_links}")
    print(f"Valid links: {report.valid_links}")
    print(f"Broken links: {len(report.broken_links)}")
    print(f"Orphaned sections: {len(report.orphaned_sections)}")
    print(f"Self references: {len(report.self_references)}")


def _link_report_passed(report: LinkReport) -> bool:
    """Check if link report passed."""
    return len(report.broken_links) == 0 and len(report.orphaned_sections) == 0 and len(report.self_references) == 0


def _display_summary(results: dict, strict: bool) -> int:
    """
    Display summary of all checks.

    Args:
        results: Dictionary with all check results
        strict: If True, treat warnings as errors

    Returns:
        Exit code (0 for success, 1 if any check fails)
    """
    print(f"{'=' * 60}")
    print("Summary:")
    print(f"{'=' * 60}")

    # Format check
    format_result = results["format"]
    format_status = "✓ PASSED" if format_result["passed"] else "✗ FAILED"
    print(f"Format Check:  {format_status} ({format_result['errors']} errors, {format_result['warnings']} warnings)")

    # Lint check
    lint_result = results["lint"]
    lint_status = "✓ PASSED" if lint_result["passed"] else "✗ FAILED"
    print(f"Lint Check:    {lint_status} ({lint_result['errors']} errors, {lint_result['warnings']} warnings)")

    # Validate check
    validate_result = results["validate"]
    validate_status = "✓ PASSED" if validate_result["passed"] else "✗ FAILED"
    print(
        f"Validation:    {validate_status} ({validate_result['errors']} errors, {validate_result['warnings']} warnings)"
    )

    # Link check
    link_result = results["links"]
    link_status = "✓ PASSED" if link_result["passed"] else "✗ FAILED"
    print(
        f"Link Check:    {link_status} ({link_result['broken_links']} broken, {link_result['orphaned_sections']} orphaned, {link_result['self_references']} self-refs)"
    )

    print(f"{'=' * 60}")

    # Determine overall result
    all_passed = all(
        [
            format_result["passed"],
            lint_result["passed"],
            validate_result["passed"],
            link_result["passed"],
        ]
    )

    if strict:
        # In strict mode, warnings are errors
        total_issues = (
            format_result["errors"]
            + format_result["warnings"]
            + lint_result["errors"]
            + lint_result["warnings"]
            + validate_result["errors"]
            + validate_result["warnings"]
            + link_result["broken_links"]
            + link_result["orphaned_sections"]
            + link_result["self_references"]
        )

        if total_issues > 0:
            print(f"✗ Overall: FAILED (strict mode - {total_issues} issue(s))")
            return 1

    if all_passed:
        print("✓ Overall: PASSED")
        return 0
    else:
        print("✗ Overall: FAILED")
        return 1
