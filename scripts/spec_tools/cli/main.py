"""
Main CLI Entry Point for Spec Tools

This module provides the main CLI interface for the spec-tools package,
including argument parsing and command routing.
"""

import argparse
import sys
from pathlib import Path
from typing import Optional

from spec_tools.config import ConfigManager
from spec_tools.exceptions import SpecToolsError
from spec_tools.models import Config


def create_parser() -> argparse.ArgumentParser:
    """
    Create the main CLI argument parser with all subcommands.

    Returns:
        Configured ArgumentParser instance
    """
    parser = argparse.ArgumentParser(
        prog="spec-tools",
        description=(
            "Specification tools for Morph project - formatting, linting, "
            "validation, and link checking for Markdown specification files."
        ),
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  spec-tools format spec/                    # Format all spec files
  spec-tools format spec/ --check            # Check formatting without modifying
  spec-tools lint spec/ --strict             # Lint with strict mode
  spec-tools validate spec/ --check-traceability  # Validate with traceability check
  spec-tools check-links spec/               # Check all links
  spec-tools check-all spec/                 # Run all checks
  spec-tools init-config                    # Generate default config file

For more information on a specific command, use:
  spec-tools <command> --help
        """,
    )

    subparsers = parser.add_subparsers(
        dest="command",
        help="Available commands",
        metavar="COMMAND",
    )

    # Format command
    format_parser = subparsers.add_parser(
        "format",
        help="Format specification files according to convention",
        description=(
            "Format Markdown specification files according to the Morph project "
            "specification convention. This includes line length, whitespace, "
            "headings, lists, and emphasis normalization."
        ),
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    format_parser.add_argument(
        "path",
        help="File or directory to format",
    )
    format_parser.add_argument(
        "--check",
        action="store_true",
        help="Check formatting without modifying files (exit code 1 if changes needed)",
    )
    format_parser.add_argument(
        "--config",
        type=str,
        help="Path to configuration file (default: .spec-tools.yaml)",
    )

    # Lint command
    lint_parser = subparsers.add_parser(
        "lint",
        help="Lint specification files for convention compliance",
        description=(
            "Lint Markdown specification files to check compliance with the "
            "Morph project specification convention. This includes header "
            "validation, section structure, EARS pattern validation, math "
            "notation, Mermaid syntax, and cross-reference validation."
        ),
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    lint_parser.add_argument(
        "path",
        help="File or directory to lint",
    )
    lint_parser.add_argument(
        "--strict",
        action="store_true",
        help="Treat warnings as errors",
    )
    lint_parser.add_argument(
        "--rules",
        type=str,
        help="Comma-separated list of rules to run (default: all rules)",
    )
    lint_parser.add_argument(
        "--fix",
        action="store_true",
        help="Auto-fix issues where possible",
    )
    lint_parser.add_argument(
        "--config",
        type=str,
        help="Path to configuration file (default: .spec-tools.yaml)",
    )

    # Validate command
    validate_parser = subparsers.add_parser(
        "validate",
        help="Validate specification files against enhanced convention",
        description=(
            "Validate Markdown specification files against the enhanced "
            "specification convention, including traceability matrix, "
            "verification plan, risk assessment, security specs, performance "
            "specs, and maintainability specs."
        ),
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    validate_parser.add_argument(
        "path",
        help="File or directory to validate",
    )
    validate_parser.add_argument(
        "--check-traceability",
        action="store_true",
        help="Check traceability matrix",
    )
    validate_parser.add_argument(
        "--check-security",
        action="store_true",
        help="Check security specifications",
    )
    validate_parser.add_argument(
        "--check-performance",
        action="store_true",
        help="Check performance specifications",
    )
    validate_parser.add_argument(
        "--check-maintainability",
        action="store_true",
        help="Check maintainability specifications",
    )
    validate_parser.add_argument(
        "--check-risk",
        action="store_true",
        help="Check risk assessment",
    )
    validate_parser.add_argument(
        "--check-verification",
        action="store_true",
        help="Check verification plan",
    )
    validate_parser.add_argument(
        "--config",
        type=str,
        help="Path to configuration file (default: .spec-tools.yaml)",
    )

    # Check-links command
    links_parser = subparsers.add_parser(
        "check-links",
        help="Check links in specification files",
        description=(
            "Check all links in Markdown specification files, including "
            "markdown links, section references, file references, and "
            "external links. Reports broken links, orphaned sections, "
            "and duplicate links."
        ),
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    links_parser.add_argument(
        "path",
        help="File or directory to check",
    )
    links_parser.add_argument(
        "--output",
        type=str,
        help="Output file for the link report (default: stdout)",
    )
    links_parser.add_argument(
        "--format",
        choices=["text", "json"],
        default="text",
        help="Output format (default: text)",
    )
    links_parser.add_argument(
        "--config",
        type=str,
        help="Path to configuration file (default: .spec-tools.yaml)",
    )

    # Check-all command
    check_all_parser = subparsers.add_parser(
        "check-all",
        help="Run all validation checks",
        description=(
            "Run all validation checks on specification files: format check, "
            "lint, validate, and link checking. This provides comprehensive "
            "validation of specification files."
        ),
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    check_all_parser.add_argument(
        "path",
        help="File or directory to check",
    )
    check_all_parser.add_argument(
        "--strict",
        action="store_true",
        help="Treat warnings as errors in all checks",
    )
    check_all_parser.add_argument(
        "--verbose",
        action="store_true",
        help="Show detailed output for all checks",
    )
    check_all_parser.add_argument(
        "--config",
        type=str,
        help="Path to configuration file (default: .spec-tools.yaml)",
    )

    # Init-config command
    init_parser = subparsers.add_parser(
        "init-config",
        help="Initialize configuration file",
        description=(
            "Generate a configuration file for spec-tools with default or "
            "custom settings. The configuration file can be customized to "
            "suit project-specific requirements."
        ),
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    init_parser.add_argument(
        "--output",
        type=str,
        default=".spec-tools.yaml",
        help="Output file path (default: .spec-tools.yaml)",
    )
    init_parser.add_argument(
        "--template",
        choices=["minimal", "full"],
        default="full",
        help="Configuration template (default: full)",
    )

    return parser


def load_config(config_path: Optional[str]) -> Config:
    """
    Load configuration from file or use defaults.

    Args:
        config_path: Optional path to configuration file

    Returns:
        Config instance

    Raises:
        SpecToolsError: If configuration file cannot be loaded
    """
    if config_path:
        config_file = Path(config_path)
        if not config_file.exists():
            raise SpecToolsError(f"Configuration file not found: {config_path}")

        config_manager = ConfigManager()
        return config_manager.load_config(config_file)

    # Try to load default config file
    default_config = Path(".spec-tools.yaml")
    if default_config.exists():
        config_manager = ConfigManager()
        return config_manager.load_config(default_config)

    # Return default config
    return Config()


def main() -> int:
    """
    Main entry point for the CLI.

    Returns:
        Exit code (0 for success, non-zero for errors)
    """
    parser = create_parser()
    args = parser.parse_args()

    if not args.command:
        parser.print_help()
        return 0

    try:
        # Load configuration
        config_path = getattr(args, "config", None)
        config = load_config(config_path)

        # Import command handlers
        from spec_tools.cli.commands import (
            run_check_all_command,
            run_check_links_command,
            run_format_command,
            run_init_config_command,
            run_lint_command,
            run_validate_command,
        )

        # Route to appropriate command handler
        if args.command == "format":
            return run_format_command(args, config)
        elif args.command == "lint":
            return run_lint_command(args, config)
        elif args.command == "validate":
            return run_validate_command(args, config)
        elif args.command == "check-links":
            return run_check_links_command(args, config)
        elif args.command == "check-all":
            return run_check_all_command(args, config)
        elif args.command == "init-config":
            return run_init_config_command(args)
        else:
            parser.print_help()
            return 1

    except SpecToolsError as e:
        print(f"Error: {e}", file=sys.stderr)
        return 1
    except KeyboardInterrupt:
        print("\nOperation cancelled by user", file=sys.stderr)
        return 130
    except Exception as e:
        print(f"Unexpected error: {e}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())
