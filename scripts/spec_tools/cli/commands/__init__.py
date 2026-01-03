"""
CLI Commands Module

This module contains all command handlers for the spec-tools CLI.
"""

from spec_tools.cli.commands.format import run_format_command
from spec_tools.cli.commands.lint import run_lint_command
from spec_tools.cli.commands.validate import run_validate_command
from spec_tools.cli.commands.check_links import run_check_links_command
from spec_tools.cli.commands.check_all import run_check_all_command
from spec_tools.cli.commands.init_config import run_init_config_command

__all__ = [
    "run_format_command",
    "run_lint_command",
    "run_validate_command",
    "run_check_links_command",
    "run_check_all_command",
    "run_init_config_command",
]
