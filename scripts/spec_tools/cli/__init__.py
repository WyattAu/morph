"""
CLI Module for Spec Tools

This module provides the command-line interface for the spec-tools package,
including all command handlers and argument parsing.
"""

from spec_tools.cli.main import main, create_parser

__all__ = ["main", "create_parser"]
