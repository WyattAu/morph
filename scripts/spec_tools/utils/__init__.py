"""
Utility functions for the spec_tools package.

This module provides utility functions for logging, file system operations,
and other common tasks used throughout the package.
"""

from spec_tools.utils.file_utils import (
    find_markdown_files,
    read_file_safely,
    write_file_safely,
)
from spec_tools.utils.logging_utils import setup_logging

__all__ = [
    "setup_logging",
    "find_markdown_files",
    "read_file_safely",
    "write_file_safely",
]
