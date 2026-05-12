"""
Exception classes for the spec_tools package.

This module defines custom exception classes used throughout the package
for error handling and reporting.
"""

from spec_tools.exceptions.exceptions import (
    FormattingError,
    LinkCheckError,
    LintingError,
    SpecToolsError,
    ValidationError,
)

__all__ = [
    "SpecToolsError",
    "FormattingError",
    "LintingError",
    "ValidationError",
    "LinkCheckError",
]
