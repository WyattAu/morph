"""
Data models for the spec_tools package.

This module defines dataclasses and enums used throughout the package
for configuration, error reporting, and data structures.
"""

from spec_tools.models.models import (
    Config,
    FormattingConfig,
    LintingConfig,
    ValidationConfig,
    LinkCheckingConfig,
    OutputConfig,
    LintError,
    ValidationResult,
    LinkInfo,
    LinkReport,
    Severity,
    LinkType,
)

__all__ = [
    "Config",
    "FormattingConfig",
    "LintingConfig",
    "ValidationConfig",
    "LinkCheckingConfig",
    "OutputConfig",
    "LintError",
    "ValidationResult",
    "LinkInfo",
    "LinkReport",
    "Severity",
    "LinkType",
]
