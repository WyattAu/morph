"""
Spec Tools Package

A modular, enterprise-grade Python package for specification file management,
including formatting, linting, validation, and link checking capabilities.

This package provides tools for working with Markdown specification files
following the Morph project's specification convention.
"""

__version__ = "1.0.0"
__author__ = "Morph Project"
__license__ = "Apache-2.0"

from spec_tools.exceptions import (
    SpecToolsError,
    FormattingError,
    LintingError,
    ValidationError,
    LinkCheckError,
)

from spec_tools.models import (
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

from spec_tools.config import ConfigManager

__all__ = [
    # Version info
    "__version__",
    "__author__",
    "__license__",
    # Exceptions
    "SpecToolsError",
    "FormattingError",
    "LintingError",
    "ValidationError",
    "LinkCheckError",
    # Models
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
    # Config
    "ConfigManager",
]
