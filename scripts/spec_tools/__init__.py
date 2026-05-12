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

from spec_tools.config import ConfigManager
from spec_tools.exceptions import (
    FormattingError,
    LinkCheckError,
    LintingError,
    SpecToolsError,
    ValidationError,
)
from spec_tools.models import (
    Config,
    FormattingConfig,
    LinkCheckingConfig,
    LinkInfo,
    LinkReport,
    LinkType,
    LintError,
    LintingConfig,
    OutputConfig,
    Severity,
    ValidationConfig,
    ValidationResult,
)

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
