"""
Validation checks for spec-tools package.

This module contains individual validation checks that can be applied
to specification files to ensure compliance with the specification convention.
"""

from abc import ABC, abstractmethod
from pathlib import Path
from typing import List

from spec_tools.models import LintError


class ValidationCheck(ABC):
    """Abstract base class for validation checks.

    All validation checks must inherit from this class and implement
    the validate method. This provides a consistent interface for
    running different types of validation checks on specification files.

    Attributes:
        description: Human-readable description of what this check validates
    """

    @property
    @abstractmethod
    def description(self) -> str:
        """Get a human-readable description of this check.

        Returns:
            Description of what this validation check validates
        """
        pass

    @abstractmethod
    def validate(self, content: str, filepath: Path) -> List[LintError]:
        """Validate the content of a specification file.

        Args:
            content: The content of the specification file to validate
            filepath: Path to the file being validated (for error reporting)

        Returns:
            List of validation errors found. Empty list if validation passes.
        """
        pass


__all__ = ["ValidationCheck"]
