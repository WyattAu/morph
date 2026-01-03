"""
Linting rules for spec-tools package.

This module contains the abstract base class for linting rules
and all concrete linting rule implementations.
"""

from abc import ABC, abstractmethod
from pathlib import Path
from typing import List

from spec_tools.models import LintError


class LintingRule(ABC):
    """Abstract base class for linting rules.

    All linting rules must inherit from this class and implement
    the check() method and provide a description property.

    The check() method should analyze the content and report any
    violations of the rule without modifying the content.
    """

    @property
    @abstractmethod
    def description(self) -> str:
        """Get a description of what this rule checks.

        Returns:
            Human-readable description of the rule
        """
        pass

    @abstractmethod
    def check(self, content: str, lines: List[str], filepath: Path) -> List[LintError]:
        """Check if content complies with this rule.

        Args:
            content: Full content of the file
            lines: List of lines in the file
            filepath: File path for error reporting

        Returns:
            List of linting violations
        """
        pass


__all__ = ["LintingRule"]
