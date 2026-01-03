"""
Formatting rules for spec-tools package.

This module contains the abstract base class for formatting rules
and all concrete formatting rule implementations.
"""

from abc import ABC, abstractmethod
from pathlib import Path
from typing import List

from spec_tools.models import LintError


class FormattingRule(ABC):
    """Abstract base class for formatting rules.

    All formatting rules must inherit from this class and implement
    the apply() and check() methods.

    The apply() method should modify the content to comply with the rule,
    while the check() method should report violations without modifying
    the content.
    """

    @abstractmethod
    def apply(self, content: str) -> str:
        """Apply formatting rule to content.

        Args:
            content: Content to format

        Returns:
            Formatted content
        """
        pass

    @abstractmethod
    def check(self, content: str, filepath: Path) -> List[LintError]:
        """Check if content complies with this rule.

        Args:
            content: Content to check
            filepath: File path for error reporting

        Returns:
            List of formatting violations
        """
        pass


__all__ = ["FormattingRule"]
