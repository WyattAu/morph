"""
Whitespace formatting rule.

This module implements the TrailingWhitespaceRule which removes trailing
whitespace from all lines in markdown files.
"""

from pathlib import Path
from typing import List

from spec_tools.formatting.rules import FormattingRule
from spec_tools.models import LintError, Severity


class TrailingWhitespaceRule(FormattingRule):
    """Removes trailing whitespace from all lines.

    This rule ensures that no line ends with spaces or tabs, which is
    a common source of git diff noise and can cause issues with some
    markdown processors.

    The apply() method removes trailing whitespace from all lines,
    while the check() method reports violations without modifying
    the content.
    """

    def __init__(self, enabled: bool = True):
        """Initialize the trailing whitespace rule.

        Args:
            enabled: Whether this rule is enabled (default: True)
        """
        self.enabled = enabled

    def apply(self, content: str) -> str:
        """Apply trailing whitespace removal to content.

        Removes trailing spaces and tabs from all lines.

        Args:
            content: Content to format

        Returns:
            Content with trailing whitespace removed
        """
        if not self.enabled:
            return content

        lines = content.split("\n")
        result = [line.rstrip() for line in lines]
        return "\n".join(result)

    def check(self, content: str, filepath: Path) -> List[LintError]:
        """Check if content complies with trailing whitespace rule.

        Reports lines that have trailing whitespace.

        Args:
            content: Content to check
            filepath: File path for error reporting

        Returns:
            List of trailing whitespace violations
        """
        if not self.enabled:
            return []

        errors = []
        lines = content.split("\n")

        for line_num, line in enumerate(lines, start=1):
            stripped = line.rstrip()
            if line != stripped:
                trailing_chars = len(line) - len(stripped)
                errors.append(
                    LintError(
                        file_path=str(filepath),
                        line_number=line_num,
                        column_number=len(stripped) + 1,
                        severity=Severity.WARNING,
                        rule_id="trailing-whitespace",
                        message=f"Line has {trailing_chars} trailing whitespace character(s)",
                        suggestion="Remove trailing whitespace from the end of the line",
                        context=line,
                    )
                )

        return errors
