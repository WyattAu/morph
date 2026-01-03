"""
List formatting rule.

This module implements the ListNormalizationRule which normalizes
unordered lists to use `-` and ensures proper spacing.
"""

import re
from pathlib import Path
from typing import List

from spec_tools.formatting.rules import FormattingRule
from spec_tools.models import LintError, Severity


class ListNormalizationRule(FormattingRule):
    """Normalizes unordered list formatting.

    This rule ensures that:
    - All unordered lists use `-` as the bullet character (not `*` or `+`)
    - There is exactly one space after the bullet character
    - Nested lists are properly indented

    The apply() method normalizes list formatting, while the check()
    method reports violations without modifying the content.
    """

    def __init__(self, enabled: bool = True):
        """Initialize the list normalization rule.

        Args:
            enabled: Whether this rule is enabled (default: True)
        """
        self.enabled = enabled
        self._unordered_list_pattern = re.compile(r"^(\s*)([*+-])(\s*)(.*)$")

    def apply(self, content: str) -> str:
        """Apply list normalization to content.

        Normalizes unordered lists to use `-` with one space after.

        Args:
            content: Content to format

        Returns:
            Content with normalized list formatting
        """
        if not self.enabled:
            return content

        lines = content.split("\n")
        result = []

        for line in lines:
            match = self._unordered_list_pattern.match(line)
            if match:
                indent = match.group(1)
                bullet = match.group(2)
                spaces = match.group(3)
                text = match.group(4)

                # Normalize to `-` with one space
                result.append(f"{indent}- {text}")
            else:
                result.append(line)

        return "\n".join(result)

    def check(self, content: str, filepath: Path) -> List[LintError]:
        """Check if content complies with list normalization rule.

        Reports unordered lists that don't use `-` or have incorrect spacing.

        Args:
            content: Content to check
            filepath: File path for error reporting

        Returns:
            List of list formatting violations
        """
        if not self.enabled:
            return []

        errors = []
        lines = content.split("\n")

        for line_num, line in enumerate(lines, start=1):
            match = self._unordered_list_pattern.match(line)
            if match:
                indent = match.group(1)
                bullet = match.group(2)
                spaces = match.group(3)
                text = match.group(4)

                # Check if bullet is not `-`
                if bullet != "-":
                    errors.append(
                        LintError(
                            file_path=str(filepath),
                            line_number=line_num,
                            column_number=len(indent) + 1,
                            severity=Severity.WARNING,
                            rule_id="list-normalization",
                            message=f"Unordered list uses '{bullet}' instead of '-'",
                            suggestion="Use '-' for unordered list items",
                            context=line,
                        )
                    )

                # Check if spacing is not exactly one space
                if len(spaces) != 1:
                    if len(spaces) == 0:
                        message = f"List item missing space after '{bullet}'"
                        suggestion = f"Add a space after '{bullet}'"
                    else:
                        message = f"List item has {len(spaces)} spaces after '{bullet}' (should be 1)"
                        suggestion = f"Use exactly one space after '{bullet}'"

                    errors.append(
                        LintError(
                            file_path=str(filepath),
                            line_number=line_num,
                            column_number=len(indent) + len(bullet) + 1,
                            severity=Severity.WARNING,
                            rule_id="list-normalization",
                            message=message,
                            suggestion=suggestion,
                            context=line,
                        )
                    )

        return errors
