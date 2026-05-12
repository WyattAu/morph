"""
Heading formatting rule.

This module implements the HeadingSpacingRule which ensures exactly one
space after # characters in markdown headings.
"""

import re
from pathlib import Path
from typing import List

from spec_tools.formatting.rules import FormattingRule
from spec_tools.models import LintError, Severity


class HeadingSpacingRule(FormattingRule):
    """Ensures exactly one space after # characters in headings.

    This rule enforces the markdown convention that headings should have
    exactly one space between the # characters and the heading text.
    For example:
    - Correct: `# Heading`
    - Incorrect: `#Heading` or `#  Heading`

    The apply() method fixes spacing issues, while the check() method
    reports violations without modifying the content.
    """

    def __init__(self, enabled: bool = True):
        """Initialize the heading spacing rule.

        Args:
            enabled: Whether this rule is enabled (default: True)
        """
        self.enabled = enabled
        self._heading_pattern = re.compile(r"^(#{1,6})(\s*)(.*)$")

    def apply(self, content: str) -> str:
        """Apply heading spacing formatting to content.

        Ensures exactly one space after # characters in headings.

        Args:
            content: Content to format

        Returns:
            Content with corrected heading spacing
        """
        if not self.enabled:
            return content

        lines = content.split("\n")
        result = []

        for line in lines:
            match = self._heading_pattern.match(line)
            if match:
                hashes = match.group(1)
                text = match.group(3)
                # Ensure exactly one space after hashes
                result.append(f"{hashes} {text}")
            else:
                result.append(line)

        return "\n".join(result)

    def check(self, content: str, filepath: Path) -> List[LintError]:
        """Check if content complies with heading spacing rule.

        Reports headings with incorrect spacing after # characters.

        Args:
            content: Content to check
            filepath: File path for error reporting

        Returns:
            List of heading spacing violations
        """
        if not self.enabled:
            return []

        errors = []
        lines = content.split("\n")

        for line_num, line in enumerate(lines, start=1):
            match = self._heading_pattern.match(line)
            if match:
                hashes = match.group(1)
                spaces = match.group(2)
                match.group(3)

                # Check if there's no space or more than one space
                if len(spaces) != 1:
                    if len(spaces) == 0:
                        message = f"Heading missing space after {hashes}"
                        suggestion = f"Add a space after {hashes}"
                    else:
                        message = f"Heading has {len(spaces)} spaces after {hashes} (should be 1)"
                        suggestion = f"Use exactly one space after {hashes}"

                    errors.append(
                        LintError(
                            file_path=str(filepath),
                            line_number=line_num,
                            column_number=len(hashes) + 1,
                            severity=Severity.WARNING,
                            rule_id="heading-spacing",
                            message=message,
                            suggestion=suggestion,
                            context=line,
                        )
                    )

        return errors
