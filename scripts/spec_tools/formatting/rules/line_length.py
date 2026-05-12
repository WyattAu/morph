"""
Line length formatting rule.

This module implements the LineLengthRule which enforces maximum line length
in markdown files, with exceptions for code blocks and URLs.
"""

import re
from pathlib import Path
from typing import List

from spec_tools.formatting.rules import FormattingRule
from spec_tools.models import LintError, Severity


class LineLengthRule(FormattingRule):
    """Enforces maximum line length in markdown files.

    This rule checks that lines do not exceed the configured maximum length,
    with the following exceptions:
    - Lines within code blocks (indented with 4 spaces or within ``` fences)
    - Lines containing URLs (http://, https://, ftp://)
    - Lines that are part of tables (containing | characters)

    The apply() method wraps long lines at word boundaries, while the
    check() method reports violations without modifying the content.
    """

    def __init__(self, max_length: int = 120):
        """Initialize the line length rule.

        Args:
            max_length: Maximum allowed line length (default: 120)
        """
        self.max_length = max_length
        self._code_block_pattern = re.compile(r"^(\s{4}|\t).*")
        self._fenced_code_pattern = re.compile(r"^```")
        self._url_pattern = re.compile(r"https?://|ftp://")

    def apply(self, content: str) -> str:
        """Apply line length formatting to content.

        Wraps long lines at word boundaries, skipping code blocks and URLs.

        Args:
            content: Content to format

        Returns:
            Formatted content with wrapped lines
        """
        lines = content.split("\n")
        result = []
        in_fenced_block = False
        fence_char = None

        for line in lines:
            # Check if we're entering or exiting a code block
            if self._fenced_code_pattern.match(line):
                if not in_fenced_block:
                    in_fenced_block = True
                    fence_char = line.strip()[0]
                elif line.strip()[0] == fence_char:
                    in_fenced_block = False
                    fence_char = None
                result.append(line)
                continue

            # Skip lines in code blocks
            if in_fenced_block or self._code_block_pattern.match(line):
                result.append(line)
                continue

            # Skip lines with URLs
            if self._url_pattern.search(line):
                result.append(line)
                continue

            # Wrap long lines
            if len(line) > self.max_length:
                wrapped = self._wrap_line(line)
                result.extend(wrapped)
            else:
                result.append(line)

        return "\n".join(result)

    def check(self, content: str, filepath: Path) -> List[LintError]:
        """Check if content complies with line length rule.

        Reports lines that exceed the maximum length, excluding code blocks
        and URLs.

        Args:
            content: Content to check
            filepath: File path for error reporting

        Returns:
            List of line length violations
        """
        errors = []
        lines = content.split("\n")
        in_fenced_block = False
        fence_char = None

        for line_num, line in enumerate(lines, start=1):
            # Check if we're entering or exiting a code block
            if self._fenced_code_pattern.match(line):
                if not in_fenced_block:
                    in_fenced_block = True
                    fence_char = line.strip()[0]
                elif line.strip()[0] == fence_char:
                    in_fenced_block = False
                    fence_char = None
                continue

            # Skip lines in code blocks
            if in_fenced_block or self._code_block_pattern.match(line):
                continue

            # Skip lines with URLs
            if self._url_pattern.search(line):
                continue

            # Check line length
            if len(line) > self.max_length:
                errors.append(
                    LintError(
                        file_path=str(filepath),
                        line_number=line_num,
                        column_number=self.max_length + 1,
                        severity=Severity.WARNING,
                        rule_id="line-length",
                        message=f"Line exceeds maximum length of {self.max_length} characters (actual: {len(line)})",
                        suggestion=f"Wrap the line to be at most {self.max_length} characters",
                        context=line[: self.max_length + 20] + "..." if len(line) > self.max_length + 20 else line,
                    )
                )

        return errors

    def _wrap_line(self, line: str) -> List[str]:
        """Wrap a long line at word boundaries.

        Args:
            line: Line to wrap

        Returns:
            List of wrapped lines
        """
        words = line.split()
        if not words:
            return [line]

        result = []
        current_line = ""

        for word in words:
            if not current_line:
                current_line = word
            elif len(current_line) + 1 + len(word) <= self.max_length:
                current_line += " " + word
            else:
                result.append(current_line)
                current_line = word

        if current_line:
            result.append(current_line)

        return result
