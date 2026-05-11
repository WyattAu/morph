"""
Emphasis formatting rule.

This module implements the EmphasisNormalizationRule which normalizes
emphasis markers in markdown files, preserving LaTeX math expressions.
"""

import re
from pathlib import Path
from typing import List

from spec_tools.formatting.rules import FormattingRule
from spec_tools.models import LintError, Severity


class EmphasisNormalizationRule(FormattingRule):
    """Normalizes emphasis markers in markdown.

    This rule ensures that:
    - Italic text uses `*italic*` instead of `_italic_` (outside LaTeX)
    - Bold text uses `**bold**` instead of `__bold__` (outside LaTeX)
    - LaTeX math expressions are preserved unchanged

    The apply() method normalizes emphasis markers, while the check()
    method reports violations without modifying the content.
    """

    _PLACEHOLDER_PREFIX = "\x00MATH_BLOCK_"
    _PLACEHOLDER_SUFFIX = "\x00"

    def __init__(self, enabled: bool = True):
        """Initialize the emphasis normalization rule.

        Args:
            enabled: Whether this rule is enabled (default: True)
        """
        self.enabled = enabled
        self._math_pattern = re.compile(r"\$\$[^$]+\$\$|\$[^$]+\$")
        self._bold_underscore_pattern = re.compile(r"__([^_\n]+?)__")
        self._italic_underscore_pattern = re.compile(r"(?<!\w)_([^_\n]+?)_(?!\w)")

    def apply(self, content: str) -> str:
        """Apply emphasis normalization to content.

        Converts `_italic_` to `*italic*` and `__bold__` to `**bold**`
        outside of LaTeX math expressions.

        Args:
            content: Content to format

        Returns:
            Content with normalized emphasis markers
        """
        if not self.enabled:
            return content

        math_blocks = []
        protected_content = self._protect_math_blocks(content, math_blocks)

        protected_content = self._bold_underscore_pattern.sub(r"**\1**", protected_content)
        protected_content = self._italic_underscore_pattern.sub(r"*\1*", protected_content)

        result = self._restore_math_blocks(protected_content, math_blocks)
        return result

    def check(self, content: str, filepath: Path) -> List[LintError]:
        """Check if content complies with emphasis normalization rule.

        Reports emphasis markers that don't follow the convention
        (outside of LaTeX math expressions).

        Args:
            content: Content to check
            filepath: File path for error reporting

        Returns:
            List of emphasis marker violations
        """
        if not self.enabled:
            return []

        errors = []
        lines = content.split("\n")

        for line_num, line in enumerate(lines, start=1):
            math_blocks = []
            protected_line = self._protect_math_blocks(line, math_blocks)

            # Apply bold normalization first to avoid false italic matches
            bold_subbed = self._bold_underscore_pattern.sub(r"**\1**", protected_line)

            # Check remaining underscores for italic violations
            italic_matches = list(self._italic_underscore_pattern.finditer(bold_subbed))
            for match in italic_matches:
                errors.append(
                    LintError(
                        file_path=str(filepath),
                        line_number=line_num,
                        column_number=match.start() + 1,
                        severity=Severity.INFO,
                        rule_id="emphasis-normalization",
                        message="Italic text uses underscores instead of asterisks",
                        suggestion="Use *italic* instead of _italic_",
                        context=line,
                    )
                )

            # Check for bold with double underscores (on original protected line)
            bold_matches = list(self._bold_underscore_pattern.finditer(protected_line))
            for match in bold_matches:
                errors.append(
                    LintError(
                        file_path=str(filepath),
                        line_number=line_num,
                        column_number=match.start() + 1,
                        severity=Severity.INFO,
                        rule_id="emphasis-normalization",
                        message="Bold text uses double underscores instead of double asterisks",
                        suggestion="Use **bold** instead of __bold__",
                        context=line,
                    )
                )

        return errors

    def _protect_math_blocks(self, content: str, math_blocks: List[str]) -> str:
        """Replace LaTeX math blocks with placeholders.

        Args:
            content: Content to process
            math_blocks: List to store found math blocks

        Returns:
            Content with math blocks replaced by placeholders
        """
        def replace_math(match):
            math_blocks.append(match.group(0))
            return f"{self._PLACEHOLDER_PREFIX}{len(math_blocks) - 1}{self._PLACEHOLDER_SUFFIX}"

        return self._math_pattern.sub(replace_math, content)

    def _restore_math_blocks(self, content: str, math_blocks: List[str]) -> str:
        """Restore LaTeX math blocks from placeholders.

        Args:
            content: Content with placeholders
            math_blocks: List of math blocks to restore

        Returns:
            Content with math blocks restored
        """
        for i, math_block in enumerate(math_blocks):
            content = content.replace(f"{self._PLACEHOLDER_PREFIX}{i}{self._PLACEHOLDER_SUFFIX}", math_block)
        return content
