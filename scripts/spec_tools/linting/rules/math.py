"""
Math notation validation rule.

This module implements the MathNotationRule which validates
mathematical notation in specification files.

The rule tokenizes LaTeX math the way renderers read it:

- Fenced code blocks and inline code spans are not math (a ``$`` in
  ``$HOME`` or a price is prose, not a delimiter).
- Display math is ``$$ ... $$`` (possibly multi-line).
- Inline math is ``$ ... $`` on a single line, opened by ``$`` followed
  by a math-start character (letter, backslash, ``(``, ``{``). A lone
  ``$`` followed by anything else (``$,``, ``$5``) is treated as a
  literal dollar sign, not a delimiter.
- Inside math expressions, braces must balance (``\\{``/``\\}`` escapes
  excluded).

The rule does not validate the mathematical correctness
of expressions, only their syntax.
"""

import re
from pathlib import Path
from typing import List

from spec_tools.linting.rules import LintingRule
from spec_tools.models import LintError, Severity


class MathNotationRule(LintingRule):
    """Validates mathematical notation syntax.

    This rule checks that:
    - Inline math ($...$) has matching delimiters
    - Display math ($$...$$) has matching delimiters
    - Math expressions have balanced braces

    The rule does not validate the mathematical correctness
    of expressions, only their syntax.
    """

    @property
    def description(self) -> str:
        """Get rule description."""
        return "Validates mathematical notation syntax"

    def __init__(self) -> None:
        """Initialize math notation rule."""
        # Display math: $$ ... $$ (may span lines, non-greedy pairing)
        self._display_math_pattern = re.compile(r"\$\$(.+?)\$\$", re.DOTALL)
        # Inline math: single line, opener $ followed by a math-start
        # character, closer $ preceded by a non-space and not part of $$.
        self._inline_math_pattern = re.compile(r"(?<!\$)\$([A-Za-z\\({][^$\n]*?)(?<![\s\$])\$(?!\$)")
        # Fenced code blocks (``` ... ```) and inline code (`...`)
        self._fenced_code_pattern = re.compile(r"```.*?```", re.DOTALL)
        self._inline_code_pattern = re.compile(r"`[^`\n]*`")
        # A $ that opens math: followed by a math-start character
        self._opener_pattern = re.compile(r"\$[A-Za-z\\({]")

    def check(self, content: str, lines: List[str], filepath: Path) -> List[LintError]:
        """Check if content has valid math notation.

        Args:
            content: Full content of file
            lines: List of lines in file
            filepath: File path for error reporting

        Returns:
            List of math notation errors
        """
        errors: list[LintError] = []

        # Neutralize escaped dollars (``\$`` is a literal dollar sign, as in
        # ``$\$$`` for "the $ symbol"). Same length, so offsets survive.
        content = re.sub(r"\\\$", "  ", content)

        # Mask code: neither fences nor spans participate in math.
        # Masking preserves offsets (and therefore line numbers) by
        # replacing every non-newline character with a space.
        masked = self._mask_code(content)

        # Display math first (so $$ pairs are never read as two $ opens).
        masked = self._extract_display_math(masked, content, filepath, errors)

        # Then inline math.
        masked = self._extract_inline_math(masked, content, filepath, errors)

        # Anything left that looks like an opener is unmatched.
        self._check_unmatched(masked, content, filepath, errors)

        return errors

    def _mask_code(self, content: str) -> str:
        """Replace code spans/blocks with spaces (newlines preserved)."""

        def blank(match: re.Match) -> str:
            return "".join("\n" if ch == "\n" else " " for ch in match.group(0))

        masked = self._fenced_code_pattern.sub(blank, content)
        return self._inline_code_pattern.sub(blank, masked)

    def _blank_region(self, text: str, start: int, end: int) -> str:
        """Blank out text[start:end], preserving newlines."""
        return text[:start] + "".join("\n" if ch == "\n" else " " for ch in text[start:end]) + text[end:]

    def _line_col(self, content: str, offset: int) -> tuple:
        """Convert a character offset to (1-indexed line, column)."""
        line = content.count("\n", 0, offset) + 1
        col = offset - content.rfind("\n", 0, offset)
        return line, col

    def _extract_display_math(self, masked: str, content: str, filepath: Path, errors: List[LintError]) -> str:
        """Validate $$...$$ blocks, then blank them out of the scan."""
        for match in self._display_math_pattern.finditer(masked):
            expr = match.group(1)
            line, col = self._line_col(content, match.start())
            self._check_balanced_braces(expr, filepath, errors, line, col)
            masked = self._blank_region(masked, match.start(), match.end())
        return masked

    def _extract_inline_math(self, masked: str, content: str, filepath: Path, errors: List[LintError]) -> str:
        """Validate $...$ spans, then blank them out of the scan."""
        for match in self._inline_math_pattern.finditer(masked):
            expr = match.group(1)
            line, col = self._line_col(content, match.start())
            self._check_balanced_braces(expr, filepath, errors, line, col)
            masked = self._blank_region(masked, match.start(), match.end())
        return masked

    def _check_unmatched(self, masked: str, content: str, filepath: Path, errors: List[LintError]) -> None:
        """Flag leftover delimiters: a $$ pair fragment or a lone opener."""
        for match in re.finditer(r"\$\$", masked):
            line, col = self._line_col(content, match.start())
            errors.append(
                LintError(
                    file_path=str(filepath),
                    line_number=line,
                    column_number=col,
                    severity=Severity.ERROR,
                    rule_id="math-notation",
                    message="Unmatched display math delimiter ($$)",
                    suggestion="Ensure every $$ has a matching closing $$",
                    context=content.split("\n")[line - 1],
                )
            )
        for match in self._opener_pattern.finditer(masked):
            # Skip the second $ of a $$ pair already reported above.
            if match.start() > 0 and masked[match.start() - 1] == "$":
                continue
            line, col = self._line_col(content, match.start())
            errors.append(
                LintError(
                    file_path=str(filepath),
                    line_number=line,
                    column_number=col,
                    severity=Severity.ERROR,
                    rule_id="math-notation",
                    message="Unmatched inline math delimiter ($)",
                    suggestion="Ensure every $ has a matching closing $",
                    context=content.split("\n")[line - 1],
                )
            )

    def _check_balanced_braces(
        self,
        expr: str,
        filepath: Path,
        errors: List[LintError],
        line: int,
        col: int,
    ) -> None:
        """Check for balanced braces in one math expression.

        Backslash-escaped braces (``\\{``, ``\\}``) are literals.
        """
        unescaped = re.sub(r"\\.", "", expr)
        depth = 0
        for char in unescaped:
            if char == "{":
                depth += 1
            elif char == "}":
                if depth == 0:
                    errors.append(
                        LintError(
                            file_path=str(filepath),
                            line_number=line,
                            column_number=col,
                            severity=Severity.ERROR,
                            rule_id="math-notation",
                            message="Unbalanced braces in math expression (closing without opening)",
                            suggestion="Add opening brace or remove closing brace",
                            context=expr.strip(),
                        )
                    )
                    return
                depth -= 1
        if depth > 0:
            errors.append(
                LintError(
                    file_path=str(filepath),
                    line_number=line,
                    column_number=col,
                    severity=Severity.ERROR,
                    rule_id="math-notation",
                    message="Unbalanced braces in math expression (opening without closing)",
                    suggestion="Add closing brace or remove opening brace",
                    context=expr.strip(),
                )
            )
