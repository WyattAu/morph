"""
Math notation validation rule.

This module implements the MathNotationRule which validates
mathematical notation in specification files.
"""

import re
from pathlib import Path
from typing import List

from spec_tools.linting.rules import LintingRule
from spec_tools.models import LintError, Severity


class MathNotationRule(LintingRule):
    """Validates mathematical notation in specification files.

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

    def __init__(self):
        """Initialize math notation rule."""
        self._inline_math_pattern = re.compile(r"\$([^$]+)\$")
        self._display_math_pattern = re.compile(r"\$\$([^$]+)\$\$")

    def check(self, content: str, lines: List[str], filepath: Path) -> List[LintError]:
        """Check if content has valid math notation.

        Args:
            content: Full content of file
            lines: List of lines in file
            filepath: File path for error reporting

        Returns:
            List of math notation errors
        """
        errors = []

        # Check for matching $ delimiters
        self._check_inline_math(content, filepath, errors)

        # Check for matching $$ delimiters
        self._check_display_math(content, filepath, errors)

        # Check for balanced braces in math expressions
        self._check_balanced_braces(content, filepath, errors)

        return errors

    def _check_inline_math(
        self, content: str, filepath: Path, errors: List[LintError]
    ) -> None:
        """Check for matching inline math delimiters.

        Args:
            content: Full content of file
            filepath: File path for error reporting
            errors: List to append errors to
        """
        # Count $ delimiters
        dollar_count = content.count("$")

        # Odd number means unmatched delimiter
        if dollar_count % 2 != 0:
            # Find the line with the issue
            lines = content.split("\n")
            for line_num, line in enumerate(lines, start=1):
                if "$" in line:
                    errors.append(
                        LintError(
                            file_path=str(filepath),
                            line_number=line_num,
                            column_number=line.find("$") + 1,
                            severity=Severity.ERROR,
                            rule_id="math-notation",
                            message="Unmatched inline math delimiter ($)",
                            suggestion="Ensure every $ has a matching closing $",
                            context=line,
                        )
                    )

    def _check_display_math(
        self, content: str, filepath: Path, errors: List[LintError]
    ) -> None:
        """Check for matching display math delimiters.

        Args:
            content: Full content of file
            filepath: File path for error reporting
            errors: List to append errors to
        """
        # Count $$ delimiters
        double_dollar_count = content.count("$$")

        # Odd number means unmatched delimiter
        if double_dollar_count % 2 != 0:
            # Find the line with the issue
            lines = content.split("\n")
            for line_num, line in enumerate(lines, start=1):
                if "$$" in line:
                    errors.append(
                        LintError(
                            file_path=str(filepath),
                            line_number=line_num,
                            column_number=line.find("$$") + 1,
                            severity=Severity.ERROR,
                            rule_id="math-notation",
                            message="Unmatched display math delimiter ($$)",
                            suggestion="Ensure every $$ has a matching closing $$",
                            context=line,
                        )
                    )

    def _check_balanced_braces(
        self, content: str, filepath: Path, errors: List[LintError]
    ) -> None:
        """Check for balanced braces in math expressions.

        Args:
            content: Full content of file
            filepath: File path for error reporting
            errors: List to append errors to
        """
        # Find all math expressions
        inline_matches = list(self._inline_math_pattern.finditer(content))
        display_matches = list(self._display_math_pattern.finditer(content))

        # Check each math expression for balanced braces
        for match in inline_matches + display_matches:
            expr = match.group(1)
            line_num = content[: match.start()].count("\n") + 1

            # Check braces
            brace_stack = []
            for i, char in enumerate(expr):
                if char == "{":
                    brace_stack.append(i)
                elif char == "}":
                    if not brace_stack:
                        errors.append(
                            LintError(
                                file_path=str(filepath),
                                line_number=line_num,
                                column_number=match.start() - content[: match.start()].rfind("\n") + i + 1,
                                severity=Severity.ERROR,
                                rule_id="math-notation",
                                message="Unbalanced braces in math expression (closing without opening)",
                                suggestion="Add opening brace or remove closing brace",
                                context=expr,
                            )
                    else:
                        brace_stack.pop()

            # Check for unclosed braces
            if brace_stack:
                errors.append(
                    LintError(
                        file_path=str(filepath),
                        line_number=line_num,
                        column_number=match.start() - content[: match.start()].rfind("\n") + brace_stack[0] + 1,
                        severity=Severity.ERROR,
                        rule_id="math-notation",
                        message="Unbalanced braces in math expression (opening without closing)",
                        suggestion="Add closing brace or remove opening brace",
                        context=expr,
                    )
                )
