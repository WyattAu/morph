"""
Mermaid diagram validation rule.

This module implements the MermaidSyntaxRule which validates
Mermaid diagram syntax in specification files.
"""

import re
from pathlib import Path
from typing import List

from spec_tools.linting.rules import LintingRule
from spec_tools.models import LintError, Severity


class MermaidSyntaxRule(LintingRule):
    """Validates Mermaid diagram syntax in specification files.

    This rule checks that:
    - Diagram type is valid (e.g., flowchart, sequence, class, etc.)
    - Mermaid blocks are properly closed
    - Parentheses and brackets are balanced

    Valid diagram types:
    - flowchart, graph, sequenceDiagram, classDiagram, stateDiagram,
    - erDiagram, gantt, pie, journey, mindmap, timeline
    """

    @property
    def description(self) -> str:
        """Get rule description."""
        return "Validates Mermaid diagram syntax"

    def __init__(self) -> None:
        """Initialize Mermaid syntax rule."""
        self._valid_diagram_types = {
            "flowchart",
            "graph",
            "sequenceDiagram",
            "classDiagram",
            "stateDiagram",
            "erDiagram",
            "gantt",
            "pie",
            "journey",
            "mindmap",
            "timeline",
        }
        self._mermaid_block_pattern = re.compile(r"```mermaid\n(.*?)\n```", re.DOTALL)

    def check(self, content: str, lines: List[str], filepath: Path) -> List[LintError]:
        """Check if content has valid Mermaid syntax.

        Args:
            content: Full content of file
            lines: List of lines in file
            filepath: File path for error reporting

        Returns:
            List of Mermaid syntax errors
        """
        errors: list[LintError] = []

        # Check for unclosed mermaid blocks
        self._check_unclosed_blocks(content, filepath, errors)

        # Find and validate all mermaid blocks
        mermaid_blocks = list(self._mermaid_block_pattern.finditer(content))
        for match in mermaid_blocks:
            block_content = match.group(1)
            block_start_line = content[: match.start()].count("\n") + 1

            # Validate diagram type
            self._validate_diagram_type(block_content, block_start_line, filepath, errors)

            # Check for balanced parentheses and brackets
            self._check_balanced_parens(block_content, block_start_line, filepath, errors)

        return errors

    def _check_unclosed_blocks(self, content: str, filepath: Path, errors: List[LintError]) -> None:
        """Check for unclosed mermaid code blocks.

        Args:
            content: Full content of file
            filepath: File path for error reporting
            errors: List to append errors to
        """
        # Count opening and closing mermaid blocks
        open_count = content.count("```mermaid")
        close_count = content.count("```")

        # If more opens than closes, we have unclosed blocks
        if open_count > close_count:
            # Find the unclosed block
            lines = content.split("\n")
            for line_num, line in enumerate(lines, start=1):
                if "```mermaid" in line:
                    errors.append(
                        LintError(
                            file_path=str(filepath),
                            line_number=line_num,
                            column_number=line.find("```mermaid") + 1,
                            severity=Severity.ERROR,
                            rule_id="mermaid-syntax",
                            message="Unclosed mermaid code block",
                            suggestion="Add closing ``` to end of mermaid block",
                            context=line,
                        )
                    )
                    break

    def _validate_diagram_type(
        self, block_content: str, start_line: int, filepath: Path, errors: List[LintError]
    ) -> None:
        """Validate the diagram type in a mermaid block.

        Args:
            block_content: Content of mermaid block
            start_line: Starting line number of block
            filepath: File path for error reporting
            errors: List to append errors to
        """
        # Extract first line (should contain diagram type)
        first_line = block_content.split("\n")[0].strip()

        # Check if it's a valid diagram type
        if first_line not in self._valid_diagram_types:
            errors.append(
                LintError(
                    file_path=str(filepath),
                    line_number=start_line,
                    severity=Severity.ERROR,
                    rule_id="mermaid-syntax",
                    message=f"Invalid or missing Mermaid diagram type: {first_line}",
                    suggestion=f"Use one of: {', '.join(sorted(self._valid_diagram_types))}",
                    context=first_line,
                )
            )

    def _check_balanced_parens(
        self, block_content: str, start_line: int, filepath: Path, errors: List[LintError]
    ) -> None:
        """Check for balanced parentheses and brackets in mermaid block.

        Args:
            block_content: Content of mermaid block
            start_line: Starting line number of block
            filepath: File path for error reporting
            errors: List to append errors to
        """
        # Check parentheses
        paren_stack = []
        for i, char in enumerate(block_content):
            if char == "(":
                paren_stack.append(("(", i))
            elif char == ")":
                if not paren_stack or paren_stack[-1][0] != "(":
                    errors.append(
                        LintError(
                            file_path=str(filepath),
                            line_number=start_line + block_content[:i].count("\n"),
                            column_number=i - block_content[:i].rfind("\n"),
                            severity=Severity.ERROR,
                            rule_id="mermaid-syntax",
                            message="Unbalanced parentheses (closing without opening)",
                            suggestion="Add opening parenthesis or remove closing parenthesis",
                            context=block_content[max(0, i - 20) : i + 20],
                        )
                    )
                else:
                    paren_stack.pop()

        # Check for unclosed parentheses
        if paren_stack:
            for _open_char, pos in paren_stack:
                errors.append(
                    LintError(
                        file_path=str(filepath),
                        line_number=start_line + block_content[:pos].count("\n"),
                        column_number=pos - block_content[:pos].rfind("\n"),
                        severity=Severity.ERROR,
                        rule_id="mermaid-syntax",
                        message="Unbalanced parentheses (opening without closing)",
                        suggestion="Add closing parenthesis or remove opening parenthesis",
                        context=block_content[max(0, pos - 20) : pos + 20],
                    )
                )

        # Check brackets
        bracket_stack = []
        for i, char in enumerate(block_content):
            if char == "[":
                bracket_stack.append(("[", i))
            elif char == "]":
                if not bracket_stack or bracket_stack[-1][0] != "[":
                    errors.append(
                        LintError(
                            file_path=str(filepath),
                            line_number=start_line + block_content[:i].count("\n"),
                            column_number=i - block_content[:i].rfind("\n"),
                            severity=Severity.ERROR,
                            rule_id="mermaid-syntax",
                            message="Unbalanced brackets (closing without opening)",
                            suggestion="Add opening bracket or remove closing bracket",
                            context=block_content[max(0, i - 20) : i + 20],
                        )
                    )
                else:
                    bracket_stack.pop()

        # Check for unclosed brackets
        if bracket_stack:
            for _open_char, pos in bracket_stack:
                errors.append(
                    LintError(
                        file_path=str(filepath),
                        line_number=start_line + block_content[:pos].count("\n"),
                        column_number=pos - block_content[:pos].rfind("\n"),
                        severity=Severity.ERROR,
                        rule_id="mermaid-syntax",
                        message="Unbalanced brackets (opening without closing)",
                        suggestion="Add closing bracket or remove opening bracket",
                        context=block_content[max(0, pos - 20) : pos + 20],
                    )
                )
