"""Tests for MermaidSyntaxRule."""

from pathlib import Path

from spec_tools.linting.rules.mermaid import MermaidSyntaxRule
from spec_tools.models import Severity


class TestMermaidSyntaxRule:
    def test_init(self):
        rule = MermaidSyntaxRule()
        assert rule.description == "Validates Mermaid diagram syntax"
        assert "flowchart" in rule._valid_diagram_types
        assert "sequenceDiagram" in rule._valid_diagram_types

    def test_valid_flowchart(self):
        rule = MermaidSyntaxRule()
        content = "```mermaid\nflowchart\n    A[Start] --> B[End]\n```\n"
        lines = content.split("\n")
        errors = rule.check(content, lines, Path("test.md"))
        assert len(errors) == 0

    def test_valid_sequence_diagram(self):
        rule = MermaidSyntaxRule()
        content = "```mermaid\nsequenceDiagram\n    A->>B: Hello\n```\n"
        lines = content.split("\n")
        errors = rule.check(content, lines, Path("test.md"))
        assert len(errors) == 0

    def test_valid_class_diagram(self):
        rule = MermaidSyntaxRule()
        content = "```mermaid\nclassDiagram\n    A --> B\n```\n"
        lines = content.split("\n")
        errors = rule.check(content, lines, Path("test.md"))
        assert len(errors) == 0

    def test_invalid_diagram_type(self):
        rule = MermaidSyntaxRule()
        content = "```mermaid\nbadDiagram\n    A --> B\n```\n"
        lines = content.split("\n")
        errors = rule.check(content, lines, Path("test.md"))
        assert len(errors) == 1
        assert "Invalid or missing Mermaid diagram type" in errors[0].message

    def test_check_unclosed_blocks_not_triggered_by_design(self):
        rule = MermaidSyntaxRule()
        errors = []
        content = "```mermaid\nflowchart\n"
        rule._check_unclosed_blocks(content, Path("test.md"), errors)
        assert len(errors) == 0

        content2 = "```mermaid\nflowchart\n```\n```mermaid\nflowchart\n"
        rule._check_unclosed_blocks(content2, Path("test.md"), errors)
        assert len(errors) == 0

    def test_unbalanced_paren_closing(self):
        rule = MermaidSyntaxRule()
        content = "```mermaid\nflowchart TD\n    A) --> B\n```\n"
        lines = content.split("\n")
        errors = rule.check(content, lines, Path("test.md"))
        paren_errors = [e for e in errors if "parentheses" in e.message]
        assert len(paren_errors) >= 1
        assert "closing without opening" in paren_errors[0].message

    def test_unbalanced_paren_opening(self):
        rule = MermaidSyntaxRule()
        content = "```mermaid\nflowchart TD\n    A( --> B\n```\n"
        lines = content.split("\n")
        errors = rule.check(content, lines, Path("test.md"))
        paren_errors = [e for e in errors if "parentheses" in e.message]
        assert len(paren_errors) >= 1
        assert "opening without closing" in paren_errors[0].message

    def test_unbalanced_bracket_closing(self):
        rule = MermaidSyntaxRule()
        content = "```mermaid\nflowchart TD\n    A] --> B\n```\n"
        lines = content.split("\n")
        errors = rule.check(content, lines, Path("test.md"))
        bracket_errors = [e for e in errors if "brackets" in e.message]
        assert len(bracket_errors) >= 1
        assert "closing without opening" in bracket_errors[0].message

    def test_unbalanced_bracket_opening(self):
        rule = MermaidSyntaxRule()
        content = "```mermaid\nflowchart TD\n    A[ --> B\n```\n"
        lines = content.split("\n")
        errors = rule.check(content, lines, Path("test.md"))
        bracket_errors = [e for e in errors if "brackets" in e.message]
        assert len(bracket_errors) >= 1
        assert "opening without closing" in bracket_errors[0].message

    def test_multiple_unclosed_parens(self):
        rule = MermaidSyntaxRule()
        content = "```mermaid\nflowchart TD\n    A(( B\n```\n"
        lines = content.split("\n")
        errors = rule.check(content, lines, Path("test.md"))
        paren_errors = [e for e in errors if "parentheses" in e.message and "opening" in e.message]
        assert len(paren_errors) == 2

    def test_multiple_unclosed_brackets(self):
        rule = MermaidSyntaxRule()
        content = "```mermaid\nflowchart TD\n    A[[ B\n```\n"
        lines = content.split("\n")
        errors = rule.check(content, lines, Path("test.md"))
        bracket_errors = [e for e in errors if "brackets" in e.message and "opening" in e.message]
        assert len(bracket_errors) == 2

    def test_balanced_parens_and_brackets(self):
        rule = MermaidSyntaxRule()
        content = "```mermaid\nflowchart\n    A[Start] --> B(End)\n```\n"
        lines = content.split("\n")
        errors = rule.check(content, lines, Path("test.md"))
        assert len(errors) == 0

    def test_no_mermaid_blocks(self):
        rule = MermaidSyntaxRule()
        content = "# Title\n\nSome text without mermaid.\n"
        lines = content.split("\n")
        errors = rule.check(content, lines, Path("test.md"))
        assert len(errors) == 0

    def test_validate_diagram_type_suggestion(self):
        rule = MermaidSyntaxRule()
        content = "```mermaid\nunknownType\n```\n"
        lines = content.split("\n")
        errors = rule.check(content, lines, Path("test.md"))
        assert len(errors) == 1
        assert errors[0].suggestion is not None
        assert "flowchart" in errors[0].suggestion
