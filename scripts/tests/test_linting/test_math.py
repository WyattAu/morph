"""Tests for MathNotationRule."""

from pathlib import Path

from spec_tools.linting.rules.math import MathNotationRule
from spec_tools.models import Severity


class TestMathNotationRule:
    def test_init(self):
        rule = MathNotationRule()
        assert rule.description == "Validates mathematical notation syntax"

    def test_valid_inline_math(self):
        rule = MathNotationRule()
        content = "The value of $x$ is computed.\n"
        lines = content.split("\n")
        errors = rule.check(content, lines, Path("test.md"))
        assert len(errors) == 0

    def test_valid_display_math(self):
        rule = MathNotationRule()
        content = "$$x = 1$$\n"
        lines = content.split("\n")
        errors = rule.check(content, lines, Path("test.md"))
        assert len(errors) == 0

    def test_unmatched_inline_delimiter(self):
        rule = MathNotationRule()
        content = "The value of $x is unmatched.\n"
        lines = content.split("\n")
        errors = rule.check(content, lines, Path("test.md"))
        assert len(errors) == 1
        assert "Unmatched inline math delimiter" in errors[0].message
        assert errors[0].severity == Severity.ERROR

    def test_unmatched_display_delimiter(self):
        rule = MathNotationRule()
        content = "$$x = 1\n"
        lines = content.split("\n")
        errors = rule.check(content, lines, Path("test.md"))
        assert len(errors) == 1
        assert "Unmatched display math delimiter" in errors[0].message

    def test_balanced_braces_inline(self):
        rule = MathNotationRule()
        content = "The value $\\frac{a}{b}$ is computed.\n"
        lines = content.split("\n")
        errors = rule.check(content, lines, Path("test.md"))
        assert len(errors) == 0

    def test_unbalanced_braces_closing(self):
        rule = MathNotationRule()
        content = "The value $a}$ is computed.\n"
        lines = content.split("\n")
        errors = rule.check(content, lines, Path("test.md"))
        brace_errors = [e for e in errors if "braces" in e.message]
        assert len(brace_errors) >= 1
        assert "closing without opening" in brace_errors[0].message

    def test_unbalanced_braces_opening(self):
        rule = MathNotationRule()
        content = "The value ${a$ is computed.\n"
        lines = content.split("\n")
        errors = rule.check(content, lines, Path("test.md"))
        brace_errors = [e for e in errors if "braces" in e.message]
        assert len(brace_errors) >= 1
        assert "opening without closing" in brace_errors[0].message

    def test_balanced_braces_display(self):
        rule = MathNotationRule()
        content = "$$\\sum_{i=1}^{n} x_i$$\n"
        lines = content.split("\n")
        errors = rule.check(content, lines, Path("test.md"))
        assert len(errors) == 0

    def test_no_math(self):
        rule = MathNotationRule()
        content = "# Title\n\nNo math here.\n"
        lines = content.split("\n")
        errors = rule.check(content, lines, Path("test.md"))
        assert len(errors) == 0

    def test_unmatched_inline_error_details(self):
        rule = MathNotationRule()
        content = "Line with $ unmatched\n"
        lines = content.split("\n")
        errors = rule.check(content, lines, Path("test.md"))
        assert len(errors) == 1
        assert errors[0].rule_id == "math-notation"
        assert errors[0].line_number == 1
        assert errors[0].column_number > 0
        assert errors[0].suggestion is not None
        assert errors[0].context is not None

    def test_unmatched_display_error_details(self):
        rule = MathNotationRule()
        content = "$$unmatched\n"
        lines = content.split("\n")
        errors = rule.check(content, lines, Path("test.md"))
        assert len(errors) == 1
        assert errors[0].rule_id == "math-notation"
        assert errors[0].line_number == 1
        assert errors[0].column_number > 0
