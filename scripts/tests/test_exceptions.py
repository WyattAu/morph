"""Tests for exceptions."""

import pytest

from spec_tools.exceptions import (
    SpecToolsError,
    FormattingError,
    LintingError,
    ValidationError,
    LinkCheckError,
)


class TestSpecToolsError:
    def test_basic_message(self):
        e = SpecToolsError("test error")
        assert str(e) == "test error"
        assert e.message == "test error"
        assert e.details == {}

    def test_with_details(self):
        e = SpecToolsError("test error", details={"key": "val"})
        assert "Details:" in str(e)
        assert e.details == {"key": "val"}

    def test_catch_base(self):
        with pytest.raises(SpecToolsError):
            raise FormattingError("fmt")


class TestFormattingError:
    def test_basic(self):
        e = FormattingError("format error")
        assert str(e) == "format error"

    def test_with_file_path(self):
        e = FormattingError("format error", file_path="test.md")
        assert "test.md" in str(e)

    def test_with_line_number(self):
        e = FormattingError("format error", file_path="test.md", line_number=5)
        assert "test.md:5" in str(e)

    def test_with_details(self):
        e = FormattingError("err", file_path="f.md", details={"k": "v"})
        assert "Details:" in str(e)

    def test_file_without_line(self):
        e = FormattingError("err", file_path="f.md")
        result = str(e)
        assert result.startswith("f.md: ")


class TestLintingError:
    def test_basic(self):
        e = LintingError("lint error")
        assert str(e) == "lint error"

    def test_with_rule_id(self):
        e = LintingError("lint error", rule_id="R001")
        assert "[R001]" in str(e)

    def test_with_file_and_line(self):
        e = LintingError("err", file_path="f.md", line_number=3, rule_id="R001")
        result = str(e)
        assert "f.md:3" in result
        assert "[R001]" in result

    def test_with_details(self):
        e = LintingError("err", rule_id="R1", details={"k": "v"})
        assert "Details:" in str(e)

    def test_no_rule_id(self):
        e = LintingError("err", file_path="f.md")
        assert "[" not in str(e)


class TestValidationError:
    def test_basic(self):
        e = ValidationError("validation error")
        assert str(e) == "validation error"

    def test_with_section(self):
        e = ValidationError("err", file_path="f.md", section="Requirements")
        assert "(section: Requirements)" in str(e)

    def test_with_details(self):
        e = ValidationError("err", section="S", details={"k": "v"})
        assert "Details:" in str(e)

    def test_file_and_section(self):
        e = ValidationError("err", file_path="f.md", section="S")
        result = str(e)
        assert result.startswith("f.md (section: S): ")


class TestLinkCheckError:
    def test_basic(self):
        e = LinkCheckError("link error")
        assert str(e) == "link error"

    def test_with_link_url(self):
        e = LinkCheckError("err", link_url="http://example.com")
        assert "Link: http://example.com" in str(e)

    def test_with_file_and_line(self):
        e = LinkCheckError("err", file_path="f.md", line_number=10, link_url="x.md")
        assert "f.md:10" in str(e)
        assert "Link: x.md" in str(e)

    def test_with_details_and_link(self):
        e = LinkCheckError("err", link_url="x.md", details={"k": "v"})
        assert "Details:" in str(e)
        assert "Link: x.md" in str(e)

    def test_with_details_no_link(self):
        e = LinkCheckError("err", details={"k": "v"})
        assert "Details:" in str(e)
        assert "Link:" not in str(e)
