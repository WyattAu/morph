"""Tests for CrossReferenceRule."""

from pathlib import Path

from spec_tools.linting.rules.cross_refs import CrossReferenceRule
from spec_tools.models import Severity


class TestCrossReferenceRule:
    def test_init(self):
        rule = CrossReferenceRule()
        assert rule.description == "Validates cross-references and links"

    def test_no_links(self):
        rule = CrossReferenceRule()
        content = "# No links here\n\nJust text.\n"
        lines = content.split("\n")
        errors = rule.check(content, lines, Path("test.md"))
        assert len(errors) == 0

    def test_external_link_skipped(self):
        rule = CrossReferenceRule()
        content = "See [GitHub](https://github.com) for info.\n"
        lines = content.split("\n")
        errors = rule.check(content, lines, Path("test.md"))
        assert len(errors) == 0

    def test_ftp_link_skipped(self):
        rule = CrossReferenceRule()
        content = "See [files](ftp://example.com/file) here.\n"
        lines = content.split("\n")
        errors = rule.check(content, lines, Path("test.md"))
        assert len(errors) == 0

    def test_mailto_link_skipped(self):
        rule = CrossReferenceRule()
        content = "Email [us](mailto:test@example.com).\n"
        lines = content.split("\n")
        errors = rule.check(content, lines, Path("test.md"))
        assert len(errors) == 0

    def test_broken_file_link(self, temp_dir):
        rule = CrossReferenceRule()
        content = "See [Other](other.md) for details.\n"
        filepath = temp_dir / "test.md"
        filepath.write_text(content, encoding="utf-8")
        lines = content.split("\n")
        errors = rule.check(content, lines, filepath)
        assert len(errors) == 1
        assert errors[0].severity == Severity.ERROR
        assert "Broken link" in errors[0].message
        assert "file not found" in errors[0].message

    def test_valid_file_link(self, temp_dir):
        rule = CrossReferenceRule()
        content = "See [Other](other.md) for details.\n"
        filepath = temp_dir / "test.md"
        filepath.write_text(content, encoding="utf-8")
        (temp_dir / "other.md").write_text("# Other\n", encoding="utf-8")
        lines = content.split("\n")
        errors = rule.check(content, lines, filepath)
        assert len(errors) == 0

    def test_section_link_found(self, temp_dir):
        rule = CrossReferenceRule()
        content = "See [Section](#my-section) for info.\n\n# My Section\n\nContent here.\n"
        filepath = temp_dir / "test.md"
        filepath.write_text(content, encoding="utf-8")
        lines = content.split("\n")
        errors = rule.check(content, lines, filepath)
        assert len(errors) == 0

    def test_section_link_not_found(self, temp_dir):
        rule = CrossReferenceRule()
        content = "See [Section](#non-existent) for info.\n\n# Some Other Section\n"
        filepath = temp_dir / "test.md"
        filepath.write_text(content, encoding="utf-8")
        lines = content.split("\n")
        errors = rule.check(content, lines, filepath)
        assert len(errors) == 1
        assert "section not found" in errors[0].message

    def test_extract_sections(self):
        rule = CrossReferenceRule()
        content = "# Hello World\n## Sub Section\n### Deep Section\n"
        sections = rule._extract_sections(content)
        assert "hello-world" in sections
        assert "sub-section" in sections
        assert "deep-section" in sections

    def test_determine_link_type(self):
        rule = CrossReferenceRule()
        assert rule._determine_link_type("https://example.com") == "external"
        assert rule._determine_link_type("ftp://files.com/x") == "external"
        assert rule._determine_link_type("mailto:a@b.com") == "external"
        assert rule._determine_link_type("#section") == "section"
        assert rule._determine_link_type("file.md") == "file"

    def test_multiple_links(self, temp_dir):
        rule = CrossReferenceRule()
        content = (
            "See [Ext](https://example.com) and [File](missing.md) "
            "and [Sec](#intro).\n\n# Intro\n"
        )
        filepath = temp_dir / "test.md"
        filepath.write_text(content, encoding="utf-8")
        lines = content.split("\n")
        errors = rule.check(content, lines, filepath)
        assert len(errors) == 1
        assert "file not found" in errors[0].message

    def test_absolute_file_link_not_found(self):
        rule = CrossReferenceRule()
        content = "See [file](/nonexistent/path/file.md) here.\n"
        lines = content.split("\n")
        errors = rule.check(content, lines, Path("test.md"))
        assert len(errors) == 1
        assert "file not found" in errors[0].message

    def test_file_link_with_suggestion(self, temp_dir):
        rule = CrossReferenceRule()
        content = "Link to [missing](missing_file.md).\n"
        filepath = temp_dir / "test.md"
        filepath.write_text(content, encoding="utf-8")
        lines = content.split("\n")
        errors = rule.check(content, lines, filepath)
        assert len(errors) == 1
        assert errors[0].suggestion is not None
        assert errors[0].context is not None
        assert errors[0].line_number == 1
        assert errors[0].column_number > 0

    def test_validate_link_external(self):
        rule = CrossReferenceRule()
        link = {"type": "external", "url": "https://example.com", "text": "link", "line_number": 1, "column": 1}
        errors = []
        rule._validate_link(link, Path("test.md"), errors)
        assert len(errors) == 0

    def test_validate_link_file(self, temp_dir):
        rule = CrossReferenceRule()
        filepath = temp_dir / "test.md"
        filepath.write_text("", encoding="utf-8")
        link = {"type": "file", "url": "missing.md", "text": "link", "line_number": 1, "column": 1}
        errors = []
        rule._validate_link(link, filepath, errors)
        assert len(errors) == 1

    def test_validate_link_file_exists(self, temp_dir):
        rule = CrossReferenceRule()
        filepath = temp_dir / "test.md"
        filepath.write_text("", encoding="utf-8")
        (temp_dir / "exists.md").write_text("", encoding="utf-8")
        link = {"type": "file", "url": "exists.md", "text": "link", "line_number": 1, "column": 1}
        errors = []
        rule._validate_link(link, filepath, errors)
        assert len(errors) == 0
