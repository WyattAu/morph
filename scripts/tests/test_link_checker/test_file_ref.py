"""Tests for file_ref parser."""

from pathlib import Path

from spec_tools.link_checker.parsers.file_ref import FileReferenceParser
from spec_tools.models import LinkType


class TestFileReferenceParser:
    def test_parse_bare_file_ref(self):
        parser = FileReferenceParser()
        content = "See spec/requirements.md for details.\n"
        links = parser.parse(content, Path("test.md"))
        assert len(links) == 1
        assert links[0].url == "spec/requirements.md"
        assert links[0].link_type == LinkType.FILE

    def test_parse_skips_markdown_links(self):
        parser = FileReferenceParser()
        content = "See [link](other.md) for info.\n"
        links = parser.parse(content, Path("test.md"))
        assert len(links) == 0

    def test_parse_bare_ref_not_in_link(self):
        parser = FileReferenceParser()
        content = "File: design.md and [link](other.md)\n"
        links = parser.parse(content, Path("test.md"))
        md_refs = [l for l in links if l.url == "design.md"]
        assert len(md_refs) == 1

    def test_parse_multiple_refs(self):
        parser = FileReferenceParser()
        content = "See a.md, b.md, and c.md.\n"
        links = parser.parse(content, Path("test.md"))
        assert len(links) == 3

    def test_find_markdown_link_positions(self):
        parser = FileReferenceParser()
        content = "Line1\n[link](file.md) here\nLine3\n"
        positions = parser._find_markdown_link_positions(content)
        assert len(positions) == 1
        assert positions[0] == (2, 1)

    def test_is_in_markdown_link(self):
        parser = FileReferenceParser()
        md_links = [(1, 5)]
        assert parser._is_in_markdown_link(1, 5, md_links) is True
        assert parser._is_in_markdown_link(1, 1, md_links) is True
        assert parser._is_in_markdown_link(1, 20, md_links) is False
        assert parser._is_in_markdown_link(2, 5, md_links) is False

    def test_parse_no_refs(self):
        parser = FileReferenceParser()
        content = "Just plain text here.\n"
        links = parser.parse(content, Path("test.md"))
        assert len(links) == 0
