"""Additional tests for MarkdownLinkParser to improve coverage."""

from pathlib import Path

from spec_tools.link_checker.parsers.markdown_link import MarkdownLinkParser
from spec_tools.models import LinkType


class TestMarkdownLinkParserCoverage:
    def test_parse_ftp_link(self):
        parser = MarkdownLinkParser()
        content = "See [FTP](ftp://example.com/file) for details."
        links = parser.parse(content, Path("test.md"))
        assert len(links) == 1
        assert links[0].link_type == LinkType.EXTERNAL

    def test_parse_mailto_link(self):
        parser = MarkdownLinkParser()
        content = "Email [us](mailto:test@example.com)."
        links = parser.parse(content, Path("test.md"))
        assert len(links) == 1
        assert links[0].link_type == LinkType.EXTERNAL

    def test_parse_non_md_file_link(self):
        parser = MarkdownLinkParser()
        content = "See [data](data.json) for details."
        links = parser.parse(content, Path("test.md"))
        assert len(links) == 1
        assert links[0].link_type == LinkType.FILE

    def test_parse_multiple_links_on_one_line(self):
        parser = MarkdownLinkParser()
        content = "See [A](a.md) and [B](b.md) and [C](#section)."
        links = parser.parse(content, Path("test.md"))
        assert len(links) == 3

    def test_parse_empty_content(self):
        parser = MarkdownLinkParser()
        links = parser.parse("", Path("test.md"))
        assert len(links) == 0
