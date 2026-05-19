"""Additional tests for SpecLinkChecker to improve coverage."""

from pathlib import Path
from unittest.mock import patch

import pytest

from spec_tools.link_checker.checker import SpecLinkChecker
from spec_tools.models import LinkCheckingConfig, LinkInfo, LinkType


class TestSpecLinkCheckerCoverage:
    def test_check_file_with_broken_file_link(self, temp_dir):
        config = LinkCheckingConfig()
        checker = SpecLinkChecker(config)

        content = """# Specification

See [Missing File](missing_file.md) for details.
"""
        filepath = temp_dir / "test.md"
        filepath.write_text(content, encoding="utf-8")

        result = checker.check_file(filepath)
        assert len(result.broken_links) > 0

    def test_check_file_generic_exception(self, temp_dir):
        config = LinkCheckingConfig()
        checker = SpecLinkChecker(config)

        filepath = temp_dir / "test.md"
        filepath.write_text("# test\n", encoding="utf-8")

        with patch.object(Path, "read_text", side_effect=RuntimeError("read error")):
            with pytest.raises(Exception) as exc_info:
                checker.check_file(filepath)
            assert "Error checking links" in str(exc_info.value)

    def test_check_directory_generic_exception(self, temp_dir):
        config = LinkCheckingConfig()
        checker = SpecLinkChecker(config)

        with patch.object(Path, "glob", side_effect=RuntimeError("glob error")):
            with pytest.raises(Exception) as exc_info:
                checker.check_directory(temp_dir)
            assert "Error checking links in directory" in str(exc_info.value)

    def test_validate_link_external(self):
        config = LinkCheckingConfig()
        checker = SpecLinkChecker(config)

        link = LinkInfo(
            text="link",
            url="https://example.com",
            line_number=1,
            link_type=LinkType.EXTERNAL,
        )
        assert checker.validate_link(link) is True

    def test_validate_link_section(self):
        config = LinkCheckingConfig()
        checker = SpecLinkChecker(config)

        link = LinkInfo(
            text="link",
            url="#existing-section",
            line_number=1,
            link_type=LinkType.SECTION,
        )
        assert checker.validate_link(link, sections={"existing-section"}) is True

    def test_validate_link_file_valid(self, temp_dir):
        config = LinkCheckingConfig()
        checker = SpecLinkChecker(config)

        target = temp_dir / "target.md"
        target.write_text("# target\n", encoding="utf-8")

        link = LinkInfo(
            text="link",
            url=str(target),
            line_number=1,
            link_type=LinkType.FILE,
            file_path=temp_dir,
        )
        assert checker.validate_link(link) is True

    def test_validate_link_unknown_type(self):
        config = LinkCheckingConfig()
        checker = SpecLinkChecker(config)

        link = LinkInfo(
            text="link",
            url="something",
            line_number=1,
            link_type=None,
        )
        result = checker.validate_link(link)
        assert result is False

    def test_validate_link_uses_cache(self):
        config = LinkCheckingConfig()
        checker = SpecLinkChecker(config)

        link = LinkInfo(
            text="link",
            url="https://example.com",
            line_number=1,
            link_type=LinkType.EXTERNAL,
        )
        checker.link_cache.set(link.url, True)
        result = checker.validate_link(link)
        assert result is True

    def test_clear_cache(self):
        config = LinkCheckingConfig()
        checker = SpecLinkChecker(config)
        checker.link_cache.set("test", True)
        checker.section_cache[Path("/test")] = {"section"}
        checker.clear_cache()
        assert checker.link_cache.get("test") is None
        assert len(checker.section_cache) == 0
