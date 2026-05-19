"""Additional tests for SectionExistsValidator to improve coverage."""

from pathlib import Path

from spec_tools.link_checker.validators.section_exists import SectionExistsValidator
from spec_tools.models import LinkInfo, LinkType


class TestSectionExistsValidatorCoverage:
    def test_validate_non_section_url(self):
        validator = SectionExistsValidator()
        link = LinkInfo(
            text="link",
            url="other.md",
            line_number=1,
            link_type=LinkType.SECTION,
        )
        result = validator.validate(link)
        assert result is False
        assert link.is_valid is False
        assert "Not a section reference" in link.error_message

    def test_validate_with_no_sections_provided(self):
        validator = SectionExistsValidator()
        link = LinkInfo(
            text="link",
            url="#some-section",
            line_number=1,
            link_type=LinkType.SECTION,
        )
        result = validator.validate(link)
        assert result is True
        assert link.is_valid is True
        assert link.error_message is None

    def test_validate_section_not_in_provided_set(self):
        validator = SectionExistsValidator()
        link = LinkInfo(
            text="link",
            url="#missing-section",
            line_number=1,
            link_type=LinkType.SECTION,
        )
        result = validator.validate(link, sections={"existing-section"})
        assert result is False
        assert "Section not found" in link.error_message

    def test_validate_section_in_provided_set(self):
        validator = SectionExistsValidator()
        link = LinkInfo(
            text="link",
            url="#my-section",
            line_number=1,
            link_type=LinkType.SECTION,
        )
        result = validator.validate(link, sections={"my-section"})
        assert result is True
        assert link.is_valid is True

    def test_extract_sections_caches(self, temp_dir):
        validator = SectionExistsValidator()
        filepath = temp_dir / "test.md"
        filepath.write_text("## Hello World\n", encoding="utf-8")
        first = validator.extract_sections(filepath)
        second = validator.extract_sections(filepath)
        assert first == second
        assert filepath in validator._section_cache

    def test_extract_sections_unreadable_file(self):
        validator = SectionExistsValidator()
        result = validator.extract_sections(Path("/nonexistent/path/file.md"))
        assert result == set()

    def test_clear_cache(self, temp_dir):
        validator = SectionExistsValidator()
        filepath = temp_dir / "test.md"
        filepath.write_text("## Hello World\n", encoding="utf-8")
        validator.extract_sections(filepath)
        assert len(validator._section_cache) == 1
        validator.clear_cache()
        assert len(validator._section_cache) == 0

    def test_normalize_section_id(self):
        validator = SectionExistsValidator()
        assert validator._normalize_section_id("Hello World") == "hello-world"
        assert validator._normalize_section_id("Test!@#Section") == "testsection"
        assert validator._normalize_section_id("UPPER CASE") == "upper-case"
