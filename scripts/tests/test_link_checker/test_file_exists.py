"""Tests for FileExistsValidator."""

from pathlib import Path

from spec_tools.link_checker.validators.file_exists import FileExistsValidator
from spec_tools.models import LinkInfo, LinkType


class TestFileExistsValidator:
    def test_init(self):
        validator = FileExistsValidator()
        assert validator is not None

    def test_validate_existing_file(self, temp_dir):
        validator = FileExistsValidator()
        filepath = temp_dir / "existing.md"
        filepath.write_text("# Existing\n", encoding="utf-8")
        link = LinkInfo(
            text="link",
            url="existing.md",
            line_number=1,
            file_path=filepath,
            link_type=LinkType.MARKDOWN,
        )
        result = validator.validate(link)
        assert result is True
        assert link.is_valid is True
        assert link.error_message is None

    def test_validate_missing_file(self, temp_dir):
        validator = FileExistsValidator()
        filepath = temp_dir / "test.md"
        filepath.write_text("", encoding="utf-8")
        link = LinkInfo(
            text="link",
            url="missing.md",
            line_number=1,
            file_path=filepath,
            link_type=LinkType.MARKDOWN,
        )
        result = validator.validate(link)
        assert result is False
        assert link.is_valid is False
        assert "File not found" in link.error_message

    def test_validate_absolute_path_not_found(self):
        validator = FileExistsValidator()
        link = LinkInfo(
            text="link",
            url="/nonexistent/path/file.md",
            line_number=1,
            file_path=Path("/some/test.md"),
            link_type=LinkType.MARKDOWN,
        )
        result = validator.validate(link)
        assert result is False
        assert link.is_valid is False

    def test_validate_absolute_path_found(self, temp_dir):
        validator = FileExistsValidator()
        filepath = temp_dir / "test.md"
        filepath.write_text("", encoding="utf-8")
        link = LinkInfo(
            text="link",
            url=str(filepath),
            line_number=1,
            file_path=Path("/some/test.md"),
            link_type=LinkType.MARKDOWN,
        )
        result = validator.validate(link)
        assert result is True
        assert link.is_valid is True

    def test_validate_batch_no_checked_files(self, temp_dir):
        validator = FileExistsValidator()
        filepath = temp_dir / "test.md"
        filepath.write_text("", encoding="utf-8")
        links = [
            LinkInfo(
                text="link1",
                url="missing.md",
                line_number=1,
                file_path=filepath,
                link_type=LinkType.MARKDOWN,
            ),
            LinkInfo(
                text="link2",
                url="missing2.md",
                line_number=2,
                file_path=filepath,
                link_type=LinkType.MARKDOWN,
            ),
        ]
        validator.validate_batch(links)
        assert links[0].is_valid is False
        assert links[1].is_valid is False

    def test_validate_batch_with_checked_files(self, temp_dir):
        validator = FileExistsValidator()
        filepath = temp_dir / "test.md"
        filepath.write_text("", encoding="utf-8")
        links = [
            LinkInfo(
                text="link1",
                url="missing.md",
                line_number=1,
                file_path=filepath,
                link_type=LinkType.MARKDOWN,
            ),
            LinkInfo(
                text="link2",
                url="missing.md",
                line_number=2,
                file_path=filepath,
                link_type=LinkType.MARKDOWN,
            ),
        ]
        checked = set()
        validator.validate_batch(links, checked)
        assert links[0].is_valid is False
        assert links[0].error_message is not None
        assert len(checked) == 1

    def test_validate_batch_file_link_type(self, temp_dir):
        validator = FileExistsValidator()
        filepath = temp_dir / "test.md"
        filepath.write_text("", encoding="utf-8")
        links = [
            LinkInfo(
                text="link",
                url="missing.txt",
                line_number=1,
                file_path=filepath,
                link_type=LinkType.FILE,
            ),
        ]
        validator.validate_batch(links)
        assert links[0].is_valid is False

    def test_validate_batch_skips_non_file_types(self, temp_dir):
        validator = FileExistsValidator()
        filepath = temp_dir / "test.md"
        filepath.write_text("", encoding="utf-8")
        links = [
            LinkInfo(
                text="link",
                url="https://example.com",
                line_number=1,
                file_path=filepath,
                link_type=LinkType.EXTERNAL,
            ),
        ]
        validator.validate_batch(links)
        assert links[0].is_valid is False

    def test_validate_batch_absolute_path(self, temp_dir):
        validator = FileExistsValidator()
        filepath = temp_dir / "test.md"
        filepath.write_text("", encoding="utf-8")
        target = temp_dir / "abs.md"
        target.write_text("", encoding="utf-8")
        links = [
            LinkInfo(
                text="link",
                url=str(target),
                line_number=1,
                file_path=filepath,
                link_type=LinkType.MARKDOWN,
            ),
        ]
        validator.validate_batch(links)
        assert links[0].is_valid is True
