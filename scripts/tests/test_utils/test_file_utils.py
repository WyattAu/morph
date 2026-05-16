"""Tests for file_utils."""

from pathlib import Path

import pytest

from spec_tools.exceptions import SpecToolsError
from spec_tools.utils.file_utils import (
    find_markdown_files,
    read_file_safely,
    write_file_safely,
    ensure_directory_exists,
    get_relative_path,
)


class TestFindMarkdownFiles:
    def test_recursive(self, temp_dir):
        (temp_dir / "a.md").write_text("", encoding="utf-8")
        sub = temp_dir / "sub"
        sub.mkdir()
        (sub / "b.md").write_text("", encoding="utf-8")
        (sub / "c.txt").write_text("", encoding="utf-8")
        result = find_markdown_files(temp_dir, recursive=True)
        assert len(result) == 2

    def test_non_recursive(self, temp_dir):
        (temp_dir / "a.md").write_text("", encoding="utf-8")
        sub = temp_dir / "sub"
        sub.mkdir()
        (sub / "b.md").write_text("", encoding="utf-8")
        result = find_markdown_files(temp_dir, recursive=False)
        assert len(result) == 1

    def test_directory_not_exists(self, temp_dir):
        with pytest.raises(SpecToolsError) as exc:
            find_markdown_files(temp_dir / "nope")
        assert "does not exist" in str(exc.value)

    def test_path_is_file_not_directory(self, temp_dir):
        f = temp_dir / "file.md"
        f.write_text("", encoding="utf-8")
        with pytest.raises(SpecToolsError) as exc:
            find_markdown_files(f)
        assert "not a directory" in str(exc.value)


class TestReadFileSafely:
    def test_read_ok(self, temp_dir):
        f = temp_dir / "test.md"
        f.write_text("hello", encoding="utf-8")
        assert read_file_safely(f) == "hello"

    def test_file_not_found(self, temp_dir):
        with pytest.raises(SpecToolsError) as exc:
            read_file_safely(temp_dir / "nope.md")
        assert "File not found" in str(exc.value)

    def test_permission_error(self, temp_dir):
        f = temp_dir / "nope.md"
        f.write_text("", encoding="utf-8")
        import os
        os.chmod(str(f), 0o000)
        try:
            with pytest.raises(SpecToolsError) as exc:
                read_file_safely(f)
            assert "Permission denied" in str(exc.value)
        finally:
            os.chmod(str(f), 0o644)

    def test_encoding_error(self, temp_dir):
        f = temp_dir / "bad.bin"
        f.write_bytes(b'\x80\x81\x82')
        with pytest.raises(SpecToolsError) as exc:
            read_file_safely(f)
        assert "Encoding error" in str(exc.value)

    def test_generic_exception(self, temp_dir):
        f = temp_dir / "err.md"
        f.write_text("hello", encoding="utf-8")
        from unittest.mock import patch
        with patch("builtins.open", side_effect=IOError("generic")):
            with pytest.raises(SpecToolsError) as exc:
                read_file_safely(f)
            assert "Error reading file" in str(exc.value)


class TestWriteFileSafely:
    def test_write_ok(self, temp_dir):
        f = temp_dir / "out.md"
        write_file_safely(f, "content")
        assert f.read_text(encoding="utf-8") == "content"

    def test_creates_parent_dirs(self, temp_dir):
        f = temp_dir / "a" / "b" / "out.md"
        write_file_safely(f, "nested")
        assert f.read_text(encoding="utf-8") == "nested"

    def test_permission_error(self, temp_dir):
        import os
        read_only = temp_dir / "readonly"
        read_only.mkdir()
        os.chmod(str(read_only), 0o555)
        f = read_only / "out.md"
        try:
            with pytest.raises(SpecToolsError) as exc:
                write_file_safely(f, "nope")
            assert "Permission denied" in str(exc.value)
        finally:
            os.chmod(str(read_only), 0o755)

    def test_os_error(self, temp_dir):
        f = temp_dir / "err.md"
        f.write_text("old", encoding="utf-8")
        from unittest.mock import patch
        with patch("builtins.open", side_effect=OSError("disk full")):
            with pytest.raises(SpecToolsError) as exc:
                write_file_safely(f, "new content")
            assert "Error writing file" in str(exc.value)

    def test_generic_exception(self, temp_dir):
        f = temp_dir / "err2.md"
        from unittest.mock import patch
        with patch("pathlib.Path.mkdir", side_effect=RuntimeError("mkdir fail")):
            with pytest.raises(SpecToolsError) as exc:
                write_file_safely(f, "nope")
            assert "Unexpected error writing file" in str(exc.value)

    def test_permission_error(self, temp_dir):
        import os
        read_only = temp_dir / "readonly"
        read_only.mkdir()
        os.chmod(str(read_only), 0o555)
        f = read_only / "out.md"
        try:
            with pytest.raises(SpecToolsError) as exc:
                write_file_safely(f, "nope")
            assert "Permission denied" in str(exc.value)
        finally:
            os.chmod(str(read_only), 0o755)

    def test_os_error(self, temp_dir):
        f = temp_dir / "err.md"
        f.write_text("old", encoding="utf-8")
        from unittest.mock import patch
        with patch("builtins.open", side_effect=OSError("disk full")):
            with pytest.raises(SpecToolsError) as exc:
                write_file_safely(f, "new content")
            assert "Error writing file" in str(exc.value)

    def test_generic_exception(self, temp_dir):
        f = temp_dir / "err2.md"
        from unittest.mock import patch
        with patch("pathlib.Path.mkdir", side_effect=RuntimeError("mkdir fail")):
            with pytest.raises(SpecToolsError) as exc:
                write_file_safely(f, "nope")
            assert "Unexpected error writing file" in str(exc.value)


class TestEnsureDirectoryExists:
    def test_creates_directory(self, temp_dir):
        d = temp_dir / "new" / "dir"
        ensure_directory_exists(d)
        assert d.is_dir()

    def test_existing_directory(self, temp_dir):
        ensure_directory_exists(temp_dir)
        assert temp_dir.is_dir()

    def test_permission_error(self, temp_dir):
        import os
        read_only = temp_dir / "readonly"
        read_only.mkdir()
        os.chmod(str(read_only), 0o555)
        d = read_only / "sub"
        try:
            with pytest.raises(SpecToolsError) as exc:
                ensure_directory_exists(d)
            assert "Permission denied" in str(exc.value)
        finally:
            os.chmod(str(read_only), 0o755)

    def test_os_error(self, temp_dir):
        from unittest.mock import patch
        with patch("pathlib.Path.mkdir", side_effect=OSError("os error")):
            with pytest.raises(SpecToolsError) as exc:
                ensure_directory_exists(temp_dir / "newdir")
            assert "Error creating directory" in str(exc.value)

    def test_generic_exception(self, temp_dir):
        from unittest.mock import patch
        with patch("pathlib.Path.mkdir", side_effect=RuntimeError("unexpected")):
            with pytest.raises(SpecToolsError) as exc:
                ensure_directory_exists(temp_dir / "newdir2")
            assert "Unexpected error creating directory" in str(exc.value)


class TestGetRelativePath:
    def test_relative(self, temp_dir):
        f = temp_dir / "sub" / "file.md"
        result = get_relative_path(f, temp_dir)
        assert result == Path("sub") / "file.md"

    def test_different_drive_error(self, temp_dir):
        with pytest.raises(SpecToolsError) as exc:
            get_relative_path(Path("/a/b"), Path("/c/d"))
        assert "Cannot calculate relative path" in str(exc.value)
