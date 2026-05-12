"""Tests for Lean 4 compilation verification."""

from pathlib import Path
from unittest.mock import MagicMock, patch

import pytest

from spec_tools.verification.compilation import (
    CompilationConfig,
    Lean4CompilationVerifier,
    _MemoryMonitor,
)
from spec_tools.verification.models import (
    CompilationError,
    CompilationResult,
    CompilationStatus,
)


class TestCompilationConfig:
    def test_defaults(self):
        config = CompilationConfig()
        assert config.timeout_seconds == 300
        assert config.memory_limit_mb == 4096
        assert config.clean_before_build is True
        assert config.parallel_jobs == 1


class TestLean4CompilationVerifier:
    def test_init(self):
        verifier = Lean4CompilationVerifier()
        assert verifier.config is not None

    @patch("spec_tools.verification.compilation.subprocess.run")
    @patch("spec_tools.verification.compilation._MemoryMonitor")
    def test_verify_file_success(self, mock_monitor_cls, mock_run, temp_dir):
        mock_process = MagicMock()
        mock_process.returncode = 0
        mock_process.stdout = ""
        mock_process.stderr = ""
        mock_run.return_value = mock_process

        mock_monitor = MagicMock()
        mock_monitor.exceeded_limit = False
        mock_monitor.stop.return_value = 10.0
        mock_monitor_cls.return_value = mock_monitor

        lean_file = temp_dir / "test.lean"
        lean_file.write_text("def foo : Nat := 0\n")

        config = CompilationConfig(clean_before_build=False)
        verifier = Lean4CompilationVerifier(config)
        result = verifier.verify_file(lean_file)

        assert result.status == CompilationStatus.SUCCESS
        assert result.success is True
        assert result.duration >= 0

    @patch("spec_tools.verification.compilation.subprocess.run")
    @patch("spec_tools.verification.compilation._MemoryMonitor")
    def test_verify_file_failure(self, mock_monitor_cls, mock_run, temp_dir):
        mock_process = MagicMock()
        mock_process.returncode = 1
        mock_process.stdout = "test.lean:5:10: error: type mismatch\n"
        mock_process.stderr = ""
        mock_run.return_value = mock_process

        mock_monitor = MagicMock()
        mock_monitor.exceeded_limit = False
        mock_monitor.stop.return_value = 10.0
        mock_monitor_cls.return_value = mock_monitor

        lean_file = temp_dir / "test.lean"
        lean_file.write_text("def foo : Nat := 0\n")

        config = CompilationConfig(clean_before_build=False)
        verifier = Lean4CompilationVerifier(config)
        result = verifier.verify_file(lean_file)

        assert result.status == CompilationStatus.FAILED

    @patch("spec_tools.verification.compilation.subprocess.run")
    @patch("spec_tools.verification.compilation._MemoryMonitor")
    def test_verify_file_timeout(self, mock_monitor_cls, mock_run, temp_dir):
        import subprocess

        mock_monitor = MagicMock()
        mock_monitor.stop.return_value = 10.0
        mock_monitor_cls.return_value = mock_monitor
        mock_run.side_effect = subprocess.TimeoutExpired(cmd=["lake"], timeout=300)

        lean_file = temp_dir / "test.lean"
        lean_file.write_text("def foo : Nat := 0\n")

        config = CompilationConfig(clean_before_build=False, timeout_seconds=300)
        verifier = Lean4CompilationVerifier(config)
        result = verifier.verify_file(lean_file)

        assert result.status == CompilationStatus.TIMEOUT

    @patch("spec_tools.verification.compilation.subprocess.run")
    @patch("spec_tools.verification.compilation._MemoryMonitor")
    def test_verify_file_exception(self, mock_monitor_cls, mock_run, temp_dir):
        mock_monitor = MagicMock()
        mock_monitor.stop.return_value = 10.0
        mock_monitor_cls.return_value = mock_monitor
        mock_run.side_effect = RuntimeError("unexpected error")

        lean_file = temp_dir / "test.lean"
        lean_file.write_text("def foo : Nat := 0\n")

        config = CompilationConfig(clean_before_build=False)
        verifier = Lean4CompilationVerifier(config)
        result = verifier.verify_file(lean_file)

        assert result.status == CompilationStatus.FAILED
        assert "unexpected error" in result.output

    def test_parse_compilation_errors_pattern1(self):
        verifier = Lean4CompilationVerifier(CompilationConfig(clean_before_build=False))
        stdout = "test.lean:10:5: error: type mismatch\n"
        stderr = ""
        errors = verifier._parse_compilation_errors(stdout, stderr, Path("test.lean"))
        assert len(errors) >= 1
        assert errors[0].line_number == 10
        assert errors[0].column_number == 5

    def test_parse_compilation_errors_pattern2(self):
        verifier = Lean4CompilationVerifier(CompilationConfig(clean_before_build=False))
        stdout = "error: at line 42\n"
        stderr = ""
        errors = verifier._parse_compilation_errors(stdout, stderr, Path("test.lean"))
        assert len(errors) >= 1
        assert errors[0].line_number == 42

    def test_parse_compilation_errors_pattern3(self):
        verifier = Lean4CompilationVerifier(CompilationConfig(clean_before_build=False))
        stdout = "type mismatch expected Nat, found String\n"
        stderr = ""
        errors = verifier._parse_compilation_errors(stdout, stderr, Path("test.lean"))
        type_errors = [e for e in errors if e.error_type == "Type Mismatch"]
        assert len(type_errors) >= 1

    def test_parse_compilation_errors_pattern4(self):
        verifier = Lean4CompilationVerifier(CompilationConfig(clean_before_build=False))
        stdout = "unknown identifier 'myFunc'\n"
        stderr = ""
        errors = verifier._parse_compilation_errors(stdout, stderr, Path("test.lean"))
        unknown_errors = [e for e in errors if e.error_type == "Unknown Identifier"]
        assert len(unknown_errors) >= 1

    def test_parse_compilation_errors_pattern5(self):
        verifier = Lean4CompilationVerifier(CompilationConfig(clean_before_build=False))
        stdout = "unknown import 'Mathlib.Data.Nat'\n"
        stderr = ""
        errors = verifier._parse_compilation_errors(stdout, stderr, Path("test.lean"))
        import_errors = [e for e in errors if e.error_type == "Import Error"]
        assert len(import_errors) >= 1

    def test_get_error_context(self):
        verifier = Lean4CompilationVerifier(CompilationConfig(clean_before_build=False))
        lines = ["line 1", "line 2", "line 3", "line 4", "line 5"]
        context = verifier._get_error_context(lines, 3)
        assert context is not None
        assert "line 1" in context

    def test_get_error_context_empty(self):
        verifier = Lean4CompilationVerifier(CompilationConfig(clean_before_build=False))
        context = verifier._get_error_context([], 1)
        assert context is None

    def test_get_statistics(self):
        verifier = Lean4CompilationVerifier(CompilationConfig(clean_before_build=False))
        results = [
            CompilationResult(Path("a.lean"), CompilationStatus.SUCCESS),
            CompilationResult(Path("b.lean"), CompilationStatus.FAILED),
            CompilationResult(Path("c.lean"), CompilationStatus.TIMEOUT),
        ]
        stats = verifier.get_statistics(results)
        assert stats["total_files"] == 3
        assert stats["successful"] == 1
        assert stats["failed"] == 2
        assert stats["timeout"] == 1
        assert stats["success_rate"] == pytest.approx(33.33, rel=0.1)

    def test_get_statistics_empty(self):
        verifier = Lean4CompilationVerifier(CompilationConfig(clean_before_build=False))
        stats = verifier.get_statistics([])
        assert stats["total_files"] == 0
        assert stats["success_rate"] == 0

    def test_find_lean_files(self, temp_dir):
        (temp_dir / "a.lean").write_text("content")
        (temp_dir / "b.md").write_text("content")
        sub = temp_dir / "sub"
        sub.mkdir()
        (sub / "c.lean").write_text("content")

        verifier = Lean4CompilationVerifier(CompilationConfig(clean_before_build=False))
        files = verifier._find_lean_files(temp_dir)
        assert len(files) == 2


class TestMemoryMonitor:
    def test_start_stop(self):
        monitor = _MemoryMonitor(4096)
        monitor.start()
        peak = monitor.stop()
        assert isinstance(peak, float)

    def test_check(self):
        monitor = _MemoryMonitor(999999)
        monitor.start()
        result = monitor.check()
        assert isinstance(result, bool)


class TestCreateVerificationIssuesMarkdown:
    def test_creates_file(self, temp_dir):
        from spec_tools.verification.compilation import create_verification_issues_markdown

        output = temp_dir / "report.md"
        results = [
            CompilationResult(Path("a.lean"), CompilationStatus.SUCCESS, duration=1.0),
            CompilationResult(Path("b.lean"), CompilationStatus.FAILED, duration=2.0),
        ]
        create_verification_issues_markdown(results, output)
        assert output.exists()
        content = output.read_text()
        assert "Compilation Verification Report" in content
        assert "Success Rate:" in content
