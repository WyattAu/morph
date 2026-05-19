"""Additional tests for Lean4CompilationVerifier to improve coverage."""

from pathlib import Path
from unittest.mock import MagicMock, patch

import pytest

from spec_tools.verification.compilation import (
    CompilationConfig,
    Lean4CompilationVerifier,
    _MemoryMonitor,
    create_verification_issues_markdown,
)
from spec_tools.verification.models import (
    CompilationError,
    CompilationResult,
    CompilationStatus,
)


class TestLean4CompilationVerifierCoverage:
    @patch("spec_tools.verification.compilation.subprocess.run")
    @patch("spec_tools.verification.compilation._MemoryMonitor")
    def test_verify_file_success_with_errors_in_output(self, mock_monitor_cls, mock_run, temp_dir):
        mock_process = MagicMock()
        mock_process.returncode = 0
        mock_process.stdout = "test.lean:10:5: error: type mismatch\n"
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
        assert len(result.errors) >= 1

    @patch("spec_tools.verification.compilation.subprocess.run")
    @patch("spec_tools.verification.compilation._MemoryMonitor")
    def test_verify_file_memory_error(self, mock_monitor_cls, mock_run, temp_dir):
        mock_process = MagicMock()
        mock_process.returncode = 0
        mock_process.stdout = "test.lean:10:5: error: type mismatch\n"
        mock_process.stderr = ""
        mock_run.return_value = mock_process

        mock_monitor = MagicMock()
        mock_monitor.stop.return_value = 5000.0
        mock_monitor.exceeded_limit = True
        mock_monitor_cls.return_value = mock_monitor

        lean_file = temp_dir / "test.lean"
        lean_file.write_text("def foo : Nat := 0\n")

        config = CompilationConfig(clean_before_build=False)
        verifier = Lean4CompilationVerifier(config)
        result = verifier.verify_file(lean_file)

        assert result.status == CompilationStatus.MEMORY_ERROR

    @patch("spec_tools.verification.compilation.subprocess.run")
    @patch("spec_tools.verification.compilation._MemoryMonitor")
    def test_verify_file_clean_before_build(self, mock_monitor_cls, mock_run, temp_dir):
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

        config = CompilationConfig(clean_before_build=True, verbose=True)
        verifier = Lean4CompilationVerifier(config)
        result = verifier.verify_file(lean_file)

        assert result.status == CompilationStatus.SUCCESS

    def test_verify_directory_verbose(self, temp_dir):
        (temp_dir / "a.lean").write_text("def a : Nat := 0\n")
        (temp_dir / "b.lean").write_text("def b : Nat := 0\n")

        config = CompilationConfig(clean_before_build=False, verbose=True, timeout_seconds=1)
        verifier = Lean4CompilationVerifier(config)

        with patch.object(verifier, "verify_file") as mock_verify:
            mock_verify.return_value = CompilationResult(
                Path("a.lean"), CompilationStatus.SUCCESS
            )
            results = verifier.verify_directory(temp_dir)
            assert len(results) == 2

    def test_verify_specs_verbose(self, temp_dir):
        spec_dir = temp_dir / "SpecA"
        spec_dir.mkdir()
        (spec_dir / "Spec.lean").write_text("def a : Nat := 0\n")
        (spec_dir / "Examples.lean").write_text("def b : Nat := 0\n")
        (spec_dir / "Lemmas.lean").write_text("def c : Nat := 0\n")

        config = CompilationConfig(clean_before_build=False, verbose=True)
        verifier = Lean4CompilationVerifier(config)

        with patch.object(verifier, "verify_file") as mock_verify:
            mock_verify.return_value = CompilationResult(
                Path("Spec.lean"), CompilationStatus.SUCCESS
            )
            results = verifier.verify_specs(temp_dir)
            assert len(results) == 3

    def test_verify_specs_empty_dir(self, temp_dir):
        spec_dir = temp_dir / "EmptySpec"
        spec_dir.mkdir()

        config = CompilationConfig(clean_before_build=False)
        verifier = Lean4CompilationVerifier(config)
        results = verifier.verify_specs(temp_dir)
        assert len(results) == 0

    def test_verify_specs_nonexistent_dir(self):
        config = CompilationConfig(clean_before_build=False)
        verifier = Lean4CompilationVerifier(config)
        with pytest.raises(FileNotFoundError):
            verifier.verify_specs(Path("/nonexistent/path"))

    @patch("spec_tools.verification.compilation.subprocess.run")
    def test_clean_build_verbose_success(self, temp_dir):
        config = CompilationConfig(verbose=True)
        verifier = Lean4CompilationVerifier(config)

        mock_process = MagicMock()
        mock_process.returncode = 0
        with patch("spec_tools.verification.compilation.subprocess.run", return_value=mock_process):
            verifier._clean_build()

    @patch("spec_tools.verification.compilation.subprocess.run")
    def test_clean_build_verbose_failure(self, temp_dir):
        config = CompilationConfig(verbose=True)
        verifier = Lean4CompilationVerifier(config)

        with patch(
            "spec_tools.verification.compilation.subprocess.run",
            side_effect=RuntimeError("clean failed"),
        ):
            verifier._clean_build()

    def test_parse_compilation_errors_multiple_patterns(self):
        verifier = Lean4CompilationVerifier(CompilationConfig(clean_before_build=False))
        stdout = """test.lean:10:5: error: type mismatch
error: at line 42
unknown identifier 'myFunc'
unknown import 'Mathlib.Data.Nat'
type mismatch expected Nat, found String
"""
        stderr = ""
        errors = verifier._parse_compilation_errors(stdout, stderr, Path("test.lean"))
        assert len(errors) >= 5

    def test_parse_compilation_errors_empty_output(self):
        verifier = Lean4CompilationVerifier(CompilationConfig(clean_before_build=False))
        errors = verifier._parse_compilation_errors("", "", Path("test.lean"))
        assert len(errors) == 0

    def test_get_error_context_first_lines(self):
        verifier = Lean4CompilationVerifier(CompilationConfig(clean_before_build=False))
        lines = ["line 1", "line 2", "line 3"]
        context = verifier._get_error_context(lines, 1)
        assert "line 1" in context

    def test_get_error_context_last_lines(self):
        verifier = Lean4CompilationVerifier(CompilationConfig(clean_before_build=False))
        lines = ["line 1", "line 2", "line 3"]
        context = verifier._get_error_context(lines, 3)
        assert "line 3" in context

    def test_get_statistics_with_memory_error(self):
        verifier = Lean4CompilationVerifier(CompilationConfig(clean_before_build=False))
        results = [
            CompilationResult(Path("a.lean"), CompilationStatus.MEMORY_ERROR),
        ]
        stats = verifier.get_statistics(results)
        assert stats["memory_error"] == 1
        assert stats["failed"] == 1

    def test_get_statistics_with_errors(self):
        verifier = Lean4CompilationVerifier(CompilationConfig(clean_before_build=False))
        results = [
            CompilationResult(
                Path("a.lean"),
                CompilationStatus.FAILED,
                errors=[CompilationError(Path("a.lean"), 1, 0, "error", "msg")],
            ),
        ]
        stats = verifier.get_statistics(results)
        assert stats["total_errors"] == 1


class TestMemoryMonitorCoverage:
    def test_check_exceeded(self):
        monitor = _MemoryMonitor(0)
        monitor.start()
        result = monitor.check()
        assert isinstance(result, bool)

    def test_check_access_denied(self):
        monitor = _MemoryMonitor(4096)
        monitor.start()
        import psutil
        with patch.object(monitor.process, "memory_info", side_effect=psutil.AccessDenied(0)):
            result = monitor.check()
            assert result is False


class TestCreateVerificationIssuesMarkdownCoverage:
    def test_report_with_errors(self, temp_dir):
        output = temp_dir / "report.md"
        results = [
            CompilationResult(
                Path("a.lean"),
                CompilationStatus.FAILED,
                errors=[
                    CompilationError(
                        file_path=Path("a.lean"),
                        line_number=10,
                        column_number=5,
                        error_type="Syntax Error",
                        error_message="type mismatch",
                    )
                ],
                duration=1.0,
                memory_peak=100.0,
            ),
        ]
        create_verification_issues_markdown(results, output)
        content = output.read_text()
        assert "Syntax Error" in content
        assert "Duration:" in content
        assert "Peak Memory:" in content

    def test_report_pass_success_criteria(self, temp_dir):
        output = temp_dir / "report.md"
        results = [
            CompilationResult(Path("a.lean"), CompilationStatus.SUCCESS, duration=1.0),
        ]
        create_verification_issues_markdown(results, output)
        content = output.read_text()
        assert "PASS" in content

    def test_report_fail_success_criteria(self, temp_dir):
        output = temp_dir / "report.md"
        results = [
            CompilationResult(Path("a.lean"), CompilationStatus.FAILED, duration=1.0),
            CompilationResult(Path("b.lean"), CompilationStatus.FAILED, duration=1.0),
        ]
        create_verification_issues_markdown(results, output)
        content = output.read_text()
        assert "FAIL" in content

    def test_report_with_timeout(self, temp_dir):
        output = temp_dir / "report.md"
        results = [
            CompilationResult(Path("a.lean"), CompilationStatus.TIMEOUT, duration=300.0),
        ]
        create_verification_issues_markdown(results, output)
        content = output.read_text()
        assert "Timeout:" in content

    def test_report_with_memory_error(self, temp_dir):
        output = temp_dir / "report.md"
        results = [
            CompilationResult(Path("a.lean"), CompilationStatus.MEMORY_ERROR, duration=1.0),
        ]
        create_verification_issues_markdown(results, output)
        content = output.read_text()
        assert "Memory Error:" in content
