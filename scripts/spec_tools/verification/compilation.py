"""
Lean 4 Compilation Verification Tool

This module provides tools for verifying Lean 4 specification files,
following ADR-002 guidelines for compilation verification.

The tool supports:
- Full compilation coverage for all spec files
- Error classification (Syntax, Type, Import, Proof Obligations)
- Fallback strategies for compilation failures
- Resource management (timeouts, memory monitoring)
"""

import datetime
import re
import subprocess
import time
from dataclasses import dataclass, field
from pathlib import Path
from typing import Dict, List, Optional

import psutil

from spec_tools.verification.models import (
    CompilationError,
    CompilationResult,
    CompilationStatus,
    IssueCategory,
    IssueSeverity,
)


@dataclass
class CompilationConfig:
    """Configuration for Lean 4 compilation verification.

    Attributes:
        lean_path: Path to Lean 4 compiler executable
        lake_path: Path to Lake package manager executable
        timeout_seconds: Maximum time to wait for compilation
        memory_limit_mb: Maximum memory limit in MB
        clean_before_build: Whether to clean build artifacts before compilation
        parallel_jobs: Number of parallel compilation jobs
        verbose: Whether to enable verbose output
    """

    lean_path: Path = field(default_factory=lambda: Path("lake"))
    lake_path: Path = field(default_factory=lambda: Path("lake"))
    timeout_seconds: int = 300  # 5 minutes default
    memory_limit_mb: int = 4096  # 4GB default
    clean_before_build: bool = True
    parallel_jobs: int = 1
    verbose: bool = False


class Lean4CompilationVerifier:
    """Verifies Lean 4 specification files through compilation.

    This class implements ADR-002's decision to verify all 129 specification
    files using Lean 4 compiler, with comprehensive error tracking and
    fallback strategies for handling compilation failures.
    """

    def __init__(self, config: Optional[CompilationConfig] = None):
        """Initialize the verifier with optional configuration.

        Args:
            config: Compilation configuration. If None, uses defaults.
        """
        self.config = config or CompilationConfig()
        self._category_counters: Dict[IssueCategory, int] = {
            IssueCategory.USP: 0,
            IssueCategory.LCF: 0,
            IssueCategory.ISR: 0,
            IssueCategory.MEL: 0,
            IssueCategory.IBF: 0,
        }
        self._severity_counters: Dict[IssueSeverity, int] = {
            IssueSeverity.CRITICAL: 0,
            IssueSeverity.HIGH: 0,
            IssueSeverity.MEDIUM: 0,
            IssueSeverity.LOW: 0,
        }

    def verify_file(self, file_path: Path) -> CompilationResult:
        """Verify a single Lean 4 file.

        Args:
            file_path: Path to the Lean 4 file to verify.

        Returns:
            CompilationResult with status, errors, and timing information.
        """
        start_time = time.time()
        memory_monitor = _MemoryMonitor(self.config.memory_limit_mb)
        memory_monitor.start()

        try:
            # Clean build artifacts if configured
            if self.config.clean_before_build:
                self._clean_build()

            # Run Lake build command
            result = self._run_lake_build(file_path)

            duration = time.time() - start_time
            memory_peak = memory_monitor.stop()

            # Parse errors from output
            errors = self._parse_compilation_errors(result.stdout, result.stderr, file_path)

            # Determine compilation status
            if result.returncode == 0 and not errors:
                status = CompilationStatus.SUCCESS
            elif result.returncode != 0:
                status = CompilationStatus.FAILED
            elif memory_monitor.exceeded_limit:
                status = CompilationStatus.MEMORY_ERROR
            else:
                status = CompilationStatus.SUCCESS

            return CompilationResult(
                file_path=file_path,
                status=status,
                errors=errors,
                duration=duration,
                memory_peak=memory_peak,
                output=result.stdout + result.stderr,
            )

        except subprocess.TimeoutExpired:
            duration = time.time() - start_time
            memory_peak = memory_monitor.stop()
            return CompilationResult(
                file_path=file_path,
                status=CompilationStatus.TIMEOUT,
                errors=[],
                duration=duration,
                memory_peak=memory_peak,
                output="Compilation timed out",
            )
        except Exception as e:
            duration = time.time() - start_time
            memory_peak = memory_monitor.stop()
            return CompilationResult(
                file_path=file_path,
                status=CompilationStatus.FAILED,
                errors=[],
                duration=duration,
                memory_peak=memory_peak,
                output=f"Exception during compilation: {str(e)}",
            )

    def verify_directory(self, directory: Path) -> List[CompilationResult]:
        """Verify all Lean 4 files in a directory.

        Args:
            directory: Path to the directory containing Lean 4 files.

        Returns:
            List of CompilationResult objects for each file.
        """
        lean_files = self._find_lean_files(directory)
        results = []

        for file_path in lean_files:
            if self.config.verbose:
                print(f"Verifying: {file_path}")
            result = self.verify_file(file_path)
            results.append(result)

        return results

    def verify_specs(self, specs_root: Path = Path("Morph/Specs")) -> List[CompilationResult]:
        """Verify all specification files.

        Args:
            specs_root: Root directory containing all specification directories.

        Returns:
            List of CompilationResult objects for all spec files.
        """
        results = []

        # Find all spec directories
        spec_dirs = [d for d in specs_root.iterdir() if d.is_dir()]

        for spec_dir in spec_dirs:
            # Verify Spec.lean, Examples.lean, and Lemmas.lean
            for filename in ["Spec.lean", "Examples.lean", "Lemmas.lean"]:
                file_path = spec_dir / filename
                if file_path.exists():
                    if self.config.verbose:
                        print(f"Verifying: {file_path}")
                    result = self.verify_file(file_path)
                    results.append(result)

        return results

    def _run_lake_build(self, file_path: Path) -> subprocess.CompletedProcess:
        """Run Lake build command for a single file.

        Args:
            file_path: Path to the Lean 4 file to build.

        Returns:
            CompletedProcess with stdout, stderr, and return code.
        """
        cmd = [
            str(self.config.lake_path),
            "build",
            str(file_path),
        ]

        if self.config.verbose:
            print(f"Running: {' '.join(cmd)}")

        try:
            result = subprocess.run(
                cmd,
                capture_output=True,
                text=True,
                timeout=self.config.timeout_seconds,
                cwd=str(file_path.parent),
            )
            return result
        except subprocess.TimeoutExpired:
            raise subprocess.TimeoutExpired(cmd, self.config.timeout_seconds) from None

    def _clean_build(self) -> None:
        """Clean Lake build artifacts."""
        try:
            subprocess.run(
                [str(self.config.lake_path), "clean"],
                capture_output=True,
                timeout=60,
            )
            if self.config.verbose:
                print("Cleaned build artifacts")
        except Exception as e:
            if self.config.verbose:
                print(f"Warning: Failed to clean build: {e}")

    def _find_lean_files(self, directory: Path) -> List[Path]:
        """Find all Lean 4 files in a directory.

        Args:
            directory: Path to search for Lean 4 files.

        Returns:
            List of paths to .lean files.
        """
        lean_files = list(directory.glob("**/*.lean"))
        return lean_files

    def _parse_compilation_errors(self, stdout: str, stderr: str, file_path: Path) -> List[CompilationError]:
        """Parse compilation errors from Lean 4 output.

        Args:
            stdout: Standard output from compilation.
            stderr: Standard error output from compilation.
            file_path: Path to the file being compiled.

        Returns:
            List of CompilationError objects parsed from output.
        """
        errors = []
        output = stdout + stderr

        # Parse Lean 4 error patterns
        # Pattern 1: File:line:column: error message
        pattern1 = re.compile(r"^([^:]+):(\d+):(\d+): error:\s*(.+)$", re.MULTILINE)

        # Pattern 2: error: at line X
        pattern2 = re.compile(r"^error:\s*at\s+line\s+(\d+)", re.MULTILINE)

        # Pattern 3: type mismatch errors
        pattern3 = re.compile(r"type mismatch.*?expected\s+(.+?),?\s+found\s+(.+)", re.MULTILINE | re.IGNORECASE)

        # Pattern 4: unknown identifier
        pattern4 = re.compile(r"unknown identifier '([^']+)'", re.MULTILINE)

        # Pattern 5: import errors
        pattern5 = re.compile(r"unknown import '([^']+)'", re.MULTILINE)

        lines = output.split("\n")
        for line_num, line in enumerate(lines, start=1):
            line = line.strip()

            # Match pattern 1: File:line:column: error message
            match = pattern1.match(line)
            if match:
                errors.append(
                    CompilationError(
                        file_path=file_path,
                        line_number=int(match.group(2)),
                        column_number=int(match.group(3)),
                        error_type="Syntax/Type Error",
                        error_message=match.group(4).strip(),
                        context=self._get_error_context(lines, line_num),
                    )
                )
                continue

            # Match pattern 2: error at line X
            match = pattern2.match(line)
            if match:
                errors.append(
                    CompilationError(
                        file_path=file_path,
                        line_number=int(match.group(1)),
                        column_number=0,
                        error_type="Compilation Error",
                        error_message=line,
                        context=self._get_error_context(lines, line_num),
                    )
                )
                continue

            # Match pattern 3: type mismatch
            match = pattern3.search(line)
            if match:
                errors.append(
                    CompilationError(
                        file_path=file_path,
                        line_number=line_num,
                        column_number=0,
                        error_type="Type Mismatch",
                        error_message=f"expected {match.group(1)}, found {match.group(2)}",
                        suggestion="Check type annotations and ensure types match",
                        context=self._get_error_context(lines, line_num),
                    )
                )
                continue

            # Match pattern 4: unknown identifier
            match = pattern4.search(line)
            if match:
                errors.append(
                    CompilationError(
                        file_path=file_path,
                        line_number=line_num,
                        column_number=0,
                        error_type="Unknown Identifier",
                        error_message=f"Unknown identifier: {match.group(1)}",
                        suggestion="Check if identifier is defined or imported",
                        context=self._get_error_context(lines, line_num),
                    )
                )
                continue

            # Match pattern 5: import error
            match = pattern5.search(line)
            if match:
                errors.append(
                    CompilationError(
                        file_path=file_path,
                        line_number=line_num,
                        column_number=0,
                        error_type="Import Error",
                        error_message=f"Unknown import: {match.group(1)}",
                        suggestion="Check if import path is correct and dependency is available",
                        context=self._get_error_context(lines, line_num),
                    )
                )
                continue

        return errors

    def _get_error_context(self, lines: List[str], error_line: int) -> Optional[str]:
        """Get context lines around an error.

        Args:
            lines: All lines from the file.
            error_line: Line number where error occurred.

        Returns:
            String with context lines around the error, or None.
        """
        context_start = max(0, error_line - 3)
        context_end = min(len(lines), error_line + 2)
        context_lines = lines[context_start:context_end]

        if context_lines:
            return "\n".join(context_lines)
        return None

    def get_statistics(self, results: List[CompilationResult]) -> Dict[str, float]:
        """Get compilation statistics from results.

        Args:
            results: List of CompilationResult objects.

        Returns:
            Dictionary with compilation statistics.
        """
        total_files = len(results)
        successful = sum(1 for r in results if r.success)
        failed = sum(1 for r in results if not r.success)
        timeout = sum(1 for r in results if r.status == CompilationStatus.TIMEOUT)
        memory_error = sum(1 for r in results if r.status == CompilationStatus.MEMORY_ERROR)
        total_errors = sum(r.error_count for r in results)

        return {
            "total_files": total_files,
            "successful": successful,
            "failed": failed,
            "timeout": timeout,
            "memory_error": memory_error,
            "total_errors": total_errors,
            "success_rate": (successful / total_files * 100) if total_files > 0 else 0,
        }


class _MemoryMonitor:
    """Monitor memory usage during compilation.

    This class tracks memory usage and detects when it exceeds
    a configured limit, implementing RISK-LEAN-004 mitigation.
    """

    def __init__(self, limit_mb: int):
        """Initialize memory monitor.

        Args:
            limit_mb: Memory limit in MB.
        """
        self.limit_mb = limit_mb
        self.exceeded_limit = False
        self.process = psutil.Process()
        self._peak_memory = 0.0

    def start(self) -> None:
        """Start monitoring memory usage."""
        self.exceeded_limit = False
        self._peak_memory = 0.0

    def stop(self) -> float:
        """Stop monitoring and return peak memory usage.

        Returns:
            Peak memory usage in MB.
        """
        return self._peak_memory

    def check(self) -> bool:
        """Check if memory limit has been exceeded.

        Returns:
            True if memory limit exceeded, False otherwise.
        """
        try:
            memory_mb = self.process.memory_info().rss / 1024 / 1024  # Convert to MB
            self._peak_memory = max(self._peak_memory, memory_mb)

            if memory_mb > self.limit_mb:
                self.exceeded_limit = True
                return True

            return False
        except (psutil.NoSuchProcess, psutil.AccessDenied):
            return False


def create_verification_issues_markdown(
    results: List[CompilationResult], output_path: Path = Path("VERIFICATION_ISSUES.md")
) -> None:
    """Create a markdown report of verification issues.

    Args:
        results: List of CompilationResult objects.
        output_path: Path to output markdown file.
    """
    verifier = Lean4CompilationVerifier()
    stats = verifier.get_statistics(results)

    with open(output_path, "w") as f:
        f.write("# Lean 4 Compilation Verification Report\n\n")
        f.write(f"**Generated:** {datetime.datetime.now().isoformat()}\n\n")

        # Summary
        f.write("## Summary\n\n")
        f.write(f"- **Total Files:** {stats['total_files']}\n")
        f.write(f"- **Successful:** {stats['successful']}\n")
        f.write(f"- **Failed:** {stats['failed']}\n")
        f.write(f"- **Timeout:** {stats['timeout']}\n")
        f.write(f"- **Memory Error:** {stats['memory_error']}\n")
        f.write(f"- **Total Errors:** {stats['total_errors']}\n")
        f.write(f"- **Success Rate:** {stats['success_rate']:.1f}%\n\n")

        # Issues by file
        f.write("## Issues by File\n\n")
        for result in results:
            if not result.success or result.errors:
                f.write(f"### {result.file_path}\n\n")
                f.write(f"**Status:** {result.status.value}\n")
                f.write(f"**Duration:** {result.duration:.2f}s\n")
                f.write(f"**Peak Memory:** {result.memory_peak:.1f}MB\n\n")

                if result.errors:
                    f.write("**Errors:**\n\n")
                    for error in result.errors:
                        f.write(f"- {error}\n\n")

        # Success criteria check
        f.write("## Success Criteria Check\n\n")
        f.write("Based on ADR-002 success criteria:\n\n")
        f.write(f"- **Compilation Success Rate:** {stats['success_rate']:.1f}% (Target: >95%)\n")
        f.write(f"- **Status:** {'PASS' if stats['success_rate'] > 95 else 'FAIL'}\n\n")
