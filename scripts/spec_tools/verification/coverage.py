"""
Coverage Tracking Script

This module provides tools for tracking verification coverage across all
specification files, following threat model success criteria.

The tool supports:
- File-level coverage tracking
- Spec point coverage tracking
- Category-level coverage metrics
- Success criteria validation
- Progress reporting
"""

from pathlib import Path
from typing import List, Dict, Set, Optional, Tuple
from dataclasses import dataclass, field
from datetime import datetime

from spec_tools.verification.models import (
    CompilationResult,
    Issue,
    IssueCategory,
    IssueSeverity,
    CoverageMetrics,
    CoverageReport,
)


@dataclass
class CoverageConfig:
    """Configuration for coverage tracking.

    Attributes:
        specs_root: Root directory containing all specification directories
        required_files: List of required files per spec (Spec.lean, Examples.lean, Lemmas.lean)
        spec_point_threshold: Minimum spec points required for coverage
        success_criteria: Success criteria thresholds
    """

    specs_root: Path = field(default_factory=lambda: Path("Morph/Specs"))
    required_files: List[str] = field(default_factory=lambda: ["Spec.lean", "Examples.lean", "Lemmas.lean"])
    spec_point_threshold: int = 1
    success_criteria: Dict[str, float] = field(default_factory=lambda: {
        "file_coverage": 95.0,
        "spec_coverage": 95.0,
        "compilation_success_rate": 95.0,
        "type_checking_success_rate": 98.0,
    })


class CoverageTracker:
    """Tracks verification coverage across all specification files.

    This class implements coverage tracking following threat model
    success criteria for completeness and reproducibility.
    """

    def __init__(self, config: Optional[CoverageConfig] = None):
        """Initialize tracker with optional configuration.

        Args:
            config: Coverage tracking configuration. If None, uses defaults.
        """
        self.config = config or CoverageConfig()
        self._verified_files: Set[Path] = set()
        self._verified_specs: Set[str] = set()
        self._issues_by_category: Dict[IssueCategory, List[Issue]] = {
            IssueCategory.USP: [],
            IssueCategory.LCF: [],
            IssueCategory.ISR: [],
            IssueCategory.MEL: [],
            IssueCategory.IBF: [],
        }
        self._issues_by_severity: Dict[IssueSeverity, List[Issue]] = {
            IssueSeverity.CRITICAL: [],
            IssueSeverity.HIGH: [],
            IssueSeverity.MEDIUM: [],
            IssueSeverity.LOW: [],
        }

    def track_compilation_result(self, result: CompilationResult) -> None:
        """Track a compilation result for coverage.

        Args:
            result: CompilationResult object to track.
        """
        if result.success:
            self._verified_files.add(result.file_path)
            spec_name = result.file_path.parent.name
            if result.file_path.name == "Spec.lean":
                self._verified_specs.add(spec_name)

    def track_issue(self, issue: Issue) -> None:
        """Track an issue for coverage metrics.

        Args:
            issue: Issue object to track.
        """
        self._issues_by_category[issue.category].append(issue)
        self._issues_by_severity[issue.severity].append(issue)

    def track_directory(self, directory: Path) -> None:
        """Track coverage for all files in a directory.

        Args:
            directory: Path to directory containing Lean 4 files.
        """
        lean_files = list(directory.glob("**/*.lean"))

        for file_path in lean_files:
            if file_path in self._verified_files:
                continue
            # File not yet verified, track as uncovered
            pass

    def track_specs(self, specs_root: Optional[Path] = None) -> None:
        """Track coverage for all specification directories.

        Args:
            specs_root: Root directory containing all specification directories.
                         If None, uses config default.
        """
        root = specs_root or self.config.specs_root

        # Find all spec directories
        spec_dirs = [d for d in root.iterdir() if d.is_dir()]

        for spec_dir in spec_dirs:
            spec_name = spec_dir.name

            # Check if all required files exist
            required_files_exist = all(
                (spec_dir / filename).exists()
                for filename in self.config.required_files
            )

            if required_files_exist:
                # Check if Spec.lean is verified
                spec_verified = (spec_dir / "Spec.lean") in self._verified_files
                if spec_verified:
                    self._verified_specs.add(spec_name)

    def get_coverage_metrics(self) -> CoverageMetrics:
        """Get current coverage metrics.

        Returns:
            CoverageMetrics object with current coverage statistics.
        """
        # Count total specs and files
        spec_dirs = list(self.config.specs_root.iterdir())
        total_specs = sum(1 for d in spec_dirs if d.is_dir())

        total_files = 0
        for spec_dir in spec_dirs:
            if spec_dir.is_dir():
                total_files += len(list(spec_dir.glob("*.lean")))

        # Count verified files
        verified_files_count = len(self._verified_files)
        verified_specs_count = len(self._verified_specs)

        # Count spec points (simplified: 1 per verified spec)
        total_spec_points = total_specs * self.config.spec_point_threshold
        verified_spec_points = verified_specs_count * self.config.spec_point_threshold

        # Count issues by category
        issues_by_category: Dict[IssueCategory, int] = {}
        for category, issues in self._issues_by_category.items():
            issues_by_category[category] = len(issues)

        # Count issues by severity
        issues_by_severity: Dict[IssueSeverity, int] = {}
        for severity, issues in self._issues_by_severity.items():
            issues_by_severity[severity] = len(issues)

        return CoverageMetrics(
            total_specs=total_specs,
            verified_specs=verified_specs_count,
            total_files=total_files,
            verified_files=verified_files_count,
            total_spec_points=total_spec_points,
            verified_spec_points=verified_spec_points,
            issues_by_category=issues_by_category,
            issues_by_severity=issues_by_severity,
        )

    def generate_coverage_report(self) -> CoverageReport:
        """Generate a comprehensive coverage report.

        Returns:
            CoverageReport object with coverage metrics and lists.
        """
        metrics = self.get_coverage_metrics()

        # Get uncovered items
        uncovered_files = self._get_uncovered_files()
        uncovered_specs = self._get_uncovered_specs()

        # Get verified items
        verified_files = list(self._verified_files)
        verified_specs = list(self._verified_specs)

        return CoverageReport(
            metrics=metrics,
            uncovered_files=uncovered_files,
            uncovered_specs=uncovered_specs,
            verified_files=verified_files,
            verified_specs=verified_specs,
            generated_at=datetime.now(),
        )

    def validate_success_criteria(self) -> Tuple[bool, Dict[str, str]]:
        """Validate coverage against success criteria.

        Returns:
            Tuple of (all_passed, criteria_results).
        """
        metrics = self.get_coverage_metrics()
        criteria_results: Dict[str, str] = {}
        all_passed = True

        # File coverage check
        file_coverage = metrics.file_coverage
        file_threshold = self.config.success_criteria.get("file_coverage", 95.0)
        file_passed = file_coverage >= file_threshold
        criteria_results["file_coverage"] = (
            f"PASSED: {file_coverage:.1f}% >= {file_threshold:.1f}%"
            if file_passed
            else f"FAILED: {file_coverage:.1f}% < {file_threshold:.1f}%"
        )
        all_passed = all_passed and file_passed

        # Spec coverage check
        spec_coverage = metrics.spec_coverage
        spec_threshold = self.config.success_criteria.get("spec_coverage", 95.0)
        spec_passed = spec_coverage >= spec_threshold
        criteria_results["spec_coverage"] = (
            f"PASSED: {spec_coverage:.1f}% >= {spec_threshold:.1f}%"
            if spec_passed
            else f"FAILED: {spec_coverage:.1f}% < {spec_threshold:.1f}%"
        )
        all_passed = all_passed and spec_passed

        # Overall success
        criteria_results["overall_success"] = (
            "PASSED" if all_passed else "FAILED"
        )

        return all_passed, criteria_results

    def _get_uncovered_files(self) -> List[Path]:
        """Get list of files not yet verified.

        Returns:
            List of paths to unverified files.
        """
        spec_dirs = list(self.config.specs_root.iterdir())
        uncovered = []

        for spec_dir in spec_dirs:
            if spec_dir.is_dir():
                for filename in self.config.required_files:
                    file_path = spec_dir / filename
                    if file_path.exists() and file_path not in self._verified_files:
                        uncovered.append(file_path)

        return uncovered

    def _get_uncovered_specs(self) -> List[str]:
        """Get list of specs not yet verified.

        Returns:
            List of spec names not yet verified.
        """
        spec_dirs = list(self.config.specs_root.iterdir())
        uncovered = []

        for spec_dir in spec_dirs:
            if spec_dir.is_dir():
                spec_name = spec_dir.name
                if spec_name not in self._verified_specs:
                    uncovered.append(spec_name)

        return uncovered

    def get_progress_summary(self) -> str:
        """Get a human-readable progress summary.

        Returns:
            String summarizing current verification progress.
        """
        metrics = self.get_coverage_metrics()

        summary_lines = [
            "## Verification Progress Summary",
            "",
            f"**Total Specs:** {metrics.total_specs}",
            f"**Verified Specs:** {metrics.verified_specs} ({metrics.spec_coverage:.1f}%)",
            "",
            f"**Total Files:** {metrics.total_files}",
            f"**Verified Files:** {metrics.verified_files} ({metrics.file_coverage:.1f}%)",
            "",
            "## Issues by Category",
        ]

        for category in IssueCategory:
            count = metrics.issues_by_category.get(category, 0)
            summary_lines.append(f"- **{category.value}:** {count}")

        summary_lines.extend([
            "",
            "## Issues by Severity",
        ])

        for severity in IssueSeverity:
            count = metrics.issues_by_severity.get(severity, 0)
            summary_lines.append(f"- **{severity.value}:** {count}")

        summary_lines.extend([
            "",
            "## Success Criteria",
        ])

        all_passed, criteria = self.validate_success_criteria()
        for criterion, result in criteria.items():
            summary_lines.append(f"- {result}")

        return "\n".join(summary_lines)

    def generate_markdown_report(
        self,
        output_path: Path = Path("VERIFICATION_COVERAGE.md")
    ) -> None:
        """Generate a markdown coverage report.

        Args:
            output_path: Path to output markdown file.
        """
        report = self.generate_coverage_report()
        all_passed, criteria = self.validate_success_criteria()

        with open(output_path, 'w') as f:
            f.write("# Specification Verification Coverage Report\n\n")
            f.write(f"**Generated:** {datetime.now().isoformat()}\n\n")

            # Summary
            f.write(report)
            f.write("\n---\n\n")

            # Detailed metrics
            f.write("## Detailed Metrics\n\n")
            metrics = self.get_coverage_metrics()
            f.write(f"- **Total Specs:** {metrics.total_specs}\n")
            f.write(f"- **Verified Specs:** {metrics.verified_specs} ({metrics.spec_coverage:.1f}%)\n")
            f.write(f"- **Total Files:** {metrics.total_files}\n")
            f.write(f"- **Verified Files:** {metrics.verified_files} ({metrics.file_coverage:.1f}%)\n")
            f.write(f"- **Total Spec Points:** {metrics.total_spec_points}\n")
            f.write(f"- **Verified Spec Points:** {metrics.verified_spec_points} ({metrics.spec_point_coverage:.1f}%)\n\n")

            # Success criteria validation
            f.write("## Success Criteria Validation\n\n")
            f.write("Based on threat model success criteria:\n\n")
            for criterion, result in criteria.items():
                f.write(f"- {result}\n")

            # Overall status
            f.write(f"\n**Overall Status:** {criteria['overall_success']}\n")

            # Uncovered items
            uncovered_files = self._get_uncovered_files()
            uncovered_specs = self._get_uncovered_specs()

            if uncovered_files:
                f.write("\n## Uncovered Files\n\n")
                for file_path in uncovered_files:
                    f.write(f"- {file_path}\n")

            if uncovered_specs:
                f.write("\n## Uncovered Specs\n\n")
                for spec_name in uncovered_specs:
                    f.write(f"- {spec_name}\n")

            # Issues summary
            f.write("\n## Issues Summary\n\n")
            f.write(f"**Total Issues:** {report.total_issues}\n")
            f.write(f"- **Critical:** {report.critical_issues}\n")
            f.write(f"- **High:** {report.high_issues}\n")
            f.write(f"- **Medium:** {report.medium_issues}\n")
            f.write(f"- **Low:** {report.low_issues}\n")

    def reset_tracking(self) -> None:
        """Reset all tracking data.

        Call this to start a new verification cycle.
        """
        self._verified_files.clear()
        self._verified_specs.clear()
        for category in self._issues_by_category:
            self._issues_by_category[category].clear()
        for severity in self._issues_by_severity:
            self._issues_by_severity[severity].clear()
