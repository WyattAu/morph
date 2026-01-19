"""
Data models for verification tools.

This module defines dataclasses and enums used for Lean 4 specification
verification, including compilation results, issue tracking, and coverage metrics.
"""

from dataclasses import dataclass, field
from enum import Enum
from pathlib import Path
from typing import List, Optional, Dict, Set
from datetime import datetime


class CompilationStatus(Enum):
    """Status of Lean 4 compilation.

    Attributes:
        SUCCESS: File compiled successfully
        FAILED: File failed to compile
        TIMEOUT: Compilation timed out
        MEMORY_ERROR: Compilation exhausted memory
        DEPENDENCY_ERROR: Dependency resolution failed
    """

    SUCCESS = "SUCCESS"
    FAILED = "FAILED"
    TIMEOUT = "TIMEOUT"
    MEMORY_ERROR = "MEMORY_ERROR"
    DEPENDENCY_ERROR = "DEPENDENCY_ERROR"


class IssueCategory(Enum):
    """Issue categories based on ADR-003 taxonomy.

    Attributes:
        USP: Unclear Specification Points
        LCF: Lean 4 Compilation Failures
        ISR: Insufficient Rigor
        MEL: Missing Examples or Lemmas
        IBF: Inconsistencies Between Files
    """

    USP = "USP"  # Unclear Specification Points
    LCF = "LCF"  # Lean 4 Compilation Failures
    ISR = "ISR"  # Insufficient Rigor
    MEL = "MEL"  # Missing Examples or Lemmas
    IBF = "IBF"  # Inconsistencies Between Files


class IssueSeverity(Enum):
    """Issue severity levels based on ADR-006.

    Attributes:
        CRITICAL: Blocks compilation or fundamental contradictions
        HIGH: Significant gaps in rigor or missing key content
        MEDIUM: Ambiguities or minor inconsistencies
        LOW: Minor issues or documentation improvements
    """

    CRITICAL = "CRITICAL"
    HIGH = "HIGH"
    MEDIUM = "MEDIUM"
    LOW = "LOW"


@dataclass
class IssueId:
    """Unique identifier for a verification issue.

    Format: {CategoryCode}-{SequentialNumber}

    Attributes:
        category: Issue category (e.g., USP, LCF)
        number: Sequential number within category
    """

    category: IssueCategory
    number: int

    def __str__(self) -> str:
        """Format issue ID as string."""
        return f"{self.category.value}-{self.number:03d}"


@dataclass
class CompilationError:
    """Represents a Lean 4 compilation error.

    This dataclass captures detailed information about a compilation error,
    including its location, type, and suggested fixes.

    Attributes:
        file_path: Path to the file with the error
        line_number: Line number where error occurred
        column_number: Column number where error occurred
        error_type: Type of compilation error
        error_message: Full error message from Lean 4 compiler
        error_code: Optional error code from compiler
        context: Optional context lines around the error
        suggestion: Optional suggestion for fixing the error
    """

    file_path: Path
    line_number: int
    column_number: int = 0
    error_type: str = ""
    error_message: str = ""
    error_code: Optional[str] = None
    context: Optional[str] = None
    suggestion: Optional[str] = None

    def __str__(self) -> str:
        """Format error for display."""
        location = f"{self.file_path}:{self.line_number}"
        if self.column_number > 0:
            location += f":{self.column_number}"
        result = f"{location} {self.error_type}: {self.error_message}"
        if self.suggestion:
            result += f"\n  Suggestion: {self.suggestion}"
        return result


@dataclass
class CompilationResult:
    """Result of compiling a single Lean 4 file.

    This dataclass captures the result of a compilation attempt,
    including status, errors, and timing information.

    Attributes:
        file_path: Path to the compiled file
        status: Compilation status
        errors: List of compilation errors
        duration: Time taken for compilation in seconds
        memory_peak: Peak memory usage in MB
        output: Full compiler output
    """

    file_path: Path
    status: CompilationStatus
    errors: List[CompilationError] = field(default_factory=list)
    duration: float = 0.0
    memory_peak: float = 0.0
    output: str = ""

    @property
    def success(self) -> bool:
        """Whether compilation was successful."""
        return self.status == CompilationStatus.SUCCESS

    @property
    def error_count(self) -> int:
        """Number of errors found."""
        return len(self.errors)


@dataclass
class Issue:
    """Represents a verification issue.

    This dataclass captures information about a verification issue,
    including its category, severity, and resolution suggestions.

    Attributes:
        issue_id: Unique identifier for the issue
        category: Issue category
        severity: Issue severity
        spec_name: Name of the specification
        file_path: Path to the file with the issue
        line_numbers: List of line numbers affected
        description: Human-readable description of the issue
        detection_method: How the issue was detected
        suggested_fix: Optional suggested fix for the issue
        related_issues: List of related issue IDs
        notes: Additional notes about the issue
        discovered_at: Timestamp when issue was discovered
        status: Current status of the issue
    """

    issue_id: IssueId
    category: IssueCategory
    severity: IssueSeverity
    spec_name: str
    file_path: Path
    line_numbers: List[int] = field(default_factory=list)
    description: str = ""
    detection_method: str = ""
    suggested_fix: Optional[str] = None
    related_issues: List[str] = field(default_factory=list)
    notes: Optional[str] = None
    discovered_at: datetime = field(default_factory=datetime.now)
    status: str = "OPEN"

    def __str__(self) -> str:
        """Format issue for display."""
        return (
            f"[{self.severity.value}] {self.issue_id}: {self.description}\n"
            f"  File: {self.file_path}\n"
            f"  Spec: {self.spec_name}\n"
            f"  Category: {self.category.value}\n"
            f"  Status: {self.status}"
        )


@dataclass
class CoverageMetrics:
    """Metrics for verification coverage.

    This dataclass captures coverage statistics across all specifications,
    including file-level and category-level metrics.

    Attributes:
        total_specs: Total number of specification directories
        verified_specs: Number of verified specifications
        total_files: Total number of Lean 4 files
        verified_files: Number of successfully verified files
        total_spec_points: Total number of spec points
        verified_spec_points: Number of verified spec points
        issues_by_category: Count of issues by category
        issues_by_severity: Count of issues by severity
        coverage_percentage: Overall coverage percentage
    """

    total_specs: int = 0
    verified_specs: int = 0
    total_files: int = 0
    verified_files: int = 0
    total_spec_points: int = 0
    verified_spec_points: int = 0
    issues_by_category: Dict[IssueCategory, int] = field(default_factory=dict)
    issues_by_severity: Dict[IssueSeverity, int] = field(default_factory=dict)

    @property
    def spec_coverage(self) -> float:
        """Percentage of specs verified."""
        if self.total_specs == 0:
            return 0.0
        return (self.verified_specs / self.total_specs) * 100.0

    @property
    def file_coverage(self) -> float:
        """Percentage of files verified."""
        if self.total_files == 0:
            return 0.0
        return (self.verified_files / self.total_files) * 100.0

    @property
    def spec_point_coverage(self) -> float:
        """Percentage of spec points verified."""
        if self.total_spec_points == 0:
            return 0.0
        return (self.verified_spec_points / self.total_spec_points) * 100.0


@dataclass
class CoverageReport:
    """Report for verification coverage.

    This dataclass aggregates coverage results across all specifications,
    including detailed metrics and uncovered items.

    Attributes:
        metrics: Overall coverage metrics
        uncovered_files: List of files not yet verified
        uncovered_specs: List of specs not yet verified
        verified_files: List of successfully verified files
        verified_specs: List of successfully verified specs
        generated_at: Timestamp when report was generated
    """

    metrics: CoverageMetrics
    uncovered_files: List[Path] = field(default_factory=list)
    uncovered_specs: List[str] = field(default_factory=list)
    verified_files: List[Path] = field(default_factory=list)
    verified_specs: List[str] = field(default_factory=list)
    generated_at: datetime = field(default_factory=datetime.now)

    @property
    def total_issues(self) -> int:
        """Total number of issues found."""
        return sum(self.metrics.issues_by_severity.values())

    @property
    def critical_issues(self) -> int:
        """Number of critical issues."""
        return self.metrics.issues_by_severity.get(IssueSeverity.CRITICAL, 0)

    @property
    def high_issues(self) -> int:
        """Number of high severity issues."""
        return self.metrics.issues_by_severity.get(IssueSeverity.HIGH, 0)

    @property
    def medium_issues(self) -> int:
        """Number of medium severity issues."""
        return self.metrics.issues_by_severity.get(IssueSeverity.MEDIUM, 0)

    @property
    def low_issues(self) -> int:
        """Number of low severity issues."""
        return self.metrics.issues_by_severity.get(IssueSeverity.LOW, 0)
