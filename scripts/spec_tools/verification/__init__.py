"""
Verification Tools Package

A modular, enterprise-grade Python package for Lean 4 specification verification,
including compilation verification, issue detection, classification, severity assessment,
and coverage tracking.

This package provides tools for verifying Lean 4 specifications following
the Morph project's coding standards and ADR guidelines.
"""

from spec_tools.verification.models import (
    CompilationResult,
    CompilationError,
    CompilationStatus,
    Issue,
    IssueCategory,
    IssueSeverity,
    IssueId,
    CoverageReport,
    CoverageMetrics,
)

from spec_tools.verification.compilation import (
    Lean4CompilationVerifier,
)

from spec_tools.verification.issue_detection import (
    AutomatedIssueDetector,
)

from spec_tools.verification.classification import (
    IssueClassifier,
)

from spec_tools.verification.severity import (
    SeverityAssessor,
)

from spec_tools.verification.coverage import (
    CoverageTracker,
)

__all__ = [
    # Models
    "CompilationResult",
    "CompilationError",
    "CompilationStatus",
    "Issue",
    "IssueCategory",
    "IssueSeverity",
    "IssueId",
    "CoverageReport",
    "CoverageMetrics",
    # Tools
    "Lean4CompilationVerifier",
    "AutomatedIssueDetector",
    "IssueClassifier",
    "SeverityAssessor",
    "CoverageTracker",
]
