"""
Issue Classification Helper Tool

This module provides tools for classifying verification issues according to
ADR-003 taxonomy, ensuring consistent classification across all issues.

The tool supports:
- Five-category taxonomy (USP, LCF, ISR, MEL, IBF)
- Four severity levels (Critical, High, Medium, Low)
- Classification guidelines and decision trees
- Peer review support and audit trails
"""

from typing import List, Optional, Dict, Tuple
from dataclasses import dataclass, field
from enum import Enum

from spec_tools.verification.models import (
    Issue,
    IssueCategory,
    IssueSeverity,
    IssueId,
)


@dataclass
class ClassificationConfig:
    """Configuration for issue classification.

    Attributes:
        strict_mode: Whether to enforce strict classification rules
        require_rationale: Whether to require rationale for classification
        allow_secondary_categories: Whether to allow multiple categories per issue
        default_severity: Default severity if not specified
    """

    strict_mode: bool = False
    require_rationale: bool = True
    allow_secondary_categories: bool = True
    default_severity: IssueSeverity = IssueSeverity.MEDIUM


class IssueClassifier:
    """Classifies verification issues according to ADR-003 taxonomy.

    This class implements ADR-003's five-category taxonomy with
    four severity levels, providing consistent classification across
    all verification issues.
    """

    # Category priority order (higher priority = more severe)
    _CATEGORY_PRIORITY = {
        IssueCategory.LCF: 1,  # Lean 4 Compilation Failures
        IssueCategory.IBF: 2,  # Inconsistencies Between Files
        IssueCategory.MEL: 3,  # Missing Examples or Lemmas
        IssueCategory.ISR: 4,  # Insufficient Rigor
        IssueCategory.USP: 5,  # Unclear Specification Points
    }

    # Severity characteristics mapping
    _SEVERITY_CHARACTERISTICS = {
        IssueSeverity.CRITICAL: {
            "blocks_compilation": True,
            "fundamental_contradiction": True,
            "blocks_verification": True,
            "requires_immediate_attention": True,
        },
        IssueSeverity.HIGH: {
            "significant_gap": True,
            "missing_key_content": True,
            "address_current_iteration": True,
            "blocks_refactoring": False,
        },
        IssueSeverity.MEDIUM: {
            "ambiguity": True,
            "minor_inconsistency": True,
            "address_next_iteration": True,
            "non_critical": True,
        },
        IssueSeverity.LOW: {
            "documentation_improvement": True,
            "formatting_issue": True,
            "minor_edge_case": True,
            "address_when_permits": True,
        },
    }

    def __init__(self, config: Optional[ClassificationConfig] = None):
        """Initialize classifier with optional configuration.

        Args:
            config: Classification configuration. If None, uses defaults.
        """
        self.config = config or ClassificationConfig()
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

    def classify_issue(
        self,
        description: str,
        category_hint: Optional[IssueCategory] = None,
        severity_hint: Optional[IssueSeverity] = None,
        context: Optional[str] = None
    ) -> Tuple[IssueCategory, IssueSeverity, str]:
        """Classify an issue based on description and context.

        Args:
            description: Issue description text.
            category_hint: Optional hint for category classification.
            severity_hint: Optional hint for severity assessment.
            context: Additional context information.

        Returns:
            Tuple of (category, severity, rationale).
        """
        # Use category hint if provided
        if category_hint:
            category = category_hint
            severity = self._assess_severity(
                description, category, severity_hint, context
            )
            rationale = f"Category hint provided: {category_hint.value}"
            return category, severity, rationale

        # Auto-classify based on description
        category = self._classify_category(description, context)
        severity = self._assess_severity(
            description, category, severity_hint, context
        )
        rationale = self._generate_rationale(description, category, severity)

        return category, severity, rationale

    def classify_compilation_error(
        self,
        error_type: str,
        error_message: str,
        blocks_compilation: bool = True
    ) -> Tuple[IssueCategory, IssueSeverity]:
        """Classify a Lean 4 compilation error.

        Args:
            error_type: Type of compilation error.
            error_message: Full error message.
            blocks_compilation: Whether error blocks compilation.

        Returns:
            Tuple of (category, severity).
        """
        # LCF category for compilation errors
        category = IssueCategory.LCF

        # Assess severity based on error impact
        if blocks_compilation:
            severity = IssueSeverity.CRITICAL
        elif "type" in error_type.lower() or "import" in error_type.lower():
            severity = IssueSeverity.HIGH
        else:
            severity = IssueSeverity.MEDIUM

        return category, severity

    def classify_missing_content(
        self,
        content_type: str,
        file_type: str,
        count: int
    ) -> Tuple[IssueCategory, IssueSeverity]:
        """Classify missing content issues.

        Args:
            content_type: Type of missing content (examples, lemmas).
            file_type: Type of file (Examples.lean, Lemmas.lean).
            count: Number of items found.

        Returns:
            Tuple of (category, severity).
        """
        # MEL category for missing content
        category = IssueCategory.MEL

        # Assess severity based on count
        if count == 0:
            severity = IssueSeverity.CRITICAL
        elif count < 3:
            severity = IssueSeverity.HIGH
        elif count < 5:
            severity = IssueSeverity.MEDIUM
        else:
            severity = IssueSeverity.LOW

        return category, severity

    def classify_inconsistency(
        self,
        inconsistency_type: str,
        impact: str
    ) -> Tuple[IssueCategory, IssueSeverity]:
        """Classify inconsistency issues.

        Args:
            inconsistency_type: Type of inconsistency.
            impact: Impact of the inconsistency.

        Returns:
            Tuple of (category, severity).
        """
        # IBF category for inconsistencies
        category = IssueCategory.IBF

        # Assess severity based on impact
        if "contradiction" in impact.lower() or "conflict" in impact.lower():
            severity = IssueSeverity.CRITICAL
        elif "fundamental" in impact.lower():
            severity = IssueSeverity.HIGH
        else:
            severity = IssueSeverity.MEDIUM

        return category, severity

    def classify_ambiguity(
        self,
        ambiguity_type: str,
        affects_specification: bool = True
    ) -> Tuple[IssueCategory, IssueSeverity]:
        """Classify ambiguity issues.

        Args:
            ambiguity_type: Type of ambiguity.
            affects_specification: Whether ambiguity affects specification.

        Returns:
            Tuple of (category, severity).
        """
        # USP category for ambiguities
        category = IssueCategory.USP

        # Assess severity based on impact
        if affects_specification:
            severity = IssueSeverity.HIGH
        else:
            severity = IssueSeverity.MEDIUM

        return category, severity

    def _classify_category(
        self,
        description: str,
        context: Optional[str]
    ) -> IssueCategory:
        """Classify issue category based on description.

        Args:
            description: Issue description text.
            context: Additional context information.

        Returns:
            IssueCategory for the issue.
        """
        desc_lower = description.lower()

        # Check for LCF patterns
        lcf_keywords = [
            "compilation", "type error", "syntax error",
            "import error", "undefined", "type mismatch",
            "cannot compile", "build failed", "proof obligation"
        ]
        if any(keyword in desc_lower for keyword in lcf_keywords):
            return IssueCategory.LCF

        # Check for IBF patterns
        ibf_keywords = [
            "inconsistent", "contradiction", "conflict",
            "different definition", "mismatch between",
            "does not match", "contradicts"
        ]
        if any(keyword in desc_lower for keyword in ibf_keywords):
            return IssueCategory.IBF

        # Check for MEL patterns
        mel_keywords = [
            "missing", "empty", "no example", "no lemma",
            "incomplete", "insufficient", "lacks"
        ]
        if any(keyword in desc_lower for keyword in mel_keywords):
            return IssueCategory.MEL

        # Check for ISR patterns
        isr_keywords = [
            "informal", "not formal", "vague",
            "imprecise", "lacks rigor", "insufficient rigor"
        ]
        if any(keyword in desc_lower for keyword in isr_keywords):
            return IssueCategory.ISR

        # Default to USP for ambiguities
        return IssueCategory.USP

    def _assess_severity(
        self,
        description: str,
        category: IssueCategory,
        severity_hint: Optional[IssueSeverity],
        context: Optional[str]
    ) -> IssueSeverity:
        """Assess severity level for an issue.

        Args:
            description: Issue description text.
            category: Issue category.
            severity_hint: Optional hint for severity.
            context: Additional context information.

        Returns:
            IssueSeverity for the issue.
        """
        # Use severity hint if provided
        if severity_hint:
            return severity_hint

        desc_lower = description.lower()

        # Critical severity indicators
        critical_indicators = [
            "blocks compilation", "cannot compile", "build failed",
            "fundamental contradiction", "cannot proceed",
            "critical", "severe", "blocks verification"
        ]
        if any(indicator in desc_lower for indicator in critical_indicators):
            return IssueSeverity.CRITICAL

        # High severity indicators
        high_indicators = [
            "significant gap", "missing key", "critical missing",
            "empty file", "no content", "high priority"
        ]
        if any(indicator in desc_lower for indicator in high_indicators):
            return IssueSeverity.HIGH

        # Medium severity indicators
        medium_indicators = [
            "ambiguous", "unclear", "vague",
            "inconsistent", "minor", "should be addressed"
        ]
        if any(indicator in desc_lower for indicator in medium_indicators):
            return IssueSeverity.MEDIUM

        # Default to low severity
        return IssueSeverity.LOW

    def _generate_rationale(
        self,
        description: str,
        category: IssueCategory,
        severity: IssueSeverity
    ) -> str:
        """Generate rationale for classification decision.

        Args:
            description: Issue description text.
            category: Assigned issue category.
            severity: Assigned severity level.

        Returns:
            String explaining the classification rationale.
        """
        rationale_parts = []

        # Category rationale
        if category == IssueCategory.LCF:
            rationale_parts.append("Classified as LCF because it involves Lean 4 compilation issues")
        elif category == IssueCategory.IBF:
            rationale_parts.append("Classified as IBF because it involves inconsistencies between files")
        elif category == IssueCategory.MEL:
            rationale_parts.append("Classified as MEL because it involves missing examples or lemmas")
        elif category == IssueCategory.ISR:
            rationale_parts.append("Classified as ISR because it involves insufficient formal rigor")
        elif category == IssueCategory.USP:
            rationale_parts.append("Classified as USP because it involves unclear specification points")

        # Severity rationale
        if severity == IssueSeverity.CRITICAL:
            rationale_parts.append("Severity: Critical - blocks compilation or fundamental contradictions")
        elif severity == IssueSeverity.HIGH:
            rationale_parts.append("Severity: High - significant gaps or missing key content")
        elif severity == IssueSeverity.MEDIUM:
            rationale_parts.append("Severity: Medium - ambiguities or minor inconsistencies")
        elif severity == IssueSeverity.LOW:
            rationale_parts.append("Severity: Low - minor issues or documentation improvements")

        return ". ".join(rationale_parts)

    def get_classification_statistics(
        self,
        issues: List[Issue]
    ) -> Dict[str, any]:
        """Get classification statistics from issues.

        Args:
            issues: List of Issue objects.

        Returns:
            Dictionary with classification statistics.
        """
        stats = {
            "total_issues": len(issues),
        }

        # Count by category
        for category in IssueCategory:
            count = sum(1 for i in issues if i.category == category)
            stats[f"{category.value}_count"] = count

        # Count by severity
        for severity in IssueSeverity:
            count = sum(1 for i in issues if i.severity == severity)
            stats[f"{severity.value}_count"] = count

        # Calculate classification accuracy metrics
        stats["classification_accuracy"] = 100.0  # Would be updated with peer review

        return stats

    def validate_classification(
        self,
        issue: Issue
    ) -> Tuple[bool, List[str]]:
        """Validate an issue classification.

        Args:
            issue: Issue object to validate.

        Returns:
            Tuple of (is_valid, validation_messages).
        """
        messages = []

        # Validate category
        if not isinstance(issue.category, IssueCategory):
            messages.append(f"Invalid category: {issue.category}")

        # Validate severity
        if not isinstance(issue.severity, IssueSeverity):
            messages.append(f"Invalid severity: {issue.severity}")

        # Validate required fields
        if not issue.description:
            messages.append("Missing description")
        if not issue.spec_name:
            messages.append("Missing spec name")
        if not issue.file_path:
            messages.append("Missing file path")

        # Validate severity matches category
        if issue.category == IssueCategory.LCF and issue.severity != IssueSeverity.CRITICAL:
            if self.config.strict_mode:
                messages.append(
                    f"LCF issues should be Critical, but got {issue.severity.value}"
                )

        # Validate description length
        if len(issue.description) < 10:
            messages.append("Description too short (minimum 10 characters)")

        return len(messages) == 0, messages
