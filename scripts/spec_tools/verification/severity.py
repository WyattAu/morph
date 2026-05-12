"""
Severity Assessment Tool

This module provides tools for assessing issue severity according to
ADR-006 criteria, ensuring consistent severity assignment across all issues.

The tool supports:
- Four-level severity system (Critical, High, Medium, Low)
- Severity assessment matrix for consistency
- Peer review support and audit trails
- Resource allocation guidelines based on severity
"""

from dataclasses import dataclass, field
from typing import Any, Dict, List, Optional, Tuple

from spec_tools.verification.models import (
    Issue,
    IssueCategory,
    IssueSeverity,
)


@dataclass
class SeverityConfig:
    """Configuration for severity assessment.

    Attributes:
        strict_mode: Whether to enforce strict severity rules
        require_rationale: Whether to require rationale for severity
        enable_peer_review: Whether to enable peer review workflow
        resource_allocation: Resource allocation percentages by severity
    """

    strict_mode: bool = False
    require_rationale: bool = True
    enable_peer_review: bool = True
    resource_allocation: Dict[IssueSeverity, float] = field(
        default_factory=lambda: {
            IssueSeverity.CRITICAL: 0.50,  # 50% of resources
            IssueSeverity.HIGH: 0.30,  # 30% of resources
            IssueSeverity.MEDIUM: 0.15,  # 15% of resources
            IssueSeverity.LOW: 0.05,  # 5% of resources
        }
    )


class SeverityAssessor:
    """Assesses issue severity according to ADR-006 criteria.

    This class implements ADR-006's four-level severity system,
    providing consistent severity assessment with clear criteria and
    resource allocation guidelines.
    """

    # Severity characteristics from ADR-006
    _CRITICAL_CHARACTERISTICS = {
        "blocks_compilation": True,
        "fundamental_contradiction": True,
        "missing_core_definition": True,
        "type_error_blocks_verification": True,
        "proof_obligation_unsatisfied": True,
    }

    _HIGH_CHARACTERISTICS = {
        "significant_gap_rigor": True,
        "missing_key_lemma": True,
        "missing_key_example": True,
        "informal_description": True,
        "empty_lemma_file": True,
        "empty_example_file": True,
    }

    _MEDIUM_CHARACTERISTICS = {
        "ambiguity_terminology": True,
        "minor_inconsistency": True,
        "incomplete_example": True,
        "vague_quantifier": True,
        "unclear_requirement": True,
    }

    _LOW_CHARACTERISTICS = {
        "documentation_improvement": True,
        "formatting_issue": True,
        "minor_edge_case": True,
        "style_improvement": True,
        "non_critical_clarification": True,
    }

    def __init__(self, config: Optional[SeverityConfig] = None):
        """Initialize assessor with optional configuration.

        Args:
            config: Severity assessment configuration. If None, uses defaults.
        """
        self.config = config or SeverityConfig()
        self._severity_counters: Dict[IssueSeverity, int] = {
            IssueSeverity.CRITICAL: 0,
            IssueSeverity.HIGH: 0,
            IssueSeverity.MEDIUM: 0,
            IssueSeverity.LOW: 0,
        }

    def assess_severity(
        self, issue: Issue, override_severity: Optional[IssueSeverity] = None
    ) -> Tuple[IssueSeverity, str]:
        """Assess severity for a given issue.

        Args:
            issue: Issue object to assess.
            override_severity: Optional override for severity.

        Returns:
            Tuple of (severity, rationale).
        """
        # Use override if provided
        if override_severity:
            severity = override_severity
            rationale = f"Severity overridden to {severity.value}"
            return severity, rationale

        # Assess based on category and description
        severity = self._assess_by_category(issue)
        rationale = self._generate_rationale(issue, severity)

        return severity, rationale

    def assess_compilation_error(
        self, error_type: str, blocks_compilation: bool = True, error_message: str = ""
    ) -> IssueSeverity:
        """Assess severity for a compilation error.

        Args:
            error_type: Type of compilation error.
            blocks_compilation: Whether error blocks compilation.
            error_message: Full error message.

        Returns:
            IssueSeverity for the compilation error.
        """
        # Critical if blocks compilation
        if blocks_compilation:
            return IssueSeverity.CRITICAL

        # High for type errors
        if "type" in error_type.lower() or "import" in error_type.lower():
            return IssueSeverity.HIGH

        # Medium for other errors
        return IssueSeverity.MEDIUM

    def assess_missing_content(self, content_type: str, file_type: str, count: int) -> IssueSeverity:
        """Assess severity for missing content issues.

        Args:
            content_type: Type of missing content (examples, lemmas).
            file_type: Type of file (Examples.lean, Lemmas.lean).
            count: Number of items found.

        Returns:
            IssueSeverity for the missing content issue.
        """
        # Critical if completely empty
        if count == 0:
            return IssueSeverity.CRITICAL

        # High if very few items
        if count < 3:
            return IssueSeverity.HIGH

        # Medium if moderate number of items
        if count < 5:
            return IssueSeverity.MEDIUM

        return IssueSeverity.LOW

    def assess_inconsistency(
        self, inconsistency_type: str, impact: str, affects_core_specification: bool = False
    ) -> IssueSeverity:
        """Assess severity for inconsistency issues.

        Args:
            inconsistency_type: Type of inconsistency.
            impact: Impact description.
            affects_core_specification: Whether inconsistency affects core specification.

        Returns:
            IssueSeverity for the inconsistency.
        """
        impact_lower = impact.lower()

        # Critical for fundamental contradictions
        if any(
            keyword in impact_lower for keyword in ["contradiction", "conflict", "fundamental", "cannot be resolved"]
        ):
            return IssueSeverity.CRITICAL

        # High if affects core specification
        if affects_core_specification:
            return IssueSeverity.HIGH

        # Medium for other inconsistencies
        return IssueSeverity.MEDIUM

    def assess_ambiguity(self, ambiguity_type: str, affects_specification: bool = True) -> IssueSeverity:
        """Assess severity for ambiguity issues.

        Args:
            ambiguity_type: Type of ambiguity.
            affects_specification: Whether ambiguity affects specification.

        Returns:
            IssueSeverity for the ambiguity.
        """
        # High if affects specification
        if affects_specification:
            return IssueSeverity.HIGH

        return IssueSeverity.MEDIUM

    def _assess_by_category(self, issue: Issue) -> IssueSeverity:
        """Assess severity based on issue category and description.

        Args:
            issue: Issue object to assess.

        Returns:
            IssueSeverity for the issue.
        """
        desc_lower = issue.description.lower()

        # Category-specific assessment
        if issue.category == IssueCategory.LCF:
            return self._assess_lcf_severity(issue, desc_lower)
        elif issue.category == IssueCategory.IBF:
            return self._assess_ibf_severity(issue, desc_lower)
        elif issue.category == IssueCategory.MEL:
            return self._assess_mel_severity(issue, desc_lower)
        elif issue.category == IssueCategory.ISR:
            return self._assess_isr_severity(issue, desc_lower)
        elif issue.category == IssueCategory.USP:
            return self._assess_usp_severity(issue, desc_lower)
        else:
            return IssueSeverity.MEDIUM

    def _assess_lcf_severity(self, issue: Issue, desc_lower: str) -> IssueSeverity:
        """Assess severity for LCF (Lean 4 Compilation Failures) issues.

        Args:
            issue: Issue object.
            desc_lower: Lowercase description.

        Returns:
            IssueSeverity for LCF issues.
        """
        # Check for critical characteristics
        for characteristic in self._CRITICAL_CHARACTERISTICS:
            if characteristic in desc_lower:
                return IssueSeverity.CRITICAL

        # Check for high characteristics
        for characteristic in self._HIGH_CHARACTERISTICS:
            if characteristic in desc_lower:
                return IssueSeverity.HIGH

        return IssueSeverity.MEDIUM

    def _assess_ibf_severity(self, issue: Issue, desc_lower: str) -> IssueSeverity:
        """Assess severity for IBF (Inconsistencies Between Files) issues.

        Args:
            issue: Issue object.
            desc_lower: Lowercase description.

        Returns:
            IssueSeverity for IBF issues.
        """
        # Check for critical characteristics
        if any(keyword in desc_lower for keyword in ["contradiction", "conflict", "fundamental", "cannot coexist"]):
            return IssueSeverity.CRITICAL

        # Check for high characteristics
        if any(keyword in desc_lower for keyword in ["different definition", "mismatch", "inconsistent type"]):
            return IssueSeverity.HIGH

        return IssueSeverity.MEDIUM

    def _assess_mel_severity(self, issue: Issue, desc_lower: str) -> IssueSeverity:
        """Assess severity for MEL (Missing Examples or Lemmas) issues.

        Args:
            issue: Issue object.
            desc_lower: Lowercase description.

        Returns:
            IssueSeverity for MEL issues.
        """
        # Check for critical characteristics
        if any(keyword in desc_lower for keyword in ["empty", "no content", "completely missing"]):
            return IssueSeverity.CRITICAL

        # Check for high characteristics
        if any(keyword in desc_lower for keyword in ["missing key", "significant gap", "no example", "no lemma"]):
            return IssueSeverity.HIGH

        return IssueSeverity.MEDIUM

    def _assess_isr_severity(self, issue: Issue, desc_lower: str) -> IssueSeverity:
        """Assess severity for ISR (Insufficient Rigor) issues.

        Args:
            issue: Issue object.
            desc_lower: Lowercase description.

        Returns:
            IssueSeverity for ISR issues.
        """
        # Check for high characteristics
        if any(keyword in desc_lower for keyword in ["informal", "not formal", "lacks rigor", "insufficient"]):
            return IssueSeverity.HIGH

        return IssueSeverity.MEDIUM

    def _assess_usp_severity(self, issue: Issue, desc_lower: str) -> IssueSeverity:
        """Assess severity for USP (Unclear Specification Points) issues.

        Args:
            issue: Issue object.
            desc_lower: Lowercase description.

        Returns:
            IssueSeverity for USP issues.
        """
        # Check for high characteristics
        if any(keyword in desc_lower for keyword in ["ambiguous", "unclear", "vague", "multiple interpretation"]):
            return IssueSeverity.HIGH

        return IssueSeverity.MEDIUM

    def _generate_rationale(self, issue: Issue, severity: IssueSeverity) -> str:
        """Generate rationale for severity assessment.

        Args:
            issue: Issue object.
            severity: Assigned severity level.

        Returns:
            String explaining the severity rationale.
        """
        rationale_parts = []

        # Category-specific rationale
        if issue.category == IssueCategory.LCF:
            if severity == IssueSeverity.CRITICAL:
                rationale_parts.append("Blocks compilation, requires immediate attention")
            elif severity == IssueSeverity.HIGH:
                rationale_parts.append("Type error or import issue, address in current iteration")
            else:
                rationale_parts.append("Compilation error, address in next iteration")

        elif issue.category == IssueCategory.IBF:
            if severity == IssueSeverity.CRITICAL:
                rationale_parts.append("Fundamental contradiction between files")
            elif severity == IssueSeverity.HIGH:
                rationale_parts.append("Definition mismatch between files")
            else:
                rationale_parts.append("Minor inconsistency between files")

        elif issue.category == IssueCategory.MEL:
            if severity == IssueSeverity.CRITICAL:
                rationale_parts.append("Empty or missing critical content")
            elif severity == IssueSeverity.HIGH:
                rationale_parts.append("Missing key examples or lemmas")
            else:
                rationale_parts.append("Insufficient examples or lemmas")

        elif issue.category == IssueCategory.ISR:
            if severity == IssueSeverity.HIGH:
                rationale_parts.append("Informal description, lacks formal rigor")
            else:
                rationale_parts.append("Minor rigor issue")

        elif issue.category == IssueCategory.USP:
            if severity == IssueSeverity.HIGH:
                rationale_parts.append("Ambiguous specification, multiple interpretations")
            else:
                rationale_parts.append("Minor ambiguity in specification")

        return ". ".join(rationale_parts)

    def get_priority_order(self, issues: List[Issue]) -> List[Issue]:
        """Sort issues by priority (severity and category).

        Args:
            issues: List of Issue objects.

        Returns:
            List of issues sorted by priority.
        """

        def priority_key(issue: Issue) -> Tuple[int, int]:
            """Generate priority key for sorting.

            Higher severity = lower key value (higher priority).
            Within same severity, use category priority.
            """
            severity_order = {
                IssueSeverity.CRITICAL: 0,
                IssueSeverity.HIGH: 1,
                IssueSeverity.MEDIUM: 2,
                IssueSeverity.LOW: 3,
            }
            category_order = {
                IssueCategory.LCF: 0,
                IssueCategory.IBF: 1,
                IssueCategory.MEL: 2,
                IssueCategory.ISR: 3,
                IssueCategory.USP: 4,
            }
            return (severity_order.get(issue.severity, 2), category_order.get(issue.category, 4))

        return sorted(issues, key=priority_key)

    def get_resource_allocation(self, issues: List[Issue]) -> Dict[IssueSeverity, int]:
        """Calculate resource allocation based on severity distribution.

        Args:
            issues: List of Issue objects.

        Returns:
            Dictionary with resource allocation by severity.
        """
        total_issues = len(issues)
        if total_issues == 0:
            return dict.fromkeys(IssueSeverity, 0)

        allocation = {}
        for severity in IssueSeverity:
            sum(1 for i in issues if i.severity == severity)
            percentage = self.config.resource_allocation.get(severity, 0.0)
            allocation[severity] = int(total_issues * percentage)

        return allocation

    def get_severity_statistics(self, issues: List[Issue]) -> Dict[str, Any]:
        """Get severity statistics from issues.

        Args:
            issues: List of Issue objects.

        Returns:
            Dictionary with severity statistics.
        """
        stats: Dict[str, Any] = {
            "total_issues": len(issues),
        }

        # Count by severity
        for severity in IssueSeverity:
            count = sum(1 for i in issues if i.severity == severity)
            stats[f"{severity.value}_count"] = count
            stats[f"{severity.value}_percentage"] = float((count / len(issues) * 100) if issues else 0)

        # Calculate priority distribution
        critical_count = sum(1 for i in issues if i.severity == IssueSeverity.CRITICAL)
        stats["critical_priority"] = critical_count > 0
        stats["high_priority"] = sum(1 for i in issues if i.severity == IssueSeverity.HIGH) > 0

        return stats

    def validate_severity(self, issue: Issue) -> Tuple[bool, List[str]]:
        """Validate severity assignment for an issue.

        Args:
            issue: Issue object to validate.

        Returns:
            Tuple of (is_valid, validation_messages).
        """
        messages = []

        # Validate severity matches category
        if issue.category == IssueCategory.LCF and issue.severity != IssueSeverity.CRITICAL:
            if self.config.strict_mode:
                messages.append(f"LCF issues should be Critical, but got {issue.severity.value}")

        # Validate severity is within allowed range
        if not isinstance(issue.severity, IssueSeverity):
            messages.append(f"Invalid severity: {issue.severity}")

        # Validate rationale is provided if required
        if self.config.require_rationale and not issue.notes:
            messages.append("Rationale required for severity assessment")

        return len(messages) == 0, messages
