"""
Main validator class for specification files.

This module implements the SpecValidator class, which provides validation
functionality for specification files using various validation checks.
"""

from pathlib import Path
from typing import List

from spec_tools.models import LintError, ValidationConfig, ValidationResult
from spec_tools.validation.checks import ValidationCheck
from spec_tools.validation.checks.maintainability import MaintainabilitySpecCheck
from spec_tools.validation.checks.performance import PerformanceSpecCheck
from spec_tools.validation.checks.risk_assessment import RiskAssessmentCheck
from spec_tools.validation.checks.security import SecuritySpecCheck
from spec_tools.validation.checks.traceability import TraceabilityCheck
from spec_tools.validation.checks.verification import VerificationPlanCheck


class SpecValidator:
    """Validates specification files against enhanced convention.

    This class implements validation functionality for specification files,
    running various checks to ensure compliance with the specification
    convention including traceability, verification plans, risk assessment,
    security specifications, performance specifications, and maintainability.

    Attributes:
        config: Validation configuration
        checks: List of validation checks to run
    """

    def __init__(self, config: ValidationConfig) -> None:
        """Initialize the validator.

        Args:
            config: Validation configuration
        """
        self.config = config
        self.checks: List[ValidationCheck] = self._load_checks()

    def _load_checks(self) -> List[ValidationCheck]:
        """Load validation checks based on configuration.

        Returns:
            List of validation checks to run
        """
        checks: List[ValidationCheck] = []

        if self.config.check_traceability:
            checks.append(TraceabilityCheck())

        if self.config.check_verification_plan:
            checks.append(VerificationPlanCheck())

        if self.config.check_risk_assessment:
            checks.append(RiskAssessmentCheck())

        if self.config.check_security_specs:
            checks.append(SecuritySpecCheck())

        if self.config.check_performance_specs:
            checks.append(PerformanceSpecCheck())

        if self.config.check_maintainability_specs:
            checks.append(MaintainabilitySpecCheck())

        return checks

    def validate_file(self, filepath: Path) -> ValidationResult:
        """Validate a single specification file.

        Args:
            filepath: Path to the file to validate

        Returns:
            Validation result with any validation issues

        Raises:
            FileNotFoundError: If the file does not exist
            IOError: If the file cannot be read
        """
        if not filepath.exists():
            raise FileNotFoundError(f"File not found: {filepath}")

        if not filepath.is_file():
            raise OSError(f"Path is not a file: {filepath}")

        # Read file content
        content = filepath.read_text(encoding="utf-8")

        # Run all checks
        errors: List[LintError] = []
        for check in self.checks:
            check_errors = check.validate(content, filepath)
            errors.extend(check_errors)

        # Determine if validation passed
        passed = all(error.severity.value != "ERROR" for error in errors)

        return ValidationResult(
            file_path=str(filepath),
            errors=errors,
            passed=passed,
        )

    def validate_directory(self, directory: Path, recursive: bool = True) -> List[ValidationResult]:
        """Validate all specification files in a directory.

        Args:
            directory: Path to the directory to validate
            recursive: Whether to process subdirectories (default: True)

        Returns:
            List of validation results for each file

        Raises:
            FileNotFoundError: If the directory does not exist
            NotADirectoryError: If the path is not a directory
        """
        if not directory.exists():
            raise FileNotFoundError(f"Directory not found: {directory}")

        if not directory.is_dir():
            raise NotADirectoryError(f"Path is not a directory: {directory}")

        # Find all markdown files
        pattern = "**/*.md" if recursive else "*.md"
        files = list(directory.glob(pattern))

        # Validate each file
        results: List[ValidationResult] = []
        for filepath in files:
            try:
                result = self.validate_file(filepath)
                results.append(result)
            except (OSError, FileNotFoundError) as e:
                # Add error result for files that couldn't be read
                results.append(
                    ValidationResult(
                        file_path=str(filepath),
                        errors=[
                            LintError(
                                file_path=str(filepath),
                                line_number=1,
                                message=f"Failed to read file: {e}",
                            )
                        ],
                        passed=False,
                    )
                )

        return results

    def check_traceability(self, content: str) -> List[LintError]:
        """Check traceability matrix in content.

        Args:
            content: File content to check

        Returns:
            List of traceability issues
        """
        traceability_check = TraceabilityCheck()
        return traceability_check.validate(content, Path())

    def check_verification_plan(self, content: str) -> List[LintError]:
        """Check verification plan in content.

        Args:
            content: File content to check

        Returns:
            List of verification plan issues
        """
        verification_check = VerificationPlanCheck()
        return verification_check.validate(content, Path())

    def check_risk_assessment(self, content: str) -> List[LintError]:
        """Check risk assessment in content.

        Args:
            content: File content to check

        Returns:
            List of risk assessment issues
        """
        risk_check = RiskAssessmentCheck()
        return risk_check.validate(content, Path())

    def check_security_specs(self, content: str) -> List[LintError]:
        """Check security specifications in content.

        Args:
            content: File content to check

        Returns:
            List of security specification issues
        """
        security_check = SecuritySpecCheck()
        return security_check.validate(content, Path())

    def check_performance_specs(self, content: str) -> List[LintError]:
        """Check performance specifications in content.

        Args:
            content: File content to check

        Returns:
            List of performance specification issues
        """
        performance_check = PerformanceSpecCheck()
        return performance_check.validate(content, Path())

    def check_maintainability_specs(self, content: str) -> List[LintError]:
        """Check maintainability specifications in content.

        Args:
            content: File content to check

        Returns:
            List of maintainability specification issues
        """
        maintainability_check = MaintainabilitySpecCheck()
        return maintainability_check.validate(content, Path())


__all__ = ["SpecValidator"]
