"""
Specification linter for spec-tools package.

This module implements the SpecLinter class which applies
linting rules to specification files.
"""

from pathlib import Path
from typing import Dict, List

from spec_tools.linting.rules import LintingRule
from spec_tools.linting.rules.change_log import ChangeLogRule
from spec_tools.linting.rules.cross_refs import CrossReferenceRule
from spec_tools.linting.rules.header import HeaderValidationRule
from spec_tools.linting.rules.math import MathNotationRule
from spec_tools.linting.rules.mermaid import MermaidSyntaxRule
from spec_tools.linting.rules.requirements import EARSValidationRule
from spec_tools.linting.rules.sections import SectionStructureRule
from spec_tools.models import LintingConfig, ValidationResult


class SpecLinter:
    """Lints specification files against convention.

    This class implements the LinterInterface and applies a series of
    linting rules to markdown files. Rules are loaded based on
    configuration and run to detect violations.

    The linter can:
    - Lint individual files or entire directories
    - Get descriptions of all available rules
    - Report errors with severity levels and suggestions
    """

    def __init__(self, config: LintingConfig):
        """Initialize specification linter.

        Args:
            config: Linting configuration
        """
        self.config = config
        self.rules: Dict[str, LintingRule] = self._load_rules()

    def _load_rules(self) -> Dict[str, LintingRule]:
        """Load all linting rules based on configuration.

        Returns:
            Dictionary mapping rule names to rule instances
        """
        rules: Dict[str, LintingRule] = {}

        # Always load header and section validation
        rules["header"] = HeaderValidationRule()
        rules["sections"] = SectionStructureRule()

        # Load optional rules based on config
        if self.config.check_ears_pattern:
            rules["ears"] = EARSValidationRule()

        if self.config.check_math_notation:
            rules["math"] = MathNotationRule()

        if self.config.check_mermaid_syntax:
            rules["mermaid"] = MermaidSyntaxRule()

        if self.config.check_cross_references:
            rules["cross_refs"] = CrossReferenceRule()

        # Always load change log validation
        rules["change_log"] = ChangeLogRule()

        return rules

    def lint_file(self, filepath: Path) -> ValidationResult:
        """Lint a single file.

        Runs all enabled linting rules on the specified file
        and aggregates the results.

        Args:
            filepath: Path to the file to lint

        Returns:
            Validation result with any linting issues

        Raises:
            LintingError: If file cannot be read
        """
        try:
            content = filepath.read_text(encoding="utf-8")
            lines = content.split("\n")
            errors = []

            # Run all rules
            for _rule_name, rule in self.rules.items():
                rule_errors = rule.check(content, lines, filepath)
                errors.extend(rule_errors)

            # Determine if validation passed
            passed = all(e.severity.value != "ERROR" for e in errors)

            return ValidationResult(
                file_path=str(filepath),
                errors=errors,
                passed=passed,
            )
        except FileNotFoundError as e:
            from spec_tools.exceptions import LintingError

            raise LintingError(
                f"File not found: {filepath}",
                file_path=str(filepath),
            ) from e
        except Exception as e:
            from spec_tools.exceptions import LintingError

            raise LintingError(
                f"Error linting file: {filepath}",
                file_path=str(filepath),
                details={"error": str(e)},
            ) from e

    def lint_directory(self, directory: Path, recursive: bool = True) -> List[ValidationResult]:
        """Lint all files in a directory.

        Applies linting rules to all markdown files in the specified
        directory, optionally including subdirectories.

        Args:
            directory: Path to the directory
            recursive: Whether to process subdirectories (default: True)

        Returns:
            List of validation results for each file

        Raises:
            LintingError: If directory cannot be accessed
        """
        try:
            pattern = "**/*.md" if recursive else "*.md"
            files = list(directory.glob(pattern))

            results = []
            for filepath in files:
                result = self.lint_file(filepath)
                results.append(result)

            return results
        except Exception as e:
            from spec_tools.exceptions import LintingError

            raise LintingError(
                f"Error linting directory: {directory}",
                file_path=str(directory),
                details={"error": str(e)},
            ) from e

    def get_rules(self) -> Dict[str, str]:
        """Get all available linting rules.

        Returns a dictionary mapping rule names to their descriptions.

        Returns:
            Dictionary mapping rule IDs to descriptions
        """
        return {name: rule.description for name, rule in self.rules.items()}
