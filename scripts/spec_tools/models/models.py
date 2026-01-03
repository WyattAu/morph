"""
Data models for the spec_tools package.

This module defines dataclasses and enums used throughout the package
for configuration, error reporting, and data structures.
"""

from dataclasses import dataclass, field
from enum import Enum
from pathlib import Path
from typing import List, Optional


class Severity(Enum):
    """Error severity levels.

    Attributes:
        ERROR: Critical error that must be fixed
        WARNING: Issue that should be addressed but doesn't block operations
        INFO: Informational message
    """

    ERROR = "ERROR"
    WARNING = "WARNING"
    INFO = "INFO"


class LinkType(Enum):
    """Types of links found in specification files.

    Attributes:
        MARKDOWN: Link to another markdown file
        SECTION: Link to a section within the same or another file
        FILE: Link to a non-markdown file
        EXTERNAL: Link to an external URL
    """

    MARKDOWN = "markdown"
    SECTION = "section"
    FILE = "file"
    EXTERNAL = "external"


@dataclass
class FormattingConfig:
    """Configuration for formatting operations.

    Attributes:
        max_line_length: Maximum allowed line length (default: 120)
        enforce_trailing_whitespace: Whether to enforce no trailing whitespace
        normalize_lists: Whether to normalize list formatting
        fix_heading_spacing: Whether to fix heading spacing
        normalize_emphasis: Whether to normalize emphasis markers
    """

    max_line_length: int = 120
    enforce_trailing_whitespace: bool = True
    normalize_lists: bool = True
    fix_heading_spacing: bool = True
    normalize_emphasis: bool = True


@dataclass
class LintingConfig:
    """Configuration for linting operations.

    Attributes:
        strict: Whether to treat warnings as errors
        check_ears_pattern: Whether to check EARS pattern compliance
        check_math_notation: Whether to check mathematical notation
        check_mermaid_syntax: Whether to check Mermaid diagram syntax
        check_cross_references: Whether to check cross-references
    """

    strict: bool = False
    check_ears_pattern: bool = True
    check_math_notation: bool = True
    check_mermaid_syntax: bool = True
    check_cross_references: bool = True


@dataclass
class ValidationConfig:
    """Configuration for validation operations.

    Attributes:
        check_traceability: Whether to check traceability matrix
        check_verification_plan: Whether to check verification plan
        check_risk_assessment: Whether to check risk assessment
        check_security_specs: Whether to check security specifications
        check_performance_specs: Whether to check performance specifications
        check_maintainability_specs: Whether to check maintainability specifications
    """

    check_traceability: bool = True
    check_verification_plan: bool = True
    check_risk_assessment: bool = True
    check_security_specs: bool = True
    check_performance_specs: bool = True
    check_maintainability_specs: bool = True


@dataclass
class LinkCheckingConfig:
    """Configuration for link checking operations.

    Attributes:
        check_broken_links: Whether to check for broken links
        check_orphaned_sections: Whether to check for orphaned sections
        check_duplicate_links: Whether to check for duplicate links
        check_self_references: Whether to check for self-references
    """

    check_broken_links: bool = True
    check_orphaned_sections: bool = True
    check_duplicate_links: bool = True
    check_self_references: bool = False


@dataclass
class OutputConfig:
    """Configuration for output formatting.

    Attributes:
        format: Output format (text or json)
        verbose: Whether to enable verbose output
        quiet: Whether to suppress non-error output
        color_output: Whether to enable colored output
    """

    format: str = "text"
    verbose: bool = False
    quiet: bool = False
    color_output: bool = True


@dataclass
class Config:
    """Main configuration class for spec-tools.

    This class aggregates all configuration options for the spec-tools package.
    It can be loaded from a YAML file or created with default values.

    Attributes:
        formatting: Formatting configuration
        linting: Linting configuration
        validation: Validation configuration
        link_checking: Link checking configuration
        output: Output configuration
    """

    formatting: FormattingConfig = field(default_factory=FormattingConfig)
    linting: LintingConfig = field(default_factory=LintingConfig)
    validation: ValidationConfig = field(default_factory=ValidationConfig)
    link_checking: LinkCheckingConfig = field(default_factory=LinkCheckingConfig)
    output: OutputConfig = field(default_factory=OutputConfig)


@dataclass
class LintError:
    """Represents a linting error or warning.

    This dataclass captures information about a single linting issue,
    including its location, severity, and optional suggestions for fixing it.

    Attributes:
        file_path: Path to the file where the error occurred
        line_number: Line number where the error occurred
        column_number: Optional column number where the error occurred
        severity: Severity level of the error
        rule_id: Identifier of the rule that was violated
        message: Human-readable error message
        suggestion: Optional suggestion for fixing the error
        context: Optional context lines around the error
    """

    file_path: str
    line_number: int
    column_number: int = 0
    severity: Severity = Severity.ERROR
    rule_id: str = ""
    message: str = ""
    suggestion: Optional[str] = None
    context: Optional[str] = None

    def __str__(self) -> str:
        """Format error for display.

        Returns:
            Formatted error string with location, severity, and message
        """
        location = f"{self.file_path}:{self.line_number}"
        if self.column_number > 0:
            location += f":{self.column_number}"

        severity_str = f"[{self.severity.value}]"
        result = f"{location} {severity_str} {self.rule_id}: {self.message}"

        if self.suggestion:
            result += f"\n  Suggestion: {self.suggestion}"

        if self.context:
            result += f"\n  Context: {self.context}"

        return result


@dataclass
class ValidationResult:
    """Result of validating a file or directory.

    This dataclass captures the results of a validation operation,
    including all errors found and whether the validation passed.

    Attributes:
        file_path: Path to the file that was validated
        errors: List of errors found during validation
        passed: Whether validation passed (no ERROR severity issues)
    """

    file_path: str
    errors: List[LintError] = field(default_factory=list)
    passed: bool = True

    @property
    def error_count(self) -> int:
        """Count of ERROR severity issues.

        Returns:
            Number of errors with ERROR severity
        """
        return sum(1 for e in self.errors if e.severity == Severity.ERROR)

    @property
    def warning_count(self) -> int:
        """Count of WARNING severity issues.

        Returns:
            Number of errors with WARNING severity
        """
        return sum(1 for e in self.errors if e.severity == Severity.WARNING)

    @property
    def info_count(self) -> int:
        """Count of INFO severity issues.

        Returns:
            Number of errors with INFO severity
        """
        return sum(1 for e in self.errors if e.severity == Severity.INFO)

    @property
    def total_count(self) -> int:
        """Total count of all issues.

        Returns:
            Total number of errors, warnings, and info messages
        """
        return len(self.errors)


@dataclass
class LinkInfo:
    """Information about a single link.

    This dataclass captures information about a link found in a
    specification file, including its location and validation status.

    Attributes:
        text: Link text
        url: Link URL or reference
        line_number: Line number where the link was found
        column_number: Optional column number where the link was found
        file_path: Path to the file containing the link
        link_type: Type of link (markdown, section, file, or external)
        is_valid: Whether the link is valid
        error_message: Optional error message if link is invalid
    """

    text: str
    url: str
    line_number: int
    column_number: int = 0
    file_path: Path = field(default_factory=Path)
    link_type: LinkType = LinkType.EXTERNAL
    is_valid: bool = False
    error_message: Optional[str] = None


@dataclass
class LinkReport:
    """Report for link checking results.

    This dataclass aggregates the results of link checking operations,
    including statistics and lists of issues found.

    Attributes:
        file_path: Path to the file or directory that was checked
        total_links: Total number of links found
        valid_links: Number of valid links
        broken_links: List of broken links
        orphaned_sections: List of orphaned section references
        duplicate_links: List of duplicate link tuples
        self_references: List of self-referencing links
    """

    file_path: Path
    total_links: int = 0
    valid_links: int = 0
    broken_links: List[LinkInfo] = field(default_factory=list)
    orphaned_sections: List[LinkInfo] = field(default_factory=list)
    duplicate_links: List[tuple] = field(default_factory=list)
    self_references: List[LinkInfo] = field(default_factory=list)

    @property
    def invalid_count(self) -> int:
        """Count of invalid links.

        Returns:
            Number of invalid links (broken + orphaned + self-references)
        """
        return (
            len(self.broken_links)
            + len(self.orphaned_sections)
            + len(self.self_references)
        )

    @property
    def duplicate_count(self) -> int:
        """Count of duplicate link groups.

        Returns:
            Number of duplicate link groups found
        """
        return len(self.duplicate_links)

    @property
    def passed(self) -> bool:
        """Whether link checking passed.

        Returns:
            True if no invalid links were found, False otherwise
        """
        return self.invalid_count == 0
