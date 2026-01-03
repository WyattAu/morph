"""
Custom exception classes for the spec_tools package.

This module defines a hierarchy of exception classes used throughout
the package for error handling and reporting.
"""


class SpecToolsError(Exception):
    """Base exception class for all spec_tools errors.

    All custom exceptions in the spec_tools package inherit from this
    base class, allowing for consistent error handling and catching.

    Attributes:
        message: Human-readable error message
        details: Optional dictionary with additional error context
    """

    def __init__(self, message: str, details: dict | None = None) -> None:
        """Initialize the exception.

        Args:
            message: Human-readable error message
            details: Optional dictionary with additional error context
        """
        self.message = message
        self.details = details or {}
        super().__init__(self.message)

    def __str__(self) -> str:
        """Return string representation of the exception."""
        if self.details:
            return f"{self.message} Details: {self.details}"
        return self.message


class FormattingError(SpecToolsError):
    """Exception raised when formatting operations fail.

    This exception is raised when there are errors during the formatting
    of specification files, such as invalid file formats, parsing errors,
    or issues applying formatting rules.

    Attributes:
        message: Human-readable error message
        file_path: Path to the file that caused the error
        line_number: Optional line number where the error occurred
        details: Optional dictionary with additional error context
    """

    def __init__(
        self,
        message: str,
        file_path: str | None = None,
        line_number: int | None = None,
        details: dict | None = None,
    ) -> None:
        """Initialize the formatting error.

        Args:
            message: Human-readable error message
            file_path: Path to the file that caused the error
            line_number: Optional line number where the error occurred
            details: Optional dictionary with additional error context
        """
        self.file_path = file_path
        self.line_number = line_number
        super().__init__(message, details)

    def __str__(self) -> str:
        """Return string representation of the exception."""
        location = ""
        if self.file_path:
            location = self.file_path
            if self.line_number is not None:
                location += f":{self.line_number}"
            location += ": "

        if self.details:
            return f"{location}{self.message} Details: {self.details}"
        return f"{location}{self.message}"


class LintingError(SpecToolsError):
    """Exception raised when linting operations fail.

    This exception is raised when there are errors during the linting
    of specification files, such as rule violations, parsing errors,
    or issues with linting configuration.

    Attributes:
        message: Human-readable error message
        file_path: Path to the file that caused the error
        rule_id: Optional identifier of the rule that was violated
        line_number: Optional line number where the error occurred
        details: Optional dictionary with additional error context
    """

    def __init__(
        self,
        message: str,
        file_path: str | None = None,
        rule_id: str | None = None,
        line_number: int | None = None,
        details: dict | None = None,
    ) -> None:
        """Initialize the linting error.

        Args:
            message: Human-readable error message
            file_path: Path to the file that caused the error
            rule_id: Optional identifier of the rule that was violated
            line_number: Optional line number where the error occurred
            details: Optional dictionary with additional error context
        """
        self.file_path = file_path
        self.rule_id = rule_id
        self.line_number = line_number
        super().__init__(message, details)

    def __str__(self) -> str:
        """Return string representation of the exception."""
        location = ""
        if self.file_path:
            location = self.file_path
            if self.line_number is not None:
                location += f":{self.line_number}"
            location += ": "

        rule_info = f"[{self.rule_id}] " if self.rule_id else ""

        if self.details:
            return f"{location}{rule_info}{self.message} Details: {self.details}"
        return f"{location}{rule_info}{self.message}"


class ValidationError(SpecToolsError):
    """Exception raised when validation operations fail.

    This exception is raised when there are errors during the validation
    of specification files, such as missing required sections, invalid
    content, or violations of specification conventions.

    Attributes:
        message: Human-readable error message
        file_path: Path to the file that caused the error
        section: Optional section name where the error occurred
        details: Optional dictionary with additional error context
    """

    def __init__(
        self,
        message: str,
        file_path: str | None = None,
        section: str | None = None,
        details: dict | None = None,
    ) -> None:
        """Initialize the validation error.

        Args:
            message: Human-readable error message
            file_path: Path to the file that caused the error
            section: Optional section name where the error occurred
            details: Optional dictionary with additional error context
        """
        self.file_path = file_path
        self.section = section
        super().__init__(message, details)

    def __str__(self) -> str:
        """Return string representation of the exception."""
        location = ""
        if self.file_path:
            location = self.file_path
            if self.section:
                location += f" (section: {self.section})"
            location += ": "

        if self.details:
            return f"{location}{self.message} Details: {self.details}"
        return f"{location}{self.message}"


class LinkCheckError(SpecToolsError):
    """Exception raised when link checking operations fail.

    This exception is raised when there are errors during the checking
    of links in specification files, such as broken links, orphaned
    sections, or invalid link formats.

    Attributes:
        message: Human-readable error message
        file_path: Path to the file that caused the error
        link_url: The URL or reference that caused the error
        line_number: Optional line number where the error occurred
        details: Optional dictionary with additional error context
    """

    def __init__(
        self,
        message: str,
        file_path: str | None = None,
        link_url: str | None = None,
        line_number: int | None = None,
        details: dict | None = None,
    ) -> None:
        """Initialize the link check error.

        Args:
            message: Human-readable error message
            file_path: Path to the file that caused the error
            link_url: The URL or reference that caused the error
            line_number: Optional line number where the error occurred
            details: Optional dictionary with additional error context
        """
        self.file_path = file_path
        self.link_url = link_url
        self.line_number = line_number
        super().__init__(message, details)

    def __str__(self) -> str:
        """Return string representation of the exception."""
        location = ""
        if self.file_path:
            location = self.file_path
            if self.line_number is not None:
                location += f":{self.line_number}"
            location += ": "

        link_info = f"Link: {self.link_url}" if self.link_url else ""

        if self.details:
            if link_info:
                return f"{location}{self.message} {link_info} Details: {self.details}"
            return f"{location}{self.message} Details: {self.details}"

        if link_info:
            return f"{location}{self.message} {link_info}"
        return f"{location}{self.message}"
