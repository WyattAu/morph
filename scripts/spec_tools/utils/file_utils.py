"""
File system utilities for the spec_tools package.

This module provides utility functions for file system operations,
including finding markdown files and safe file reading/writing.
"""

from pathlib import Path
from typing import List

from spec_tools.exceptions import SpecToolsError


def find_markdown_files(directory: Path, recursive: bool = True) -> List[Path]:
    """Find all markdown files in a directory.

    This function searches for markdown files (.md extension) in the
    specified directory. It can search recursively through subdirectories
    or only in the top-level directory.

    Args:
        directory: Path to the directory to search
        recursive: Whether to search recursively through subdirectories

    Returns:
        List of paths to markdown files found

    Raises:
        SpecToolsError: If the directory does not exist or is not a directory
    """
    if not directory.exists():
        raise SpecToolsError(
            f"Directory does not exist: {directory}",
            details={"directory": str(directory)},
        )

    if not directory.is_dir():
        raise SpecToolsError(
            f"Path is not a directory: {directory}",
            details={"directory": str(directory)},
        )

    if recursive:
        # Search recursively
        markdown_files = sorted(directory.rglob("*.md"))
    else:
        # Search only in top-level directory
        markdown_files = sorted(directory.glob("*.md"))

    return markdown_files


def read_file_safely(filepath: Path) -> str:
    """Read a file safely with error handling.

    This function reads the contents of a file with proper error handling
    for common issues like file not found, permission errors, and encoding
    issues.

    Args:
        filepath: Path to the file to read

    Returns:
        Contents of the file as a string

    Raises:
        SpecToolsError: If the file cannot be read
    """
    try:
        with open(filepath, "r", encoding="utf-8") as f:
            return f.read()
    except FileNotFoundError as e:
        raise SpecToolsError(
            f"File not found: {filepath}",
            details={"filepath": str(filepath)},
        ) from e
    except PermissionError as e:
        raise SpecToolsError(
            f"Permission denied reading file: {filepath}",
            details={"filepath": str(filepath)},
        ) from e
    except UnicodeDecodeError as e:
        raise SpecToolsError(
            f"Encoding error reading file: {filepath}",
            details={"filepath": str(filepath), "encoding": "utf-8"},
        ) from e
    except Exception as e:
        raise SpecToolsError(
            f"Error reading file: {filepath}",
            details={"filepath": str(filepath), "error": str(e)},
        ) from e


def write_file_safely(filepath: Path, content: str) -> None:
    """Write content to a file safely with error handling.

    This function writes content to a file with proper error handling
    for common issues like permission errors and disk full errors.
    It also creates parent directories if they don't exist.

    Args:
        filepath: Path to the file to write
        content: Content to write to the file

    Raises:
        SpecToolsError: If the file cannot be written
    """
    try:
        # Create parent directories if they don't exist
        filepath.parent.mkdir(parents=True, exist_ok=True)

        with open(filepath, "w", encoding="utf-8") as f:
            f.write(content)
    except PermissionError as e:
        raise SpecToolsError(
            f"Permission denied writing file: {filepath}",
            details={"filepath": str(filepath)},
        ) from e
    except OSError as e:
        raise SpecToolsError(
            f"Error writing file: {filepath}",
            details={"filepath": str(filepath), "error": str(e)},
        ) from e
    except Exception as e:
        raise SpecToolsError(
            f"Unexpected error writing file: {filepath}",
            details={"filepath": str(filepath), "error": str(e)},
        ) from e


def ensure_directory_exists(directory: Path) -> None:
    """Ensure a directory exists, creating it if necessary.

    This function checks if a directory exists and creates it (and any
    parent directories) if it doesn't exist.

    Args:
        directory: Path to the directory to ensure exists

    Raises:
        SpecToolsError: If the directory cannot be created
    """
    try:
        directory.mkdir(parents=True, exist_ok=True)
    except PermissionError as e:
        raise SpecToolsError(
            f"Permission denied creating directory: {directory}",
            details={"directory": str(directory)},
        ) from e
    except OSError as e:
        raise SpecToolsError(
            f"Error creating directory: {directory}",
            details={"directory": str(directory), "error": str(e)},
        ) from e
    except Exception as e:
        raise SpecToolsError(
            f"Unexpected error creating directory: {directory}",
            details={"directory": str(directory), "error": str(e)},
        ) from e


def get_relative_path(filepath: Path, base_path: Path) -> Path:
    """Get the relative path of a file from a base path.

    This function calculates the relative path of a file from a base
    directory. This is useful for displaying file paths in a more
    user-friendly way.

    Args:
        filepath: Path to the file
        base_path: Base path to calculate relative path from

    Returns:
        Relative path from base_path to filepath

    Raises:
        SpecToolsError: If the paths are not on the same drive or
            if the relative path cannot be calculated
    """
    try:
        return filepath.relative_to(base_path)
    except ValueError as e:
        raise SpecToolsError(
            f"Cannot calculate relative path: {filepath} from {base_path}",
            details={
                "filepath": str(filepath),
                "base_path": str(base_path),
            },
        ) from e
