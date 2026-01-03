"""
Logging utilities for the spec_tools package.

This module provides functionality for setting up and configuring
logging with support for different output formats and verbosity levels.
"""

import json
import logging
import sys
from typing import Any

from spec_tools.models import OutputConfig


class JSONFormatter(logging.Formatter):
    """Custom formatter for JSON log output.

    This formatter formats log records as JSON objects, which is
    useful for log aggregation and analysis tools.
    """

    def format(self, record: logging.LogRecord) -> str:
        """Format log record as JSON.

        Args:
            record: Log record to format

        Returns:
            JSON-formatted log message
        """
        log_data: dict[str, Any] = {
            "timestamp": self.formatTime(record, self.datefmt),
            "level": record.levelname,
            "logger": record.name,
            "message": record.getMessage(),
        }

        if record.pathname:
            log_data["file"] = record.pathname
        if record.lineno:
            log_data["line"] = record.lineno
        if record.funcName:
            log_data["function"] = record.funcName

        if record.exc_info:
            log_data["exception"] = self.formatException(record.exc_info)

        return json.dumps(log_data)


class ColoredFormatter(logging.Formatter):
    """Custom formatter with color support for terminal output.

    This formatter adds ANSI color codes to log messages based on
    their severity level, making them easier to read in terminal output.
    """

    # ANSI color codes
    COLORS = {
        "DEBUG": "\033[36m",  # Cyan
        "INFO": "\033[32m",  # Green
        "WARNING": "\033[33m",  # Yellow
        "ERROR": "\033[31m",  # Red
        "CRITICAL": "\033[35m",  # Magenta
    }
    RESET = "\033[0m"

    def format(self, record: logging.LogRecord) -> str:
        """Format log record with colors.

        Args:
            record: Log record to format

        Returns:
            Color-formatted log message
        """
        levelname = record.levelname
        if levelname in self.COLORS:
            record.levelname = f"{self.COLORS[levelname]}{levelname}{self.RESET}"

        result = super().format(record)

        # Reset levelname for subsequent formatting
        record.levelname = levelname

        return result


def setup_logging(config: OutputConfig) -> None:
    """Set up logging configuration based on output config.

    This function configures the root logger with the specified
    output format, verbosity level, and other options.

    Args:
        config: Output configuration object

    Raises:
        ValueError: If both verbose and quiet are True
    """
    if config.verbose and config.quiet:
        raise ValueError("verbose and quiet cannot both be True")

    # Determine log level
    if config.quiet:
        log_level = logging.ERROR
    elif config.verbose:
        log_level = logging.DEBUG
    else:
        log_level = logging.INFO

    # Get root logger
    root_logger = logging.getLogger()
    root_logger.setLevel(log_level)

    # Remove existing handlers
    root_logger.handlers.clear()

    # Create handler
    handler = logging.StreamHandler(sys.stderr)
    handler.setLevel(log_level)

    # Set formatter based on output format
    if config.format == "json":
        formatter = JSONFormatter()
    elif config.color_output and sys.stderr.isatty():
        formatter = ColoredFormatter(
            fmt="%(asctime)s %(levelname)s %(name)s: %(message)s",
            datefmt="%Y-%m-%d %H:%M:%S",
        )
    else:
        formatter = logging.Formatter(
            fmt="%(asctime)s %(levelname)s %(name)s: %(message)s",
            datefmt="%Y-%m-%d %H:%M:%S",
        )

    handler.setFormatter(formatter)
    root_logger.addHandler(handler)


def get_logger(name: str) -> logging.Logger:
    """Get a logger instance with the specified name.

    Args:
        name: Name for the logger (typically __name__)

    Returns:
        Logger instance
    """
    return logging.getLogger(name)


def log_dict(logger: logging.Logger, level: str, data: dict[str, Any]) -> None:
    """Log a dictionary as formatted JSON.

    Args:
        logger: Logger instance to use
        level: Log level (debug, info, warning, error, critical)
        data: Dictionary to log

    Raises:
        ValueError: If level is not a valid log level
    """
    level_map = {
        "debug": logger.debug,
        "info": logger.info,
        "warning": logger.warning,
        "error": logger.error,
        "critical": logger.critical,
    }

    if level not in level_map:
        raise ValueError(f"Invalid log level: {level}")

    log_func = level_map[level]
    log_func(json.dumps(data, indent=2))
