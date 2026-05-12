"""Tests for logging_utils."""

import json
import logging

import pytest

from spec_tools.models import OutputConfig
from spec_tools.utils.logging_utils import (
    JSONFormatter,
    ColoredFormatter,
    setup_logging,
    get_logger,
    log_dict,
)


class TestJSONFormatter:
    def test_format_basic(self):
        formatter = JSONFormatter()
        record = logging.LogRecord(
            name="test", level=logging.INFO, pathname="test.py",
            lineno=1, msg="hello", args=(), exc_info=None,
            funcName="test_func",
        )
        result = formatter.format(record)
        data = json.loads(result)
        assert data["level"] == "INFO"
        assert data["message"] == "hello"
        assert data["logger"] == "test"
        assert data["file"] == "test.py"
        assert data["line"] == 1

    def test_format_with_exception(self):
        formatter = JSONFormatter()
        try:
            raise ValueError("boom")
        except ValueError:
            import sys
            exc_info = sys.exc_info()
        record = logging.LogRecord(
            name="test", level=logging.ERROR, pathname="test.py",
            lineno=1, msg="error", args=(), exc_info=exc_info,
        )
        result = formatter.format(record)
        data = json.loads(result)
        assert "exception" in data


class TestColoredFormatter:
    def test_format_info(self):
        formatter = ColoredFormatter(fmt="%(levelname)s %(message)s")
        record = logging.LogRecord(
            name="test", level=logging.INFO, pathname="test.py",
            lineno=1, msg="hello", args=(), exc_info=None,
        )
        result = formatter.format(record)
        assert "\033[32m" in result
        assert "INFO" in result
        assert "hello" in result
        assert "\033[0m" in result

    def test_format_error(self):
        formatter = ColoredFormatter(fmt="%(levelname)s %(message)s")
        record = logging.LogRecord(
            name="test", level=logging.ERROR, pathname="test.py",
            lineno=1, msg="fail", args=(), exc_info=None,
        )
        result = formatter.format(record)
        assert "\033[31m" in result

    def test_format_unknown_level(self):
        formatter = ColoredFormatter(fmt="%(levelname)s %(message)s")
        record = logging.LogRecord(
            name="test", level=logging.WARNING, pathname="test.py",
            lineno=1, msg="warn", args=(), exc_info=None,
        )
        result = formatter.format(record)
        assert "WARNING" in result


class TestSetupLogging:
    def test_verbose_quiet_conflict(self):
        config = OutputConfig(verbose=True, quiet=True)
        with pytest.raises(ValueError, match="verbose and quiet"):
            setup_logging(config)

    def test_quiet_mode(self):
        config = OutputConfig(quiet=True)
        setup_logging(config)
        root = logging.getLogger()
        assert root.level == logging.ERROR

    def test_verbose_mode(self):
        config = OutputConfig(verbose=True)
        setup_logging(config)
        root = logging.getLogger()
        assert root.level == logging.DEBUG

    def test_default_mode(self):
        config = OutputConfig()
        setup_logging(config)
        root = logging.getLogger()
        assert root.level == logging.INFO

    def test_json_format(self):
        config = OutputConfig(format="json")
        setup_logging(config)
        logger = get_logger("test")
        handler = logger.handlers[0] if logger.handlers else logging.getLogger().handlers[-1]
        assert isinstance(handler.formatter, JSONFormatter)

    def test_color_format_tty(self, monkeypatch):
        import sys
        monkeypatch.setattr(sys.stderr, "isatty", lambda: True)
        config = OutputConfig(color_output=True)
        setup_logging(config)
        handler = logging.getLogger().handlers[-1]
        assert isinstance(handler.formatter, ColoredFormatter)

    def test_plain_format(self):
        config = OutputConfig(color_output=False)
        setup_logging(config)
        handler = logging.getLogger().handlers[-1]
        assert isinstance(handler.formatter, logging.Formatter)
        assert not isinstance(handler.formatter, (JSONFormatter, ColoredFormatter))


class TestGetLogger:
    def test_returns_logger(self):
        logger = get_logger("test_logger")
        assert isinstance(logger, logging.Logger)
        assert logger.name == "test_logger"


class TestLogDict:
    def test_log_dict_info(self, caplog):
        logger = get_logger("test")
        with caplog.at_level(logging.INFO):
            log_dict(logger, "info", {"key": "value"})
        assert any("key" in r.message for r in caplog.records)

    def test_log_dict_error(self, caplog):
        logger = get_logger("test")
        with caplog.at_level(logging.ERROR):
            log_dict(logger, "error", {"error": "bad"})

    def test_log_dict_invalid_level(self):
        logger = get_logger("test")
        with pytest.raises(ValueError, match="Invalid log level"):
            log_dict(logger, "invalid", {"key": "val"})
