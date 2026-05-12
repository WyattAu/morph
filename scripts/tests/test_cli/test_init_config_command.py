"""Tests for CLI init-config command."""

from pathlib import Path
from types import SimpleNamespace
from unittest.mock import MagicMock, patch

import pytest

from spec_tools.cli.commands.init_config import (
    run_init_config_command,
    ConfigManager,
)
from spec_tools.models import Config


def _make_args(output="config.yaml", template="default"):
    return SimpleNamespace(output=output, template=template)


class TestRunInitConfigCommand:
    def test_creates_config_file(self, temp_dir):
        output_path = str(temp_dir / "config.yaml")
        args = _make_args(output=output_path)
        result = run_init_config_command(args)
        assert result == 0
        assert (temp_dir / "config.yaml").exists()

    def test_file_already_exists(self, temp_dir):
        config_file = temp_dir / "config.yaml"
        config_file.write_text("existing content")
        args = _make_args(output=str(config_file))
        result = run_init_config_command(args)
        assert result == 1

    def test_with_template(self, temp_dir):
        output_path = str(temp_dir / "custom.yaml")
        args = _make_args(output=output_path, template="strict")
        result = run_init_config_command(args)
        assert result == 0


class TestConfigManager:
    def test_save_config(self, temp_dir):
        manager = ConfigManager()
        config = Config()
        output_path = temp_dir / "config.yaml"
        manager.save_config(config, output_path)
        assert output_path.exists()
        content = output_path.read_text()
        assert "formatting:" in content
        assert "linting:" in content

    def test_load_config(self, temp_dir):
        import yaml
        config_file = temp_dir / "config.yaml"
        config_file.write_text("formatting:\n  max_line_length: 80\n")

        manager = ConfigManager()
        config = manager.load_config(config_file)
        assert config.formatting.max_line_length == 80

    def test_load_empty_config(self, temp_dir):
        config_file = temp_dir / "config.yaml"
        config_file.write_text("")

        manager = ConfigManager()
        config = manager.load_config(config_file)
        assert isinstance(config, Config)

    def test_load_yaml_error(self, temp_dir):
        config_file = temp_dir / "config.yaml"
        config_file.write_text("bad: [unclosed")

        manager = ConfigManager()
        with pytest.raises(Exception):
            manager.load_config(config_file)

    def test_save_config_structure(self, temp_dir):
        manager = ConfigManager()
        config = Config()
        config.formatting.max_line_length = 100
        config.linting.strict = True
        output_path = temp_dir / "config.yaml"
        manager.save_config(config, output_path)

        content = output_path.read_text()
        assert "Spec Tools Configuration" in content
        assert "max_line_length: 100" in content
        assert "strict: true" in content
