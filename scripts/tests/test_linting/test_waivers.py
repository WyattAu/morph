"""Tests for intentional-deviation waivers."""

from pathlib import Path

from spec_tools.linting.waivers import find_waivers_file, load_waivers, waived_reason


def _write(path: Path, text: str) -> Path:
    path.write_text(text, encoding="utf-8")
    return path


class TestFindWaiversFile:
    def test_finds_file_upward(self, temp_dir):
        _write(temp_dir / "spec-lint-waivers.toml", "")
        sub = temp_dir / "spec" / "language"
        sub.mkdir(parents=True)
        assert find_waivers_file(sub / "x.md") == temp_dir / "spec-lint-waivers.toml"

    def test_none_when_absent(self, temp_dir):
        assert find_waivers_file(temp_dir / "x.md") is None


class TestLoadWaivers:
    def test_loads_entries(self, temp_dir):
        _write(
            temp_dir / "spec-lint-waivers.toml",
            '[[waiver]]\npath = "spec/GLOSSARY.md"\nrule = "section-structure"\nreason = "Glossary class."\n',
        )
        waivers = load_waivers(temp_dir / "spec" / "GLOSSARY.md")
        assert len(waivers) == 1
        assert waivers[0]["path"] == "spec/GLOSSARY.md"
        assert waivers[0]["rule"] == "section-structure"

    def test_malformed_file_yields_no_waivers(self, temp_dir):
        _write(temp_dir / "spec-lint-waivers.toml", "[[waiver\nnot toml")
        assert load_waivers(temp_dir / "x.md") == []

    def test_skips_entries_missing_fields(self, temp_dir):
        _write(
            temp_dir / "spec-lint-waivers.toml",
            '[[waiver]]\npath = "spec/x.md"\n',
        )
        assert load_waivers(temp_dir / "x.md") == []


class TestWaivedReason:
    def test_match_by_suffix_and_rule(self, temp_dir):
        waivers = [{"path": "spec/GLOSSARY.md", "rule": "section-structure", "reason": "R"}]
        target = temp_dir / "spec" / "GLOSSARY.md"
        assert waived_reason(waivers, target, "section-structure") == "R"
        assert waived_reason(waivers, target, "math-notation") is None
        assert waived_reason(waivers, temp_dir / "spec" / "other.md", "section-structure") is None


class TestLinterAppliesWaivers:
    def test_waived_errors_filtered_and_counted(self, temp_dir):
        from spec_tools.linting.linter import SpecLinter
        from spec_tools.models import LintingConfig

        _write(
            temp_dir / "spec-lint-waivers.toml",
            '[[waiver]]\npath = "bad.md"\nrule = "math-notation"\nreason = "Intentional."\n',
        )
        target = _write(temp_dir / "bad.md", "Value $x is unmatched.\n")
        linter = SpecLinter(LintingConfig())
        assert linter.waived_count == 0
        result = linter.lint_file(target)
        assert [e for e in result.errors if e.rule_id == "math-notation"] == []
        assert linter.waived_count == 1

    def test_unwaived_errors_still_reported(self, temp_dir):
        from spec_tools.linting.linter import SpecLinter
        from spec_tools.models import LintingConfig

        _write(
            temp_dir / "spec-lint-waivers.toml",
            '[[waiver]]\npath = "other.md"\nrule = "math-notation"\nreason = "Elsewhere."\n',
        )
        (temp_dir / "spec").mkdir(exist_ok=True)
        target = _write(temp_dir / "spec" / "bad.md", "Value $x is unmatched.\n")
        linter = SpecLinter(LintingConfig())
        result = linter.lint_file(target)
        assert not result.passed
        assert linter.waived_count == 0
