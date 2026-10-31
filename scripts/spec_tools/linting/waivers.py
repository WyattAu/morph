"""
Intentional-deviation waivers for the specification linter.

Some specification files legitimately deviate from
``docs/conventions/specification_convention.md``: glossaries have no
Requirements section, umbrella specs span several topics, reference
grammars state no requirements. Rewriting those files to satisfy a
heading-name check would damage them; fabricating the missing sections
would be worse. Waivers record such deviations explicitly, with a
reason, in ``spec-lint-waivers.toml`` at the repository root:

```toml
[[waiver]]
path = "spec/GLOSSARY.md"
rule = "section-structure"
reason = "Glossary document class: defines terms corpus-wide."
```

A waiver applies to every error of the named rule in the named file.
Waived errors are reported (never silently dropped): the CLI summary
prints how many errors were waived and where the waivers live.
"""

from pathlib import Path
from typing import List, Optional

import tomllib


def find_waivers_file(start: Path) -> Optional[Path]:
    """Walk up from ``start`` looking for ``spec-lint-waivers.toml``.

    Args:
        start: File or directory to start the upward search from.

    Returns:
        Path to the waivers file, or ``None`` when there is none.
    """
    current = start.resolve()
    if current.is_file():
        current = current.parent
    for candidate in [current, *current.parents]:
        waivers_file = candidate / "spec-lint-waivers.toml"
        if waivers_file.is_file():
            return waivers_file
    return None


def load_waivers(start: Path) -> List[dict]:
    """Load waivers applicable under ``start``.

    Args:
        start: File or directory the lint run covers.

    Returns:
        List of ``{\"path\", \"rule\", \"reason\"}`` dicts (possibly empty).
        A malformed waivers file yields no waivers rather than failing
        the lint run.
    """
    waivers_file = find_waivers_file(start)
    if waivers_file is None:
        return []
    try:
        with waivers_file.open("rb") as handle:
            data = tomllib.load(handle)
    except (OSError, tomllib.TOMLDecodeError):
        return []
    waivers = []
    entries = data.get("waiver", [])
    if isinstance(entries, dict):
        entries = [entries]
    for entry in entries:
        if not isinstance(entry, dict):
            continue
        if isinstance(entry.get("path"), str) and isinstance(entry.get("rule"), str):
            waivers.append(
                {
                    "path": entry["path"],
                    "rule": entry["rule"],
                    "reason": str(entry.get("reason", "")),
                }
            )
    return waivers


def waived_reason(waivers: List[dict], filepath: Path, rule_id: str) -> Optional[str]:
    """Return the waiver reason when an error is waived, else ``None``.

    Matching is by path suffix so waivers stay valid regardless of the
    absolute checkout location.

    Args:
        waivers: Loaded waiver entries.
        filepath: Path of the file the error was reported in.
        rule_id: Rule ID of the reported error.

    Returns:
        The waiver reason, or ``None`` when no waiver applies.
    """
    text = filepath.as_posix()
    for waiver in waivers:
        if waiver["rule"] == rule_id and text.endswith(waiver["path"]):
            return waiver["reason"]
    return None
