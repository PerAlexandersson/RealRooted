"""Parser for Lean's single-line import directives.

This intentionally does not parse Lean comments or multiline syntax.  It only
recognizes one complete import directive per physical line, optionally
preceded by ``public`` or ``private``.
"""

from __future__ import annotations

import re
from dataclasses import dataclass, field


IMPORT_RE = re.compile(
    r"(?P<indent>[ \t]*)(?:(?P<qualifier>public|private)[ \t]+)?import[ \t]+"
    r"(?P<module>[A-Za-z0-9_.']+)[ \t]*"
)


@dataclass(frozen=True)
class ImportDirective:
    qualifier: str | None
    module: str
    indentation: str = field(default="", compare=False)

    def format(self) -> str:
        prefix = f"{self.qualifier} " if self.qualifier else ""
        return f"{self.indentation}{prefix}import {self.module}"


def parse_import_line(line: str) -> ImportDirective | None:
    """Parse one physical line, returning ``None`` when it is not an import."""
    if "\n" in line or "\r" in line:
        return None
    match = IMPORT_RE.fullmatch(line)
    if match is None:
        return None
    return ImportDirective(
        match.group("qualifier"),
        match.group("module"),
        match.group("indent"),
    )


def parse_imports(lines: list[str]) -> list[ImportDirective]:
    """Parse all supported import directives in a sequence of lines."""
    return [directive for line in lines if (directive := parse_import_line(line))]
