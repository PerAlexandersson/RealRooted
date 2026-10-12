#!/usr/bin/env python3
"""Backfill catalog ``formalized`` dates from the history of selected results.

Run this from a checkout containing the challenge sources, pointing
``--history-repo`` at a clone whose ``origin/main`` has the relevant history.
The output is a tab-separated ``slug, date, method`` report suitable for
reviewing the backfill.  ``--dry-run`` never changes a source file.
"""

from __future__ import annotations

import argparse
import pathlib
import re
import subprocess
import sys
import tomllib


METADATA_RE = re.compile(r"<!--\s*realrooted-catalog\s*\n(.*?)-->", re.DOTALL)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--repo-root",
        type=pathlib.Path,
        default=pathlib.Path(__file__).resolve().parents[1],
        help="checkout whose challenge metadata will be updated",
    )
    parser.add_argument(
        "--history-repo",
        type=pathlib.Path,
        default=pathlib.Path(__file__).resolve().parents[1],
        help="checkout with the origin/main history to search",
    )
    parser.add_argument("--dry-run", action="store_true", help="report dates without writing files")
    return parser.parse_args()


def git_dates(history_repo: pathlib.Path, *args: str) -> list[str]:
    result = subprocess.run(
        ["git", "-C", str(history_repo), *args],
        capture_output=True,
        check=True,
        text=True,
    )
    return [line for line in result.stdout.splitlines() if re.fullmatch(r"\d{4}-\d{2}-\d{2}", line)]


def formalized_date(
    history_repo: pathlib.Path, source_path: str, theorem_name: str
) -> tuple[str, str]:
    """Find the first pickaxe hit, or the challenge module's first addition."""
    short_name = theorem_name.rsplit(".", 1)[-1]
    for kind in ("theorem", "lemma"):
        dates = git_dates(
            history_repo,
            "log",
            "origin/main",
            "--reverse",
            "--format=%cs",
            f"-S{kind} {short_name}",
            "--",
            "RealRooted",
        )
        if dates:
            return dates[0], "pickaxe"
    dates = git_dates(
        history_repo,
        "log",
        "origin/main",
        "--diff-filter=A",
        "--format=%cs",
        "--",
        source_path,
    )
    if dates:
        return dates[-1], "page-add"
    raise ValueError(
        f"{source_path}: no pickaxe hit for {theorem_name} and no file-addition commit on origin/main"
    )


def selected_theorem(metadata: dict[object, object], source_path: str) -> str:
    theorems = metadata.get("theorems")
    if not isinstance(theorems, list) or not theorems:
        raise ValueError(f"{source_path}: catalog page has no theorem to date")
    selected = next(
        (record for record in theorems if isinstance(record, dict) and record.get("headline") is True),
        theorems[0],
    )
    if not isinstance(selected, dict) or not isinstance(selected.get("name"), str):
        raise ValueError(f"{source_path}: selected theorem has no name")
    return selected["name"]


def replace_metadata_date(text: str, match: re.Match[str], formalized: str) -> str:
    metadata = match.group(1)
    if re.search(r"(?m)^formalized\s*=", metadata):
        replacement = re.sub(
            r'(?m)^formalized\s*=\s*"[^"]*"\s*$', f'formalized = "{formalized}"', metadata
        )
    else:
        replacement, count = re.subn(
            r"(?m)^(slug\s*=.*)$", rf'\1\nformalized = "{formalized}"', metadata, count=1
        )
        if count != 1:
            raise ValueError("metadata has no slug line")
    return text[: match.start(1)] + replacement + text[match.end(1) :]


def main() -> int:
    args = parse_args()
    root = args.repo_root.resolve()
    history_repo = args.history_repo.resolve()
    rows: list[tuple[str, str, str]] = []
    try:
        for path in sorted((root / "RealRooted" / "Challenges").rglob("*.lean")):
            text = path.read_text(encoding="utf-8")
            match = METADATA_RE.search(text)
            if match is None:
                continue
            metadata = tomllib.loads(match.group(1))
            if not isinstance(metadata, dict):
                raise ValueError(f"{path.relative_to(root)}: metadata is not a table")
            source_path = path.relative_to(root).as_posix()
            slug = metadata.get("slug")
            if not isinstance(slug, str):
                raise ValueError(f"{source_path}: metadata has no slug")
            formalized, method = formalized_date(
                history_repo, source_path, selected_theorem(metadata, source_path)
            )
            rows.append((slug, formalized, method))
            if not args.dry_run:
                path.write_text(replace_metadata_date(text, match, formalized), encoding="utf-8")
    except (OSError, subprocess.CalledProcessError, tomllib.TOMLDecodeError, ValueError) as error:
        print(f"error: {error}", file=sys.stderr)
        return 1
    print("slug\tformalized\tmethod")
    print("\n".join("\t".join(row) for row in rows))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
