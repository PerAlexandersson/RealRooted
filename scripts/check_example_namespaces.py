#!/usr/bin/env python3
"""Check that regression examples declare nothing public in the root namespace.

Files under `RealRooted/Tactic/Examples` copy downstream statements literally, including
definitions such as `def A199221`.  A public root-level copy collides with the downstream
definition as soon as one environment imports both (for example a downstream umbrella that
imports `RealRooted` and its own `A199221` module).  Such declarations must live in a
namespace (the convention is `namespace A199221Downstream`) or be `private`.

Exit codes: 0 if no file has a public root-level declaration, 1 otherwise.
"""

from __future__ import annotations

import argparse
import pathlib
import re
import sys

EXAMPLES = "RealRooted/Tactic/Examples"
DECL_RE = re.compile(
    r"^(?:@\[[^\]]*\]\s*)?(?P<private>private\s+)?(?:protected\s+)?(?:noncomputable\s+)?"
    r"(?:def|abbrev|theorem|lemma|structure|inductive|class|opaque)\s+(?P<name>[^\s:(]+)"
)
NAMESPACE_RE = re.compile(r"^namespace\s+(\S+)")
SECTION_RE = re.compile(r"^(?:noncomputable\s+)?section(?:\s+(\S+))?\s*$")
END_RE = re.compile(r"^end(?:\s+(\S+))?\s*$")


def root_declarations(text: str) -> list[tuple[int, str]]:
    """Return `(line, name)` for public declarations outside every namespace."""
    scopes: list[tuple[str, str]] = []
    found = []
    for lineno, line in enumerate(text.splitlines(), 1):
        if m := NAMESPACE_RE.match(line):
            scopes.append(("namespace", m.group(1)))
        elif m := SECTION_RE.match(line):
            scopes.append(("section", m.group(1) or ""))
        elif m := END_RE.match(line):
            name = m.group(1) or ""
            for i in range(len(scopes) - 1, -1, -1):
                if scopes[i][1] == name:
                    del scopes[i:]
                    break
        elif m := DECL_RE.match(line):
            in_namespace = any(kind == "namespace" for kind, _ in scopes)
            if not in_namespace and not m.group("private"):
                found.append((lineno, m.group("name")))
    return found


def self_test() -> int:
    bad = "noncomputable section\n\ndef A199221 : Nat := 1\n\nend\n"
    good = (
        "namespace A199221Downstream\n\nnoncomputable section\n\ndef A199221 : Nat := 1\n\n"
        "end\n\nend A199221Downstream\n\nprivate def helper : Nat := 2\n"
    )
    assert root_declarations(bad) == [(3, "A199221")], root_declarations(bad)
    assert root_declarations(good) == [], root_declarations(good)
    print("ok: self-test passed")
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--repo-root", default=".", type=pathlib.Path)
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args()
    if args.self_test:
        return self_test()
    root = args.repo_root / EXAMPLES
    errors = []
    for path in sorted(root.rglob("*.lean")):
        for lineno, name in root_declarations(path.read_text(encoding="utf-8")):
            rel = path.relative_to(args.repo_root)
            errors.append(f"{rel}:{lineno}: public root-level declaration `{name}`")
    if errors:
        print("\n".join(errors))
        print("error: put regression-example declarations in a namespace "
              "(e.g. `namespace A199221Downstream`) or make them private", file=sys.stderr)
        return 1
    print(f"ok: no public root-level declarations under {EXAMPLES}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
