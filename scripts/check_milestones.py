#!/usr/bin/env python3
"""Validate the curated milestone catalog and optionally audit its Lean witnesses.

The default command is source-only. --audit requires an up-to-date Lake build;
CI runs it after the ordinary full build. An axiom audit does not establish that
the English statement matches the theorem: that remains a review obligation.
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
NAME = re.compile(r"[A-Za-z_][A-Za-z_0-9']*(?:\.[A-Za-z_][A-Za-z_0-9']*)*")
STATUSES = {"proved", "conditional", "open", "refuted"}
STATUS_LABELS = {
    "proved": "Proved theorem",
    "conditional": "Conditional theorem — external inputs remain",
    "open": "Open target — not proved",
    "refuted": "Refuted formulation — counterexample proved",
}


def validate_catalog(data: dict, root: Path = ROOT) -> None:
    if not isinstance(data, dict):
        raise ValueError("catalog must be an object")
    if data.get("schema_version") != 1:
        raise ValueError("unsupported catalog schema_version")
    entries = data.get("milestones")
    if not isinstance(entries, list) or not entries:
        raise ValueError("milestones must be a nonempty list")
    ids: set[str] = set()
    for item in entries:
        if not isinstance(item, dict):
            raise ValueError("milestone entries must be objects")
        for field in ("id", "title", "summary", "scope", "status"):
            if not isinstance(item.get(field), str) or not item[field].strip():
                raise ValueError(f"missing nonempty {field}")
        ident = item["id"]
        if not re.fullmatch(r"[a-z][a-z0-9-]*", ident) or ident in ids:
            raise ValueError(f"invalid or duplicate id: {ident}")
        ids.add(ident)
        if item["status"] not in STATUSES:
            raise ValueError(f"invalid status: {ident}")
        if not isinstance(item.get("witnesses"), list):
            raise ValueError(f"missing witnesses list: {ident}")
        if not isinstance(item.get("issues"), list) or not all(
            isinstance(url, str) and re.fullmatch(
                r"https://github\.com/[\w-]+/[\w.-]+/issues/[1-9][0-9]*", url
            ) for url in item["issues"]
        ):
            raise ValueError(f"invalid issue links: {ident}")
        if item["status"] == "open":
            if item["witnesses"] or not item["issues"]:
                raise ValueError(f"open target needs an issue and no witness: {ident}")
        elif not item["witnesses"]:
            raise ValueError(f"non-open milestone needs a theorem witness: {ident}")
        seen: set[str] = set()
        for witness in item["witnesses"]:
            if not isinstance(witness, dict):
                raise ValueError(f"witness entries must be objects: {ident}")
            module, theorem = witness.get("module"), witness.get("declaration")
            if not isinstance(module, str) or not NAME.fullmatch(module):
                raise ValueError(f"invalid module: {ident}")
            if not module.startswith("RealRooted.Challenges."):
                raise ValueError(f"witness must use a challenge entry point: {ident}")
            if not isinstance(theorem, str) or not NAME.fullmatch(theorem):
                raise ValueError(f"invalid declaration: {ident}")
            # This bounds the catalog metadata to the named challenge facade.
            # It does not prove the declaration is physically defined in that
            # file; imported declarations remain a separate Lean-level concern.
            if not theorem.startswith(module + "."):
                raise ValueError(f"declaration must be in listed challenge module: {ident}")
            if theorem in seen:
                raise ValueError(f"duplicate witness: {ident}")
            seen.add(theorem)
            if not (root / (module.replace(".", "/") + ".lean")).is_file():
                raise ValueError(f"missing challenge module: {module}")


def witness_names(data: dict) -> list[str]:
    return sorted({w["declaration"] for m in data["milestones"] for w in m["witnesses"]})


def audit_source(data: dict) -> str:
    modules = sorted({w["module"] for m in data["milestones"] for w in m["witnesses"]})
    source = "import Lean\n" + "".join(f"import {m}\n" for m in modules) + "\n"
    for name in witness_names(data):
        # Reject a proposition definition or a source axiom masquerading as a
        # theorem witness, even if #print axioms alone would accept it.
        source += (
            "run_cmd do\n"
            f"  match (← Lean.getEnv).find? `{name} with\n"
            "  | some (.thmInfo _) => pure ()\n"
            f'  | _ => throwError "Not a theorem witness: {name}"\n'
            f"#print axioms {name}\n\n"
        )
    return source


def parse_axioms(output: str, expected: list[str]) -> dict[str, list[str]]:
    pattern = re.compile(
        # Lean wraps the rendered declaration name in apostrophes. Names may
        # themselves contain apostrophes, so terminate at the apostrophe before
        # the fixed ` depends`/` does` suffix rather than at the first one.
        r"'(?P<name>[^\n]+?)' (?:depends on axioms:\s*\[(?P<axioms>[^]]*)\]"
        r"|does not depend on any axioms)", re.MULTILINE
    )
    found: dict[str, list[str]] = {}
    for match in pattern.finditer(output):
        name = match["name"]
        if name not in expected:
            raise ValueError(f"unexpected axiom result: {name}")
        if name in found:
            raise ValueError(f"duplicate axiom result: {name}")
        axioms = sorted({a.strip() for a in (match["axioms"] or "").split(",") if a.strip()})
        if not set(axioms) <= ALLOWED_AXIOMS:
            raise ValueError(f"nonstandard axioms for {name}: {axioms}")
        found[name] = axioms
    missing = set(expected) - found.keys()
    if missing:
        raise ValueError(f"missing axiom results: {sorted(missing)}")
    return found


def markdown(data: dict) -> str:
    lines = [
        "# Formalization milestones", "",
        "A curated guide to major theorems, not a count of helper lemmas.", "",
        "**Reading the status:** “Proved” means the stated theorem has a Lean witness;",
        "its mathematical hypotheses still apply. “Conditional” means an explicit external",
        "model identity or other unformalized input remains. An open target has no witness.",
        "The scope notes are part of the claim, not fine print.", "",
        "This generated source catalog is not a live CI badge. The `milestone-audit` CI",
        "artifact records a transitive-axiom audit for one exact Git revision. Only a",
        "successful full build followed by that audit validates that revision. The separate",
        "Comparator workflow independently rechecks only its configured theorem list;",
        "catalog membership does not imply independent-comparator coverage.", "",
        "Source of truth: [milestones.json](milestones.json). Regenerate with",
        "`python3 scripts/check_milestones.py --write`.", "",
    ]
    for item in data["milestones"]:
        lines.extend([f"## {item['title']}", "", f"Status: {STATUS_LABELS[item['status']]}", "",
                      item["summary"], "", f"Scope: {item['scope']}", ""])
        for witness in item["witnesses"]:
            path = witness["module"].replace(".", "/") + ".lean"
            lines.append(f"- Lean theorem: [{witness['declaration']}]({path})")
        for issue in item["issues"]:
            lines.append(f"- [Tracking issue #{issue.rsplit('/', 1)[1]}]({issue})")
        lines.append("")
    return "\n".join(lines)


def run_audit(data: dict, report_path: Path) -> None:
    # An isolated scratch file is generated, never added to the library or Git.
    with tempfile.TemporaryDirectory(prefix="realrooted-milestones-") as directory:
        source = Path(directory) / "Audit.lean"
        source.write_text(audit_source(data), encoding="utf-8")
        result = subprocess.run(
            ["lake", "env", "lean", str(source)], cwd=ROOT, text=True,
            stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=1200,
        )
    if result.returncode:
        raise ValueError(f"Lean axiom audit failed (exit {result.returncode}):\n{result.stdout}")
    axioms = parse_axioms(result.stdout, witness_names(data))
    revision = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip()
    report = {
        "schema_version": 1, "revision": revision,
        "verification": "lean-transitive-axiom-audit",
        "permitted_axioms": sorted(ALLOWED_AXIOMS), "axioms": axioms,
        "independent_comparator_coverage": "See comparator/config.json; not inferred here.",
        "milestones": data["milestones"],
    }
    report_path.parent.mkdir(parents=True, exist_ok=True)
    report_path.write_text(json.dumps(report, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    print(f"Audited {len(axioms)} witnesses at {revision}; report: {report_path}")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write", action="store_true", help="regenerate MILESTONES.md")
    parser.add_argument("--audit", action="store_true", help="run Lean after a fresh full build")
    parser.add_argument("--report", type=Path, default=Path("milestone-audit.json"))
    args = parser.parse_args()
    try:
        data = json.loads((ROOT / "milestones.json").read_text(encoding="utf-8"))
        validate_catalog(data)
        expected = markdown(data)
        document = ROOT / "MILESTONES.md"
        if args.write:
            document.write_text(expected, encoding="utf-8")
        elif not document.is_file() or document.read_text(encoding="utf-8") != expected:
            raise ValueError("MILESTONES.md is stale; run scripts/check_milestones.py --write")
        if args.audit:
            run_audit(data, args.report)
        print(f"Milestone source checks passed ({len(data['milestones'])} entries).")
        return 0
    except (ValueError, OSError, subprocess.SubprocessError) as error:
        print(f"Milestone check failed: {error}")
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
