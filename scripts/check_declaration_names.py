#!/usr/bin/env python3
"""Ratchet naming findings for declarations published in the catalog."""
import argparse
from collections import Counter
from pathlib import Path
import re
import sys
import unittest

sys.dont_write_bytecode = True
from challenge_catalog import CatalogItem, load_catalog

ROOT = Path(__file__).resolve().parents[1]
BASELINE = ROOT / "scripts/declaration_names_baseline.txt"
RULES = ("oeis", "length", "workflow", "preserves", "challenges", "family")


def findings(pages, family=False):
    result = set()
    for page in pages:
        for item in page.items:
            name = item.name
            leaf = name.rsplit(".", 1)[-1]
            rules = []
            if re.search(r"A\d{6}", name): rules.append("oeis")
            if len(leaf) > 60: rules.append("length")
            if re.search(r"Internal|Backend|Legacy|Hyp|Bridge|Statement|_aux|_core|auxiliary", name, re.I): rules.append("workflow")
            if "preserves" in name.lower(): rules.append("preserves")
            if item.expected_kind == "theorem" and name.startswith("RealRooted.Challenges."): rules.append("challenges")
            if family and page.section == "families" and item.headline:
                # Provisional convention: a namespace segment equals the normalized slug.
                normalized = lambda x: re.sub(r"[^a-z0-9]", "", x.lower())
                if normalized(page.slug) not in [normalized(x) for x in name.split(".")[:-1]]:
                    rules.append("family")
            result.update(f"{rule}\t{name}" for rule in rules)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--update", action="store_true")
    parser.add_argument("--family", action="store_true", help="enable provisional slug-based family namespace rule")
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args()
    if args.self_test:
        class Tests(unittest.TestCase):
            def test_rules(self):
                from types import SimpleNamespace
                item = CatalogItem("RealRooted.Challenges.A123456.Backend_preserves_" + "x" * 61, "theorem", None, headline=True)
                page = SimpleNamespace(items=[item], section="families", slug="sample")
                self.assertEqual({x.split("\t")[0] for x in findings([page], True)}, set(RULES))
                self.assertFalse(findings([SimpleNamespace(items=[CatalogItem("RealRooted.Foo.good", "theorem", None)], section="theorems", slug="foo")]))
        suite = unittest.defaultTestLoader.loadTestsFromTestCase(Tests)
        return 0 if unittest.TextTestRunner().run(suite).wasSuccessful() else 1
    current = findings(load_catalog(ROOT), args.family)
    # Family findings are evaluated separately until the scheme is adopted.
    baseline = set(BASELINE.read_text().splitlines()) if BASELINE.exists() else set()
    if not args.family:
        baseline = {x for x in baseline if not x.startswith("family\t")}
    if args.update:
        if not args.family and BASELINE.exists():
            current |= {x for x in BASELINE.read_text().splitlines() if x.startswith("family\t")}
        BASELINE.write_text("".join(x + "\n" for x in sorted(current)))
        baseline = current
    counts = Counter(x.split("\t")[0] for x in current)
    print("Rule          Findings")
    for rule in RULES:
        print(f"{rule:12} {counts[rule]:8}" + (" (disabled)" if rule == "family" and not args.family else ""))
    for label, entries in (("new", current - baseline), ("stale", baseline - current)):
        for entry in sorted(entries): print(f"{label}: {entry}")
    return int(current != baseline)


if __name__ == "__main__":
    raise SystemExit(main())
