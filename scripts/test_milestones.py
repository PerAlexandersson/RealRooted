#!/usr/bin/env python3
"""Source-only regression tests: no Lean or Lake is invoked."""

import copy
import unittest
from unittest.mock import patch

from check_milestones import audit_source, markdown, parse_axioms, validate_catalog


def fixture():
    return {"schema_version": 1, "milestones": [{
        "id": "example", "title": "Example", "summary": "An example theorem.",
        "scope": "Under explicit hypotheses.", "status": "proved", "issues": [],
        "witnesses": [{"module": "RealRooted.Challenges.Example", "declaration": "Foo.bar"}],
    }]}


class CatalogTests(unittest.TestCase):
    @patch("pathlib.Path.is_file", return_value=True)
    def test_valid_catalog(self, _):
        validate_catalog(fixture())

    @patch("pathlib.Path.is_file", return_value=True)
    def test_duplicate_ids(self, _):
        data = fixture()
        data["milestones"].append(copy.deepcopy(data["milestones"][0]))
        with self.assertRaisesRegex(ValueError, "duplicate id"):
            validate_catalog(data)

    def test_open_requires_issue_not_witness(self):
        data = fixture()
        data["milestones"][0]["status"] = "open"
        with self.assertRaisesRegex(ValueError, "open target"):
            validate_catalog(data)
        data["milestones"][0]["witnesses"] = []
        data["milestones"][0]["issues"] = ["https://github.com/a/b/issues/1"]
        validate_catalog(data)

    def test_proved_requires_witness(self):
        data = fixture()
        data["milestones"][0]["witnesses"] = []
        with self.assertRaisesRegex(ValueError, "theorem witness"):
            validate_catalog(data)

    def test_invalid_lean_name(self):
        data = fixture()
        data["milestones"][0]["witnesses"][0]["declaration"] = "Foo\naxiom bad : False"
        with self.assertRaisesRegex(ValueError, "invalid declaration"):
            validate_catalog(data)

    @patch("pathlib.Path.is_file", return_value=False)
    def test_missing_module(self, _):
        with self.assertRaisesRegex(ValueError, "missing challenge"):
            validate_catalog(fixture())

    def test_source_only_expected_commands(self):
        source = audit_source(fixture())
        self.assertIn("import RealRooted.Challenges.Example\n", source)
        self.assertIn("#print axioms Foo.bar\n", source)
        self.assertIn("some (.thmInfo _)", source)
        self.assertIn("Not a theorem witness: Foo.bar", source)

    def test_standard_and_empty_axioms(self):
        result = parse_axioms("'Foo.bar' depends on axioms: [propext,\nClassical.choice]\n"
                              "'Foo.empty' does not depend on any axioms\n", ["Foo.bar", "Foo.empty"])
        self.assertEqual(result["Foo.empty"], [])

    def test_missing_result(self):
        with self.assertRaisesRegex(ValueError, "missing axiom"):
            parse_axioms("", ["Foo.bar"])

    def test_nonstandard_axiom(self):
        for axiom in ("sorryAx", "customFact"):
            with self.assertRaisesRegex(ValueError, "nonstandard"):
                parse_axioms(f"'Foo.bar' depends on axioms: [{axiom}]", ["Foo.bar"])

    def test_duplicate_and_unexpected_results(self):
        line = "'Foo.bar' does not depend on any axioms\n"
        with self.assertRaisesRegex(ValueError, "duplicate"):
            parse_axioms(line * 2, ["Foo.bar"])
        with self.assertRaisesRegex(ValueError, "unexpected"):
            parse_axioms(line, ["Other.name"])

    def test_preview_labels_conditional_as_conditional(self):
        data = fixture()
        data["milestones"][0]["status"] = "conditional"
        self.assertIn("Conditional theorem — external inputs remain", markdown(data))
        self.assertIn("not a live CI badge", markdown(data))


if __name__ == "__main__":
    unittest.main()
