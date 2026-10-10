#!/usr/bin/env python3
"""Generate a searchable index of the public theorems of RealRooted.

Writes two files:

* ``docs/LEMMA_INDEX.tsv`` (gitignored, regenerate on demand): one line per public ``theorem``/``lemma`` with its qualified name,
  module, conclusion key, number of using files, first docstring sentence and statement
  (flattened to one line, truncated).  Meant for ``grep``: by name, by conclusion key, or by
  any word of the statement.
* ``docs/WORKHORSES.md`` (a committed snapshot): for each conclusion key, the most used
  theorems.

The index is parsed from source (no Lean build is needed), so statements are shown as written.
Usage counts are the number of other ``.lean`` files that mention the theorem's last name
component, or its qualified name when the last component is too generic.

    python3 scripts/lemma_index.py          # regenerate
    python3 scripts/lemma_index.py --check  # fail if the files are stale
"""

from __future__ import annotations

import argparse
import re
import subprocess
import sys
from collections import defaultdict
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
TSV = ROOT / "docs" / "LEMMA_INDEX.tsv"
MD = ROOT / "docs" / "WORKHORSES.md"
STATEMENT_WIDTH = 220
TOP_PER_KEY = 25

DECL = re.compile(r"^(?:@\[[^\]]*\]\s*)?(protected |private |noncomputable )*(theorem|lemma)\s+(\S+)")
IDENT = re.compile(r"[A-Za-z_][A-Za-z0-9_'.!?₀-₉ᵢ]*")

# Conclusion keys, tried in order on the conclusion (the type after the last top-level `:`).
KEYS = [
    ("StrictInterl", r"\bStrictInterl\b"),
    ("Interlaces", r"\bInterlaces\b|\bInterl\b"),
    ("IsInterlacingSeq", r"\bIsInterlacingSeq"),
    ("HasCommonInterleaver", r"\bHasCommon\w*Interleaver\b|\bCompatible\b"),
    ("IsPolyaFreqSeq", r"\bIsPolyaFreqSeq\b|\bIsPFPolynomial\b|\bTotallyNonneg\b"),
    ("Stable", r"\bStable\b|\bIsStable\b|\bMvRealStable\b|\bHurwitz"),
    ("IsNegativeSimple", r"\bIsNegativeSimple\b|\bSimpleNegRooted\b"),
    ("Splits", r"\.Splits\b|\bSplits\b"),
    ("roots", r"\.roots\b|\bIsRoot\b|\brootCount|\broots\b"),
    ("HasNonnegCoeffs", r"\bHasNonnegCoeffs\b|\bHasPosLeadingCoeff\b"),
    ("natDegree", r"\bnatDegree\b|\bdegree\b"),
    ("leadingCoeff", r"\bleadingCoeff\b"),
    ("coeff", r"\.coeff\b|\bcoeff\b"),
    ("eval", r"\.eval\b|\beval\b|\bsign\b"),
    ("recurrence", r"=\s*\w+\s*\*\s*\(?\w+\s*\(n"),
    ("polynomial identity", r"\bderivative\b|ℝ\[X\]"),
    ("nonvanishing", r"≠"),
    ("inequality", r"≤|<|≥|>"),
    ("equation", r"="),
]


def git_files() -> list[Path]:
    out = subprocess.run(["git", "ls-files", "RealRooted/*.lean", "RealRooted/**/*.lean"],
                         cwd=ROOT, capture_output=True, text=True, check=True).stdout
    return [ROOT / p for p in out.split() if p]


def module_of(path: Path) -> str:
    return str(path.relative_to(ROOT).with_suffix("")).replace("/", ".")


def strip_comments(text: str) -> str:
    """Remove `--` line comments and nested `/- -/` block comments (keeps line structure)."""
    out, i, depth = [], 0, 0
    while i < len(text):
        if text.startswith("/-", i):
            depth += 1
            i += 2
            continue
        if depth and text.startswith("-/", i):
            depth -= 1
            i += 2
            continue
        if depth:
            out.append("\n" if text[i] == "\n" else " ")
            i += 1
            continue
        if text.startswith("--", i):
            j = text.find("\n", i)
            i = len(text) if j < 0 else j
            continue
        out.append(text[i])
        i += 1
    return "".join(out)


def statement_of(lines: list[str], start: int) -> str:
    """The declaration from `start` up to its `:=` (or `|` for equation-style proofs)."""
    buf = []
    for line in lines[start:start + 40]:
        cut = None
        for tok in (":= by", ":=", " where"):
            k = line.find(tok)
            if k >= 0 and (cut is None or k < cut):
                cut = k
        if cut is not None:
            buf.append(line[:cut])
            break
        if buf and line.startswith("  | "):
            break
        buf.append(line)
    return re.sub(r"\s+", " ", " ".join(buf)).strip()


def conclusion_of(stmt: str) -> str:
    """The text after the last top-level `:` of the signature."""
    depth, last = 0, -1
    for i, ch in enumerate(stmt):
        if ch in "([{⟨":
            depth += 1
        elif ch in ")]}⟩":
            depth -= 1
        elif ch == ":" and depth == 0 and stmt[i:i + 2] != ":=":
            last = i
    return stmt[last + 1:] if last >= 0 else stmt


def key_of(conclusion: str) -> str:
    # the final conjunct/consequent carries the conclusion of an implication chain
    tail = re.split(r"→|↔|∧", conclusion)[-1]
    for name, pat in KEYS:
        if re.search(pat, tail):
            return name
    for name, pat in KEYS:
        if re.search(pat, conclusion):
            return name
    return "other"


def doc_before(raw_lines: list[str], start: int) -> str:
    """First sentence of the docstring ending just above line `start`."""
    j = start - 1
    while j >= 0 and raw_lines[j].strip().startswith("@["):
        j -= 1
    if j < 0 or not raw_lines[j].rstrip().endswith("-/"):
        return ""
    end = j
    while j >= 0 and "/--" not in raw_lines[j]:
        j -= 1
    if j < 0:
        return ""
    text = " ".join(raw_lines[j:end + 1])
    text = text[text.find("/--") + 3:]
    text = text.replace("-/", "")
    text = re.sub(r"\s+", " ", text).strip()
    m = re.match(r"(.+?[.!?])(\s|$)", text)
    sentence = m.group(1) if m else text
    return sentence[:200]


def collect():
    files = git_files()
    decls = []
    words_per_file: dict[Path, set[str]] = {}
    for path in files:
        raw = path.read_text(encoding="utf-8")
        text = strip_comments(raw)
        words_per_file[path] = set(IDENT.findall(text))
        raw_lines = raw.split("\n")
        lines = text.split("\n")
        ns: list[str] = []
        for i, line in enumerate(lines):
            s = line.strip()
            m = re.match(r"^namespace\s+(\S+)", line)
            if m:
                ns.append(m.group(1))
                continue
            m = re.match(r"^end\s+(\S+)\s*$", line)
            if m and ns and ns[-1] == m.group(1):
                ns.pop()
                continue
            m = DECL.match(line)
            if not m or (m.group(1) and "private" in m.group(1)):
                continue
            if "private " in line.split(m.group(2))[0]:
                continue
            short = m.group(3)
            full = short if short.startswith("_root_.") else ".".join(ns + [short])
            full = full.replace("_root_.", "")
            stmt = statement_of(lines, i)
            decls.append({
                "name": full, "short": short.split(".")[-1], "path": path,
                "module": module_of(path), "stmt": stmt,
                "key": key_of(conclusion_of(stmt)), "doc": doc_before(raw_lines, i),
            })
    # usage counts: other files mentioning the name
    by_word: dict[str, set[Path]] = defaultdict(set)
    for path, words in words_per_file.items():
        for w in words:
            by_word[w].add(path)
            if "." in w:
                by_word[w.split(".")[-1]].add(path)
    # a short name counts only when it is distinctive; otherwise the last two components do
    short_count: dict[str, int] = defaultdict(int)
    for d in decls:
        short_count[d["short"]] += 1
    for d in decls:
        parts = d["name"].split(".")
        if short_count[d["short"]] == 1 and len(d["short"]) >= 8:
            users = by_word.get(d["short"], set()) | by_word.get(d["name"], set())
        else:
            tail = ".".join(parts[-2:])
            users = {p for p in by_word.get(d["short"], set())
                     if any(w.endswith(tail) for w in words_per_file[p] if "." in w)}
            users |= by_word.get(d["name"], set())
        d["uses"] = len(users - {d["path"]})
    decls.sort(key=lambda d: d["name"])
    return decls


def render(decls) -> tuple[str, str]:
    rows = ["name\tmodule\tkey\tuses\tdoc\tstatement"]
    for d in decls:
        stmt = d["stmt"]
        if len(stmt) > STATEMENT_WIDTH:
            stmt = stmt[:STATEMENT_WIDTH - 1] + "…"
        doc = d["doc"].replace("\t", " ")
        rows.append(f"{d['name']}\t{d['module']}\t{d['key']}\t{d['uses']}\t{doc}\t{stmt}")
    tsv = "\n".join(rows) + "\n"

    by_key: dict[str, list] = defaultdict(list)
    for d in decls:
        by_key[d["key"]].append(d)
    md = ["# Workhorse lemmas", "",
          "A snapshot generated by `python3 scripts/lemma_index.py`; do not edit by hand.  For "
          "each conclusion key, the public theorems used by the most other files.  The same "
          "command writes the full index `docs/LEMMA_INDEX.tsv` (not committed: one line per "
          "public theorem with module, key, usage count, docstring and statement); search it "
          "with `grep`, for example",
          "", "```bash",
          "grep -P '\\tInterlaces\\t' docs/LEMMA_INDEX.tsv | sort -t$'\\t' -k4 -nr | head",
          "grep -i 'derivRec.*interlaces' docs/LEMMA_INDEX.tsv | cut -f1,6",
          "```", "",
          "For goals about rows of a recurrence, try the row tactics first (`rr_row_interlaces`, "
          "`rr_row_splits`, `rr_row_natDegree` and their `?` variants, see "
          "`RealRooted/Tactic/RowInterlacing.lean`).", ""]
    order = [k for k, _ in KEYS] + ["other"]
    for key in order:
        items = sorted(by_key.get(key, []), key=lambda d: (-d["uses"], d["name"]))
        items = [d for d in items if d["uses"] > 0][:TOP_PER_KEY]
        if not items:
            continue
        md += [f"## {key}", "", "| uses | theorem | module | doc |", "|---:|---|---|---|"]
        for d in items:
            doc = d["doc"].replace("|", "\\|")
            md.append(f"| {d['uses']} | `{d['name']}` | `{d['module']}` | {doc} |")
        md.append("")
    return tsv, "\n".join(md)


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--check", action="store_true", help="fail if the generated files are stale")
    args = ap.parse_args()
    tsv, md = render(collect())
    if args.check:
        stale = [p for p, c in ((TSV, tsv), (MD, md))
                 if not p.exists() or p.read_text(encoding="utf-8") != c]
        for p in stale:
            print(f"{p.relative_to(ROOT)} is stale; run python3 scripts/lemma_index.py")
        return 1 if stale else 0
    TSV.parent.mkdir(exist_ok=True)
    TSV.write_text(tsv, encoding="utf-8")
    MD.write_text(md, encoding="utf-8")
    print(f"wrote {TSV.relative_to(ROOT)} ({tsv.count(chr(10)) - 1} theorems) and "
          f"{MD.relative_to(ROOT)}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
