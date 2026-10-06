#!/usr/bin/env python3
"""Rank modules by build time in a GitHub Actions build log.

Reads the `✔ [i/N] Built Module (12s)` lines that Lake prints.  Only modules
that were actually compiled appear, so use the log of a run that rebuilt the
project (one where the build job took most of an hour rather than minutes).

Usage:

    scripts/ci_module_times.py --run 37455387501          # fetch with `gh`
    scripts/ci_module_times.py --log build.log --prefix RealRooted.Tactic
    scripts/ci_module_times.py --run 37455387501 --group 2

`--group k` sums the times by the first `k` components after `RealRooted`.
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from collections import defaultdict
from pathlib import Path

BUILT_RE = re.compile(r"Built (\S+) \(([0-9.]+)(ms|s)\)")


def fetch_log(run: str, job_name: str) -> str:
    jobs = json.loads(subprocess.check_output(
        ["gh", "run", "view", run, "--json", "jobs"], text=True))["jobs"]
    job = next((j for j in jobs if j["name"] == job_name), None)
    if job is None:
        sys.exit(f"run {run} has no job named {job_name!r}")
    return subprocess.check_output(
        ["gh", "api", f"repos/{{owner}}/{{repo}}/actions/jobs/{job['databaseId']}/logs"],
        text=True)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    source = parser.add_mutually_exclusive_group(required=True)
    source.add_argument("--run", help="GitHub Actions run id")
    source.add_argument("--log", type=Path, help="saved job log")
    parser.add_argument("--job", default="build", help="job name (default: build)")
    parser.add_argument("--prefix", default="RealRooted", help="module prefix filter")
    parser.add_argument("--group", type=int, help="sum by this many name components")
    parser.add_argument("--top", type=int, default=30, help="rows to print")
    args = parser.parse_args()

    text = args.log.read_text(encoding="utf-8") if args.log else fetch_log(args.run, args.job)
    times: dict[str, float] = {}
    for module, value, unit in BUILT_RE.findall(text):
        if module.startswith(args.prefix):
            times[module] = float(value) / (1000 if unit == "ms" else 1)
    if not times:
        sys.exit("no `Built` lines matched; was anything compiled in this run?")

    rows: dict[str, float] = times
    counts: dict[str, int] = defaultdict(lambda: 1)
    if args.group:
        rows, counts = defaultdict(float), defaultdict(int)
        for module, t in times.items():
            key = ".".join(module.split(".")[: 1 + args.group])
            rows[key] += t
            counts[key] += 1

    print(f"{sum(times.values()):>9.0f}s  TOTAL ({len(times)} modules)")
    for key, t in sorted(rows.items(), key=lambda kv: -kv[1])[: args.top]:
        suffix = f"  ({counts[key]} modules)" if args.group else ""
        print(f"{t:>9.1f}s  {key}{suffix}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
