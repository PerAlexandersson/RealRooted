#!/usr/bin/env python3
"""Ratchet for private imports (#2086).

Runs `lake shake` over every Lean module (after `lake build`) and collects the `public import`s
that shake would downgrade to a plain `import` because only proofs need them.  Shake's other
suggestions (unused or replaceable imports) are not checked.  Findings already recorded in
`scripts/private_imports_baseline.txt` are accepted; any new finding fails the check.

Shake cannot see names inside syntax quotations, so a tactic module whose macros insert a theorem
must keep `public import` of the declaring module; such imports belong in the baseline.

usage:
  check_private_imports.py                 run shake and compare with the baseline
  check_private_imports.py --report FILE   use an existing shake report instead of running shake
  check_private_imports.py --update        rewrite the baseline from the current findings
  check_private_imports.py --lake CMD      lake command to run (default `lake`)
"""
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
BASELINE = ROOT / 'scripts' / 'private_imports_baseline.txt'
NON_MODULES = ROOT / 'scripts' / 'non_module_files.txt'


def module_names():
    skip = set()
    if NON_MODULES.exists():
        skip = {l.strip() for l in NON_MODULES.read_text().splitlines()
                if l.strip() and not l.startswith('#')}
    files = subprocess.run(['git', 'ls-files', 'RealRooted/*.lean'], cwd=ROOT,
                           capture_output=True, text=True, check=True).stdout.split()
    mods = []
    for f in files:
        if f in skip:
            continue
        head = (ROOT / f).read_text(encoding='utf-8').split('\n')[:12]
        if 'module' in head:
            mods.append(f[:-len('.lean')].replace('/', '.'))
    return mods


def findings(report):
    out = set()
    for path, body in re.findall(r'^(\S+\.lean):\n((?:[ \t]+.*\n?)+)', report, re.M):
        i = path.rfind('RealRooted/')
        if i < 0:
            continue
        rel = path[i:]
        rem = re.search(r'remove #\[(.*)\]', body)
        add = re.search(r'add #\[(.*)\]', body)
        if not rem or not add:
            continue
        added = {m.group(1) for item in add.group(1).split(',')
                 if (m := re.match(r'\s*(?:meta )?import (\S+)\s*$', item))}
        for item in rem.group(1).split(','):
            m = re.match(r'\s*public (?:meta )?import (\S+)\s*$', item)
            if m and m.group(1) in added:
                out.add(f'{rel}: {m.group(1)}')
    return out


def main(argv):
    lake = argv[argv.index('--lake') + 1] if '--lake' in argv else 'lake'
    if '--report' in argv:
        report = Path(argv[argv.index('--report') + 1]).read_text(encoding='utf-8')
    else:
        proc = subprocess.run([*lake.split(), 'shake', *module_names()], cwd=ROOT,
                              capture_output=True, text=True)
        report = proc.stdout + proc.stderr
    found = findings(report)
    if '--update' in argv:
        BASELINE.write_text(''.join(f'{l}\n' for l in sorted(found)), encoding='utf-8')
        print(f'wrote {len(found)} accepted finding(s) to {BASELINE.relative_to(ROOT)}')
        return 0
    base = set()
    if BASELINE.exists():
        base = {l.strip() for l in BASELINE.read_text(encoding='utf-8').splitlines() if l.strip()}
    new = sorted(found - base)
    gone = len(base - found)
    if new:
        print('error: `lake shake` says only proofs need these `public import`s.')
        print('Make each a plain `import`, or, if a macro quotation needs it,')
        print('record it with `python3 scripts/check_private_imports.py --update`:')
        for l in new:
            print(f'  {l}')
        return 1
    print(f'ok: no new public-import findings ({len(found)} accepted'
          + (f'; {gone} baseline entries are resolved, run --update to drop them' if gone else '')
          + ')')
    return 0


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
