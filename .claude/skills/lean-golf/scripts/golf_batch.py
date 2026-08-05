#!/usr/bin/env python3
"""Batch-test a replacement tactic on small Lean proofs, one file at a time.

Phase `try`     : replace every candidate proof body with the given tactic,
                  padding with blank lines so line numbers stay identical.
Phase `keep`    : read a build log, revert every candidate whose lines errored,
                  and compact the survivors.

Usage:
    python3 golf_batch.py try  RealRooted/F.lean [tactic]
    lake env lean RealRooted/F.lean 2>&1 | tee /tmp/log.txt
    python3 golf_batch.py keep RealRooted/F.lean /tmp/log.txt

State lives in .golf_state/<slugified path>.json next to the scratch dir.
All indices are 0-indexed line offsets into the file; `body` is the region
strictly after the `:= by` line through the end of the declaration.
"""
import json, os, re, sys

STATE_DIR = os.environ.get("GOLF_STATE_DIR", ".golf_state")

DECL = re.compile(
    r"^(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|nonrec\s+|noncomputable\s+)*"
    r"(theorem|lemma)\s+([A-Za-z_0-9.'!?]+)")
TAC = re.compile(r"^\s*(?:·\s*)?([a-z_]+[a-z_0-9]*)")
SAFE = {
    'rw', 'simp', 'simp_all', 'unfold', 'constructor', 'exact', 'refine', 'intro',
    'intros', 'ring', 'ring_nf', 'positivity', 'lia', 'norm_num', 'by_cases',
    'field_simp', 'subst', 'push_cast', 'linarith', 'show', 'change', 'have',
    'apply', 'rcases', 'obtain', 'cases', 'gcongr', 'calc', 'grind',
}
SKIP_TEXT = ('sorry', 'induction', 'nlinarith', 'decide', 'native_decide')


def state_path(path):
    os.makedirs(STATE_DIR, exist_ok=True)
    return os.path.join(STATE_DIR, path.replace('/', '_').replace('.lean', '') + '.json')


def candidates(lines):
    """Yield dicts with body region [b0, e0) for each small tactic proof."""
    starts = [i for i, l in enumerate(lines) if DECL.match(l)]
    out = []
    for k, i in enumerate(starts):
        end = starts[k + 1] if k + 1 < len(starts) else len(lines)
        blk = lines[i:end]
        while blk and (blk[-1].strip() == '' or blk[-1].lstrip().startswith('--')):
            blk.pop()
        by = next((j for j, l in enumerate(blk) if l.rstrip().endswith(':= by')), None)
        if by is None:
            continue
        b0, e0 = i + by + 1, i + len(blk)          # body region, 0-indexed
        body = [l for l in lines[b0:e0] if l.strip()]
        if not (2 <= len(body) <= 6):
            continue
        heads = []
        for l in body:
            m = TAC.match(l)
            if not m:
                heads = None
                break
            heads.append(m.group(1))
        if heads is None or not all(h in SAFE for h in heads) or heads == ['grind']:
            continue
        text = '\n'.join(body)
        if any(s in text for s in SKIP_TEXT):
            continue
        out.append({'name': DECL.match(blk[0]).group(2), 'decl_line': i + 1,
                    'b0': b0, 'e0': e0, 'orig': lines[b0:e0]})
    return out


FUSE_HEADS = {'rw', 'simp', 'simp_all', 'unfold', 'ring', 'ring_nf', 'norm_num', 'push_cast'}
ARGS = re.compile(r'\[(.*)\]\s*$')


def fused_tactic(body):
    """`rw [A, B]` + `simp` chains -> a single `simp [A, B]` / `norm_num [A, B]`.

    Returns None when the body contains a tactic this fusion cannot represent.
    """
    args, numeric = [], False
    for l in body:
        head = TAC.match(l).group(1)
        if head not in FUSE_HEADS:
            return None
        if head in ('norm_num', 'push_cast'):
            numeric = True
        rest = l.strip()[len(head):].strip()
        if rest.startswith('only'):
            rest = rest[4:].strip()
        m = ARGS.match(rest)
        if m:
            for a in m.group(1).split(','):
                a = a.strip()
                if a and a not in args:
                    args.append(a)
        elif rest and head == 'unfold':
            for a in rest.split():
                if a not in args:
                    args.append(a)
        elif rest and head not in ('ring', 'ring_nf'):
            return None          # e.g. `rw [...] at h`, `simp at h`
    if not args:
        return None
    return ('norm_num [' if numeric else 'simp [') + ', '.join(args) + ']'


def phase_try(path, tactic):
    lines = open(path, encoding='utf-8').read().split('\n')
    cands = candidates(lines)
    touched = []
    for c in sorted(cands, key=lambda c: -c['b0']):        # bottom-up
        region = lines[c['b0']:c['e0']]
        indent = next((len(l) - len(l.lstrip()) for l in region if l.strip()), None)
        if indent is None:
            continue
        if tactic in ('fuse', 'fuse-ring'):
            t = fused_tactic([l for l in region if l.strip()])
            if t is None:
                continue
            if tactic == 'fuse-ring':
                # `<;>` (not a second line) so the variant also succeeds when
                # `simp` already closed every goal.
                t += ' <;> ring'
        else:
            t = tactic
        c['tactic'] = t
        lines[c['b0']:c['e0']] = [' ' * indent + t] + [''] * (len(region) - 1)
        touched.append(c)
    open(path, 'w', encoding='utf-8').write('\n'.join(lines))
    json.dump({'path': path, 'tactic': tactic, 'touched': touched},
              open(state_path(path), 'w'))
    print(f"{path}: replaced {len(touched)} proof bodies with `{tactic}` "
          f"(line numbers preserved)")


def phase_keep(path, logfile):
    st = json.load(open(state_path(path)))
    log = open(logfile, encoding='utf-8').read()
    bad = {int(m.group(1)) for m in
           re.finditer(re.escape(path) + r':(\d+):\d+: (?:error|warning)', log)}
    lines = open(path, encoding='utf-8').read().split('\n')
    ok, failed = [], []
    for c in st['touched']:
        # Replacement occupies 1-indexed lines b0+1 .. e0, but Lean anchors
        # `unsolved goals` at the `by` token, i.e. 1-indexed line b0.
        if any(c['b0'] <= L <= c['e0'] for L in bad):
            failed.append(c)
        else:
            ok.append(c)
    for c in sorted(failed, key=lambda c: -c['b0']):       # revert, bottom-up
        assert lines[c['b0']].strip() == c.get('tactic', st['tactic']), \
            f"state/file mismatch at {path}:{c['b0'] + 1} ({c['name']})"
        lines[c['b0']:c['e0']] = c['orig']
    for c in sorted(ok, key=lambda c: -c['b0']):           # drop blank padding
        lines[c['b0']:c['e0']] = [l for l in lines[c['b0']:c['e0']] if l.strip()]
    open(path, 'w', encoding='utf-8').write('\n'.join(lines))
    saved = sum(len(c['orig']) - 1 for c in ok)
    print(f"{path}: kept {len(ok)} `{st['tactic']}` proofs (-{saved} lines), "
          f"reverted {len(failed)}")
    if ok:
        print("  kept: " + ", ".join(c['name'] for c in ok))
    if failed:
        print("  failed: " + ", ".join(c['name'] for c in failed))


if __name__ == '__main__':
    phase, path = sys.argv[1], sys.argv[2]
    if phase == 'try':
        phase_try(path, sys.argv[3] if len(sys.argv) > 3 else 'grind')
    elif phase == 'keep':
        phase_keep(path, sys.argv[3])
    else:
        sys.exit(f"unknown phase {phase!r}")
