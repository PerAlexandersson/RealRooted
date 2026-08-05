#!/usr/bin/env bash
# Per-file: back up, batch-replace candidate proofs with a tactic, elaborate,
# keep only what compiled, re-verify, and restore the backup if anything is off.
set -uo pipefail
cd "$(git rev-parse --show-toplevel)"
SCRATCH=${GOLF_SCRATCH:-$(mktemp -d)}
export GOLF_STATE_DIR=$SCRATCH/golf_state
S=.claude/skills/lean-golf/scripts/golf_batch.py
TACTIC=${TACTIC:-grind}
mkdir -p "$SCRATCH/backup" "$GOLF_STATE_DIR"

for f in "$@"; do
  bk="$SCRATCH/backup/$(echo "$f" | tr / _)"
  cp "$f" "$bk"
  echo "=== $f"
  python3 $S try "$f" "$TACTIC" || { cp "$bk" "$f"; continue; }
  lake env lean "$f" > "$SCRATCH/golf_state/$(echo "$f" | tr / _).log" 2>&1
  python3 $S keep "$f" "$SCRATCH/golf_state/$(echo "$f" | tr / _).log" || { cp "$bk" "$f"; continue; }
  if lake env lean "$f" > "$SCRATCH/golf_state/$(echo "$f" | tr / _).verify.log" 2>&1; then
    echo "    verified clean"
  else
    echo "    NOT CLEAN after keep -> restoring backup"
    head -5 "$SCRATCH/golf_state/$(echo "$f" | tr / _).verify.log"
    cp "$bk" "$f"
  fi
done
