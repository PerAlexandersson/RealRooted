#!/usr/bin/env bash
# Per-file: back up, batch-replace candidate proofs with a tactic, elaborate,
# keep only what compiled, re-verify, and restore the backup if anything is off.
#
# Usage: TACTIC=grind scripts/golf/golf_driver.sh RealRooted/Foo.lean ...
# Each file is elaborated with LEAN_ENV (default: `lake-workspace env lean` when
# that wrapper exists, else `lake env lean`) against already-built imports; it
# never starts a project build. Run one driver at a time.
set -uo pipefail
cd "$(git rev-parse --show-toplevel)"
SCRATCH=${GOLF_SCRATCH:-$(mktemp -d)}
export GOLF_STATE_DIR=$SCRATCH/golf_state
S=scripts/golf/golf_batch.py
if [ -z "${LEAN_ENV:-}" ]; then
  if command -v lake-workspace >/dev/null 2>&1; then LEAN_ENV="lake-workspace env lean"
  else LEAN_ENV="lake env lean"; fi
fi
export LEAN_NUM_THREADS=${LEAN_NUM_THREADS:-1}
TACTIC=${TACTIC:-grind}
mkdir -p "$SCRATCH/backup" "$GOLF_STATE_DIR"

for f in "$@"; do
  bk="$SCRATCH/backup/$(echo "$f" | tr / _)"
  cp "$f" "$bk"
  echo "=== $f"
  python3 $S try "$f" "$TACTIC" || { cp "$bk" "$f"; continue; }
  $LEAN_ENV "$f" > "$SCRATCH/golf_state/$(echo "$f" | tr / _).log" 2>&1
  python3 $S keep "$f" "$SCRATCH/golf_state/$(echo "$f" | tr / _).log" || { cp "$bk" "$f"; continue; }
  if $LEAN_ENV "$f" > "$SCRATCH/golf_state/$(echo "$f" | tr / _).verify.log" 2>&1; then
    echo "    verified clean"
  else
    echo "    NOT CLEAN after keep -> restoring backup"
    head -5 "$SCRATCH/golf_state/$(echo "$f" | tr / _).verify.log"
    cp "$bk" "$f"
  fi
done
