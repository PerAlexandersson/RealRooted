#!/usr/bin/env bash
# Time warm elaboration of hotspot files after the refactor.
# Run from the RealRooted/ directory.
#
# Usage: ./scripts/time-lean.sh [file ...]
#   Without arguments, times the default hotspot set.

set -euo pipefail
cd "$(dirname "$0")/.."

DEFAULT_FILES=(
  RealRooted/WagnerX.lean
  RealRooted/WagnerRightSum.lean
  RealRooted/WagnerLeftSum.lean
  RealRooted/WeightedSum.lean
  RealRooted/PosCombo.lean
  RealRooted/AllCombo.lean
  RealRooted/ObreschkoffConverse.lean
  RealRooted/CommonInterleaverSeq.lean
  RealRooted/ProductFamily.lean
  RealRooted/AffineFamily.lean
  RealRooted/MatrixInterlacing.lean
  RealRooted/MaWang.lean
)

FILES=("${@:-${DEFAULT_FILES[@]}}")

printf "%-45s %s\n" "File" "Time"
printf "%-45s %s\n" "----" "----"
for f in "${FILES[@]}"; do
  t=$( { time nice -n 19 lake env lean "$f" 2>/dev/null; } 2>&1 | grep real | awk '{print $2}' )
  printf "%-45s %s\n" "$f" "$t"
done
