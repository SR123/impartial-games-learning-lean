#!/bin/sh
# Rebuild all 38 bundled Lean modules into a NEW, isolated output directory.
#
# Usage:  sh tools/lean/build_bundle.sh <output-dir> [<mathlib-project-dir>]
#
#   <output-dir>            must not exist yet (the script refuses to reuse a directory)
#   <mathlib-project-dir>   a Lake project whose pinned Mathlib (v4.26.0,
#                           2df2f0150c275ad53cb3c90f7c98ec15a56a1a67) has been built, e.g.
#                           lean/phase8 after
#                             (cd lean/phase8 && lake exe cache get && lake build Mathlib.Data.Real.Archimedean \
#                              Mathlib.Data.Fintype.BigOperators Mathlib.Algebra.BigOperators.Fin \
#                              Mathlib.Algebra.Order.BigOperators.Group.Finset Mathlib.Tactic.Linarith \
#                              Mathlib.Tactic.Positivity Mathlib.Tactic.FieldSimp Mathlib.Tactic.NormNum \
#                              Mathlib.Tactic.Ring Mathlib.Tactic.GCongr)
#                           Defaults to lean/phase8.  Needed only for RealNoise and RealFourier.
#
# Requires Lean 4.26.0 (`lean`, `lake` on PATH).  Writes one .olean and one log per module
# into <output-dir>; the sources are only read.
set -e
HERE=$(cd "$(dirname "$0")/../.." && pwd)
SRC="$HERE/lean"
OUT="$1"
MLP="${2:-$SRC/phase8}"
[ -n "$OUT" ] || { echo "usage: $0 <output-dir> [<mathlib-project-dir>]"; exit 2; }
[ -e "$OUT" ] && { echo "refusing to reuse existing directory $OUT"; exit 2; }
lean --version | grep -q "version 4.26.0" || { echo "Lean 4.26.0 required"; exit 2; }
mkdir -p "$OUT/olean" "$OUT/logs"
OUT=$(cd "$OUT" && pwd)
date -u +"%Y-%m-%dT%H:%M:%SZ" > "$OUT/started_utc.txt"
lean --version > "$OUT/lean_version.txt"
c() {  # c <dir relative to lean/> <Module>
  if LEAN_PATH="$OUT/olean" lean --root="$SRC/$1" "$SRC/$1/$2.lean" -o "$OUT/olean/$2.olean" > "$OUT/logs/$2.log" 2>&1; then
    echo "$2 0" >> "$OUT/results.txt"; echo "$2.lean: exit 0"
  else
    echo "$2 1" >> "$OUT/results.txt"; echo "$2.lean: FAILED"; head -40 "$OUT/logs/$2.log"; exit 1
  fi
}
c . NimCore
c . NimRollout
for f in NimGame NimProbability; do c phase2 $f; done
for f in NimAttain Circuit NimRecurrent BitBridge NimCorrBridge AttainCircuit; do c phase3 $f; done
for f in FiniteNet BinaryReadout ParityCircuit Controller ControllerBits SharedCircuit SelectCircuit LocalRestore Foundation Coverage; do c phase4 $f; done
for f in PriorityEncoder ThresholdNet ThresholdInst WholeGame; do c phase5 $f; done
for f in Family Barrier RolloutExec Bypass Classical BoardStore Windows Misc; do c phase6 $f; done
for f in NoiseModel Shootout; do c phase7 $f; done
for f in WeakMastery Fourier; do c phase8 $f; done
MATHLIB_PATH=$(cd "$MLP" && lake env printenv LEAN_PATH)
for f in RealNoise RealFourier; do
  if LEAN_PATH="$MATHLIB_PATH:$OUT/olean" lean "$SRC/phase8/$f.lean" -o "$OUT/olean/$f.olean" > "$OUT/logs/$f.log" 2>&1; then
    echo "$f 0" >> "$OUT/results.txt"; echo "$f.lean: exit 0"
  else
    echo "$f 1" >> "$OUT/results.txt"; echo "$f.lean: FAILED"; head -40 "$OUT/logs/$f.log"; exit 1
  fi
done
date -u +"%Y-%m-%dT%H:%M:%SZ" > "$OUT/finished_utc.txt"
echo "all 38 modules built into $OUT"
