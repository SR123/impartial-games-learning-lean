#!/bin/sh
# Phase 8 build.  Run from the phase8 directory with Lean 4.26.0 (`lean` and `lake` on PATH;
# commit d8204c9f).  Writes only build/, logs/ and (for Mathlib) .lake/ inside phase8.
set -e
lean --version
lean --version | grep -q "version 4.26.0" || { echo "Lean 4.26.0 required"; exit 1; }
mkdir -p build logs

# 1. Pinned Mathlib (lakefile.toml + lake-manifest.json: mathlib tag v4.26.0 =
#    2df2f0150c275ad53cb3c90f7c98ec15a56a1a67).  `lake build` fetches the pinned sources into
#    .lake/packages if they are absent (where the network allows, the official cache
#    `lake exe cache get` may be run first instead of compiling).  Only the modules below and
#    their imports are built.
lake build Mathlib.Data.Real.Archimedean Mathlib.Data.Fintype.BigOperators Mathlib.Algebra.BigOperators.Fin \
  Mathlib.Algebra.Order.BigOperators.Group.Finset Mathlib.Tactic.Linarith Mathlib.Tactic.Positivity \
  Mathlib.Tactic.FieldSimp Mathlib.Tactic.NormNum Mathlib.Tactic.Ring Mathlib.Tactic.GCongr > logs/mathlib_build.log 2>&1
MATHLIB_PATH=$(lake env printenv LEAN_PATH)

# 2. All 34 earlier modules, unchanged and compiled from their own directories, into a FRESH
#    phase8/build; then the four phase-8 files.  One log per module in logs/.
c() {
  if LEAN_PATH=build lean --root="$1" "$1/$2.lean" -o "build/$2.olean" > "logs/$2.log" 2>&1; then
    echo "$2.lean: exit 0"
  else
    echo "$2.lean: FAILED"; head -60 "logs/$2.log"; exit 1
  fi
}
c .. NimCore
c .. NimRollout
for f in NimGame NimProbability; do c ../phase2 $f; done
for f in NimAttain Circuit NimRecurrent BitBridge NimCorrBridge AttainCircuit; do c ../phase3 $f; done
for f in FiniteNet BinaryReadout ParityCircuit Controller ControllerBits SharedCircuit SelectCircuit LocalRestore Foundation Coverage; do
  c ../phase4 $f
done
for f in PriorityEncoder ThresholdNet ThresholdInst WholeGame; do c ../phase5 $f; done
for f in Family Barrier RolloutExec Bypass Classical BoardStore Windows Misc; do c ../phase6 $f; done
for f in NoiseModel Shootout; do c ../phase7 $f; done

# 3. Phase 8: core-only files, then the Mathlib (ℝ) files.
c . WeakMastery
c . Fourier
for f in RealNoise RealFourier; do
  if LEAN_PATH="$MATHLIB_PATH:build" lean "$f.lean" -o "build/$f.olean" > "logs/$f.log" 2>&1; then
    echo "$f.lean: exit 0"
  else
    echo "$f.lean: FAILED"; head -60 "logs/$f.log"; exit 1
  fi
done
echo "phase 8 build complete"
