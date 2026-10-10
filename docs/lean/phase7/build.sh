#!/bin/sh
# Phase 7 build. Run from the phase7 directory. Lean 4.26.0, core/Std only.
# Compiles all earlier modules (unchanged, from their own directories) into a FRESH
# phase7/build directory, then the phase-7 files.  Earlier build directories are untouched.
set -e
mkdir -p build
lean --version
lean --root=.. ../NimCore.lean -o build/NimCore.olean > build/NimCore.out
LEAN_PATH=build lean --root=.. ../NimRollout.lean -o build/NimRollout.olean > build/NimRollout.out
for f in NimGame NimProbability; do
  LEAN_PATH=build lean --root=../phase2 ../phase2/$f.lean -o build/$f.olean > build/$f.out
done
for f in NimAttain Circuit NimRecurrent BitBridge NimCorrBridge AttainCircuit; do
  LEAN_PATH=build lean --root=../phase3 ../phase3/$f.lean -o build/$f.olean > build/$f.out
done
for f in FiniteNet BinaryReadout ParityCircuit Controller ControllerBits SharedCircuit SelectCircuit LocalRestore Foundation Coverage; do
  LEAN_PATH=build lean --root=../phase4 ../phase4/$f.lean -o build/$f.olean > build/$f.out
done
for f in PriorityEncoder ThresholdNet ThresholdInst WholeGame; do
  LEAN_PATH=build lean --root=../phase5 ../phase5/$f.lean -o build/$f.olean > build/$f.out
done
for f in Family Barrier RolloutExec Bypass Classical BoardStore Windows Misc; do
  LEAN_PATH=build lean --root=../phase6 ../phase6/$f.lean -o build/$f.olean > build/$f.out
done
PHASE7_FILES=${PHASE7_FILES-"NoiseModel Shootout"}
for f in $PHASE7_FILES; do
  LEAN_PATH=build lean $f.lean -o build/$f.olean > $f.log 2>&1 && echo "$f.lean: exit 0" || { echo "$f.lean: FAILED"; head -60 $f.log; exit 1; }
done
