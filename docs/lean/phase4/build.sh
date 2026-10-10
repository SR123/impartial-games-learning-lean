#!/bin/sh
# Phase 4 build. Run from the phase4 directory. Lean 4.26.0, core/Std only.
# Compiles the unchanged phase 1-3 files into build/ and then the phase 4 files.
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
PHASE4_FILES=${PHASE4_FILES-"FiniteNet BinaryReadout ParityCircuit Controller ControllerBits SharedCircuit SelectCircuit LocalRestore Foundation Coverage"}
for f in $PHASE4_FILES; do
  LEAN_PATH=build lean $f.lean -o build/$f.olean > $f.log 2>&1 && echo "$f.lean: exit 0" || { echo "$f.lean: FAILED"; head -60 $f.log; exit 1; }
done
