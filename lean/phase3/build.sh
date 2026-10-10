#!/bin/sh
# Phase 3 build. Run from the phase3 directory. Lean 4.26.0, core/Std only.
# Compiles the unchanged phase 1-2 files into build/ and then the phase 3 files.
set -e
mkdir -p build
lean --version
lean --root=.. ../NimCore.lean -o build/NimCore.olean > build/NimCore.out
LEAN_PATH=build lean --root=.. ../NimRollout.lean -o build/NimRollout.olean > build/NimRollout.out
LEAN_PATH=build lean --root=../phase2 ../phase2/NimGame.lean -o build/NimGame.olean > build/NimGame.out
LEAN_PATH=build lean --root=../phase2 ../phase2/NimProbability.lean -o build/NimProbability.olean > build/NimProbability.out
PHASE3_FILES=${PHASE3_FILES:-"NimAttain Circuit NimRecurrent BitBridge NimCorrBridge AttainCircuit"}
for f in $PHASE3_FILES; do
  LEAN_PATH=build lean $f.lean -o build/$f.olean > $f.log 2>&1 && echo "$f.lean: exit 0" || { echo "$f.lean: FAILED"; cat $f.log | head -50; exit 1; }
done
