#!/bin/sh
# Phase 2 build. Run from the phase2 directory. Lean 4.26.0, core/Std only.
# Compiles the unchanged parent files to build/ and then the two phase 2 files.
set -e
mkdir -p build
lean --version
lean --root=.. ../NimCore.lean -o build/NimCore.olean > build/NimCore.out
LEAN_PATH=build lean --root=.. ../NimRollout.lean -o build/NimRollout.olean > build/NimRollout.out
LEAN_PATH=build lean NimGame.lean -o build/NimGame.olean > NimGame.log 2>&1
echo "NimGame.lean: exit $?"
LEAN_PATH=build lean NimProbability.lean -o build/NimProbability.olean > NimProbability.log 2>&1
echo "NimProbability.lean: exit $?"
