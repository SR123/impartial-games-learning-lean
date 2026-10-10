#!/bin/sh
# Compile the JMLR reading copy into work/texbuild to obtain the .aux label numbers used by
# tools/validate_site.py (which falls back to evidence_inputs/reference_compile/ if this has not
# been run).  The source in input/ is copied, never modified.  Requires a TeX Live installation
# with latexmk and pdflatex.
set -eu
cd "$(dirname "$0")/.."
mkdir -p work/texbuild
cp -R input/jmlr_source/. work/texbuild/
cd work/texbuild
latexmk -pdf -interaction=nonstopmode paper_jmlr.tex > latexmk.out 2>&1 || { tail -40 latexmk.out; exit 1; }
grep -c '\\newlabel' paper_jmlr.aux
