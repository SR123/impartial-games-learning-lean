# Learning bottlenecks in impartial games

**Overcoming a Learning Bottleneck in Impartial Games: A Circuit Complexity Approach**, by Søren Riis.

- [Read the interactive paper](https://sr123.github.io/impartial-games-learning-lean/).
- [Download the same paper as a PDF](https://sr123.github.io/impartial-games-learning-lean/paper/paper_jmlr.pdf).
- [Explore the proof coverage](https://sr123.github.io/impartial-games-learning-lean/coverage.html).
- [Browse the Lean sources](lean/).

The interactive edition contains the complete paper, optional explanations, illustrations of the three constructions, and links from mathematical claims to formal statements and Lean source. The author's personal account is on a separate, optional page.

## Verification

The development contains **38 Lean modules, 1,588 theorem/lemma declarations and 24,493 source lines**. A fresh isolated rebuild with Lean 4.26.0 succeeded for every module. Axiom reports use only `propext`, `Classical.choice` and `Quot.sound`. The [latest build record](verification/latest/fresh_build.json), [source scan](verification/latest/source_scan.json) and [module logs](verification/latest/logs/) are included.

The paper-to-proof interface comprises 161 claim records and an audited correspondence map. The site distinguishes checked theorems, conditional results, definitions, classical external results, empirical observations, interpretation and open questions. Classical parity lower bounds remain explicit external inputs. Experimental training results are not Lean proofs; this repository does not contain a complete experimental retraining package.

Each shallow component is distinguished from a whole sequential computation. The constructions establish representational possibilities under their stated promises and resource bounds; they do not guarantee discovery through self-play.

## Read locally

Only Python 3 is required to serve the committed website:

```sh
python3 tools/serve.py --dir docs
```

Open `http://127.0.0.1:8765/`. To test the GitHub Pages path:

```sh
python3 tools/serve.py --dir docs --prefix /impartial-games-learning-lean/
```

Open `http://127.0.0.1:8765/impartial-games-learning-lean/`. HTTP serving enables the inline explanation panels; direct file opening uses separate explanation pages.

## Rebuild the interactive edition

Requirements: Python 3.10+, Node.js 18+, a TeX installation providing `pdflatex`, and Poppler's `pdftocairo` and `pdftotext`.

```sh
python3 -m venv .venv
. .venv/bin/activate
pip install -r requirements.txt
npm ci --prefix tools
python3 tools/build_site.py
python3 tools/validate_site.py --no-browser --no-stale-tests
python3 tools/check_sync.py
```

The build writes `dist/`. It checks the pinned manuscript/PDF hashes, declaration identities, claim locks and illustration reference values. The synchronization tool may report that the original upstream working directory is unavailable in a standalone clone; the bundled snapshots remain the reproducible inputs. Browser checks require the validator's optional Playwright/Chromium dependency. The commands above run the static, fidelity, reference and HTTP checks.

After validating a changed edition, run `python3 tools/publish_site.py` to copy the exact build into `docs/`. GitHub Pages serves `main:/docs`. Commit the source changes and generated site together.

## Rebuild the Lean development

Install Lean through elan; `lean-toolchain` selects Lean 4.26.0. The Mathlib revision is pinned in `lean/phase8/lake-manifest.json`.

```sh
cd lean/phase8
lake exe cache get
lake build Mathlib.Data.Real.Archimedean Mathlib.Data.Fintype.BigOperators \
  Mathlib.Algebra.BigOperators.Fin Mathlib.Algebra.Order.BigOperators.Group.Finset \
  Mathlib.Tactic.Linarith Mathlib.Tactic.Positivity Mathlib.Tactic.FieldSimp \
  Mathlib.Tactic.NormNum Mathlib.Tactic.Ring Mathlib.Tactic.GCongr
cd ../..
sh tools/lean/build_bundle.sh work/my-lean-build
python3 tools/lean/parse_build.py work/my-lean-build work/my-lean-build.json
```

Use a new output directory for each build. The build script refuses to reuse an existing one. Lean source files are never rewritten by these commands.

## Manuscript and correspondence

`input/canonical_paper.tex` is the bundled canonical manuscript. `tools/generate_jmlr.py` derives `input/jmlr_source/paper_jmlr.tex`; compile it from `input/jmlr_source/` with `latexmk -pdf`. The complete figure inputs and JMLR style are included. `input/paper_jmlr.pdf` is the PDF reproduced in the website.

After any manuscript edit, regenerate the PDF and interactive edition together. Update the input hashes and correspondence record, retain the actual compile `.aux` and `.log` in `evidence_inputs/reference_compile/`, and inspect any changed claim/explanation links before updating their locks. The builder writes a specific review list when a claim changes. Stable labels connect the manuscript to the proofs. Historical verification records remain dated evidence, rather than being silently rewritten to describe a newer manuscript.

## Repository contents

| Path | Contents |
|---|---|
| `docs/` | Published static interactive edition and identical PDF |
| `input/` | Manuscript sources, PDF, figures and provenance |
| `lean/` | Complete local Lean development and pinned dependencies |
| `content/` | Explanations, visual specifications and author's perspective |
| `data/` | Claim records, declaration exports and Lean reference values |
| `tools/` | Site generation, validation and Lean build tools |
| `evidence_inputs/` | Historical build/audit evidence used by the edition |
| `verification/` | Latest release checks and fresh Lean rebuild evidence |

KaTeX's MIT licence is retained in `docs/assets/katex/LICENSE`. Mathlib is an external Apache-2.0 dependency. The JMLR style retains its original notices. The project-specific Lean and website code and tools are licensed under Apache-2.0. The manuscript, explanatory prose and personal history are excluded from that software licence; see [NOTICE.md](NOTICE.md).

Citation metadata is supplied in `CITATION.cff`. Contact: [s.riis@qmul.ac.uk](mailto:s.riis@qmul.ac.uk).
