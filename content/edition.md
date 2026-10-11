This interactive edition accompanies *Overcoming a Learning Bottleneck in Impartial Games:
A Circuit Complexity Approach* by Søren Riis. It connects the paper to explanations,
construction diagrams, formal statements and the complete Lean development.

## What the edition contains

- **The paper**, generated as semantic HTML from `paper_jmlr.tex`, the exact source of the 48-page JMLR reading copy.
  Wording, section order, numbering of sections, statements, equations, figures and tables, all 94 LaTeX labels,
  captions, appendices and bibliography are reproduced. The PDF is offered unchanged as the exact layout reference.
- **Three further levels per claim**, opened beneath a statement or on the claim's own page: *Explain this* (intuition,
  an example, why it matters, caveats), *How this is formalised* (objects, hypotheses, proof steps, the precise relation
  to the paper statement, and a machine-readable coverage record), and *Lean statement and source* (the elaborated Lean
  statement, the exact source text, the definitions it uses, the full module and the build evidence).
- **Proof coverage**: every inventoried claim, labelled or not, with one of seven categories.
- **The Lean sources**: all 38 project modules, browsable with line anchors and as raw files with their build scripts and
  pinned dependency metadata.
- **Illustrations** of the constructions, inside "Explain this" and before the formalisation level: exact traces of the
  two-frame selector, the threshold compiler, the rollout controller and the recurrent controller, and a schematic of
  the three bypasses (listed at the end of this page). Each states what it is and how it relates to the Lean results.
- **An author's note**, kept on a separate page that is reached only through its own link. It is separate from the article and its print output.

## How the article is generated

1. `tools/latex2html.py` parses `paper_jmlr.tex` with a project-specific converter that knows exactly the constructs
   used in this paper and **fails on anything else** (an unknown command or environment, an unresolved reference, or a
   formula that KaTeX rejects in strict mode). It replicates the LaTeX counters of the JMLR class (shared theorem
   counter reset per section, global example, figure and table counters, equations per section, appendix letters) and
   records, for every block, its exact comment-stripped source and source lines.
2. Formulas are rendered at build time with KaTeX 0.16.11 (pinned) to HTML and MathML, using the paper's own macros, so
   mathematics is selectable and needs no JavaScript.
3. `tools/build_figures.py` compiles each TikZ picture from its exact source text with the paper's packages and macros
   (`pdflatex` on a measured page with a 6pt border, then `pdftocairo -svg`), and converts the two plot figures from the manuscript's vector PDFs. The plots
   are replots of saved CSV values recorded in the manuscript's figure provenance file; nothing is re-plotted here.
4. `tools/build_site.py` checks every pinned input hash, verifies the 38 bundled Lean files against the audit's
   declaration index and every cited declaration against a fresh Lean export, resolves every claim anchor, and compares
   each claim's statement-source hash with `data/claims.lock.json`.

**When the manuscript is revised**, the article regenerates from the new source automatically, and explanations are
kept because they live in separate files (`content/explanations/`, keyed by claim id; claim metadata in
`data/claims.source.yaml`). The build then **refuses to continue** if the input hashes differ from
`site.config.yaml`, if a claim's anchor or snippet no longer resolves, or if the source of any statement with a claim
record has changed. After an editor has reviewed the affected explanations, `python3 tools/build_site.py --pin`
records the new statement hashes. Old proof metadata is never silently combined with new paper text.

## Conversion notes and limitations

- **Layout.** Line breaks, page breaks and float placement differ from the PDF. Figures and tables appear where they
  occur in the source rather than where LaTeX floated them. Theorem bodies are set upright rather than in italics, the
  end-of-proof mark is □, and run-in paragraph headings are marked up as headings for assistive technology.
- **Mathematics.** Every formula is rendered from its exact TeX. One adaptation was needed: the `align*` environment
  in Appendix H is rendered as an `aligned` block inside display mathematics. No formula was dropped; the validation
  checks that the source formulas and the rendered annotations agree one for one.
- **Figures.** TikZ text is drawn as outlines inside the SVG images, so it is not selectable; each figure has a written
  text alternative (`content/figures.yaml`) that describes what is drawn without adding claims.
- **Tables.** Tables are HTML tables. Rules follow the source (`\hline` placement); fixed column widths are not
  reproduced.
- **Citations and references.** Author–year citations reproduce the PDF's natbib formatting, including merged years.
  The reference list keeps two entries that the text does not cite (Nesterov 1983; Ngo et al. 2018), as in the
  manuscript.
- **Anchors.** Labelled items use their LaTeX labels as anchors (for example `paper.html#thm:sim-ac0`). Unlabelled
  items get stable website-side anchors derived from their titles or claim ids, for example
  `x-remark-scope-of-the-simulation` (Remark A.4), `x-remark-negations` (Remark B.2), `x-example-pairing-strategy`
  (Example 1) and `sec-paper-organisation`. The two `\paragraph` labels (`par:shootout-controller`,
  `par:controller-costs`) are attached to their run-in headings; as in LaTeX, references to them show the enclosing
  section numbers (5.4 and C).
## Source access

The full project-local Lean source is included in this edition, both as browsable pages
with line links and as raw files. The build instructions identify the Lean toolchain,
pinned Mathlib dependency and the commands needed to check the development.

## Validation

The build output is checked by `tools/validate_site.py`: input and PDF hashes; all 94 labels and their numbers against
the LaTeX `.aux` file; every heading, statement header, caption and equation number against the text of the supplied
PDF; the bibliography order; the formula inventory; a word-for-word comparison of the article with an independent
source-derived text, and a classified comparison with the PDF text; every link, asset and fragment in every page;
every claim record against the Lean sources and their audited hashes; a crawl of the whole site under a non-root
prefix; and browser checks of keyboard use, focus return, direct links, back and forward navigation, the print view,
operation without JavaScript and small screens. The results are in `validation/` in the edition's source folder.

## Third-party components

KaTeX 0.16.11 and its fonts are bundled under the MIT licence, included as
`assets/katex/LICENSE`. Mathlib is an Apache-2.0-licensed, pinned build dependency;
its source and compiled libraries are downloaded separately when rebuilding the proofs.

## Archived release

The paper and complete Lean development are preserved in [release v1.0.0 on Zenodo](https://doi.org/10.5281/zenodo.23289503). This DOI identifies the released snapshot. The current paper and interactive edition add the DOI citation after it was issued; their mathematical content and Lean sources are unchanged from that archive.
