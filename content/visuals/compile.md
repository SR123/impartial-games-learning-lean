<!-- intro -->
Every gate in these networks has weights and thresholds in $\{0,1\}$. An OR gate fires when at least one of its
literals is 1. NOT is a negated literal. An AND needs two layers: an OR of the negated inputs (that is, NOT AND),
then a negated copy. Choose a formula and set the inputs. The hand-made circuit on the left uses the fewest layers
possible in this gate model. The grid on the right is exactly what the checked compiler of [[fig:threshold-compilation]]
builds for the same formula, with the value of every wire at every layer. The two answer the same truth table, but
only the compiler comes with a general proof.

<!-- notes -->
**How this relates to the Lean proof.** The grid is the output of {{lean:NimAudit.ThresholdNet.compileF}} as Lean
evaluates it on these formulas; the browser only evaluates the exported gates. {{lean:NimAudit.ThresholdNet.compileF_spec}}
proves, for any list of formulas of depth at most $d$, that the network has at most $2d+2$ layers and computes every
formula exactly. The selector bounds in the table of Appendix C come from this rule:
{{lean:NimAudit.Family.rest_ac0}} (Boolean depth at most 20) and {{lean:NimAudit.Family.rest_net}} (at most 42
layers with weights and thresholds 0 or 1).

**What this does not show.** The 42-layer figure is an upper bound for one explicit, deliberately uniform
construction. It is not a lower bound, not a layer count measured in an experiment, and not a statement about which
networks training finds. A more economical network may use fewer layers: for the small boards in the table,
the selector formulas Lean builds have depth 15, so even the uniform compiler produces 32 layers, below the bound of 42.
Proving a sharper general bound would need a separate construction and proof.
