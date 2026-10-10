<!-- intro -->
This is the checked two-frame selector run on one example, gate group by gate group. It starts from the two frames
of [[fig:restoration-example]] and ends with the binary output fields shown in [[fig:construction-pipeline]]. Every
value below is computed from the selector's definition for the boards shown. Choose another example to see several
candidates at once, the fallback, or a terminal board. The two examples marked "outside the promise" do not start
from a zero-nim-sum board after a legal move, so the guarantee does not apply to them.

<!-- notes -->
**How this relates to the Lean proof.** The selector is `Family.restS (B, N)`: the local difference circuits
`LocalRestore.dC`, the candidate tests of `SelectCircuit.varSel` and the priority encoder `PriorityEncoder.encode`,
read on the two-frame input `LocalRestore.tf`. {{lean:NimAudit.Family.rest_semantics}} proves that, on the promised
domain, these formulas and the compiled network output a legal move that restores nim-sum 0. Outside the promise the
circuit still computes the values shown, and no theorem says that the result restores 0.

**What this does not show.** The selector does not find a first winning move from an arbitrary board. Given a
zero-nim-sum predecessor it maintains the invariant ([[thm:search-gap]](iii)). The boxes of
[[fig:construction-pipeline]] group operations; the stages here group gates, not network layers.
