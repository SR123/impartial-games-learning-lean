<!-- intro -->
In the restricted model, no family of polynomial-size, fixed-depth networks that reads only the current board
strongly masters NIM ([[thm:singleframe-impossible]], which uses the named classical input on parity). Each bypass
adds a different resource: an extra frame and a promise, executed rollouts, or a growing number of recurrent
updates. This schematic summarises [[fig:rollout_gap]] and [[prop:bypass-interfaces]]; each bypass column links to a
worked, exact construction.

<!-- notes -->
**How this relates to the Lean proof.** {{lean:NimAudit.Bypass.prop_bypass_interfaces}} packages the three
constructions with their shallow components and complete winning strategies;
{{lean:NimAudit.Bypass.bypass_barriers}} records why the complete rollout and recurrent maps cannot themselves be
$\mathrm{AC}^0$ families, assuming the named classical input that parity is not in $\mathrm{AC}^0$
(`Barrier.ParityNotAC0`).

**What this does not show.** Nothing here claims that self-play training discovers these constructions, and the
restricted model is not a model of every neural network.
