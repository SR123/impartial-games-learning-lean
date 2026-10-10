<!-- intro -->
Policy $\pi_j$ subtracts $2^j$ from the first heap of size at least $2^j$, and otherwise subtracts 1 from the first
nonzero heap. A rollout lets both simulated players follow $\pi_j$ until no move is left; its outcome bit is the
parity of the number of moves. Step through the outer controller one tick at a time: it resets, runs head 0's
rollout move by move on a working copy of the board, records the outcome when the rollout ends, reloads the original
board for the next head, and, in the all-head schedule, finally reads out a move. Every outcome bit here is produced by actually running the
rollout; nothing is supplied from outside. The early-exit schedule ([[fig:fsm-shootout-controller]]) stops at the
first outcome 1 and only classifies the position.

<!-- notes -->
**How this relates to the Lean proof.** Each tick is one step of {{lean:NimAudit.Shootout.ostep}}, with the policy
step {{lean:NimAudit.SelectCircuit.policyIdx}} inside the rollout registers {{lean:NimAudit.RolloutExec.rsStep}}.
{{lean:NimAudit.Rollout.run_parity}} identifies the outcome bits with $\sigma_0$ and $\sigma_j\oplus\sigma_0$, and
{{lean:NimAudit.Shootout.ah_counts}} proves that the all-head schedule takes $M+2B+1$ controller ticks, the reset
included; with the single readout this gives $M+2B+2$ evaluations. The browser
re-implements these steps; the agreement is checked against Lean's own evaluation of them.

**What this does not show.** Simulated moves and circuit evaluations are different counts: the $M$ moves are part of
the $M+2B+2$ evaluations. The depth bounds (17 per policy step, 19 for the readout, 34 per controller tick) apply to
one evaluation each. The complete board-to-move computation repeats them a number of times that grows with the board.
That no shallow family computes the complete map is a separate statement ([[prop:bypass-interfaces]] and the text after
it), conditional on the named classical input that parity is not in $\mathrm{AC}^0$.
