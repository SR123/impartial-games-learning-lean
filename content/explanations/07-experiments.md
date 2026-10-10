<!-- Section 7: experiments.  Empirical records rest on saved runs; nothing here is a Lean proof. -->

<!-- explain: c-exp-goal -->
The paragraph states the limit of the experiments up front. The strong goal would be to show that an AlphaZero-style
learner discovers good play by self-play once a bypass is available. That is not shown. What is reported is an
intermediate step: supervised and imitation experiments that supply guidance which outcome-only self-play would have to
generate for itself.

<!-- formal: c-exp-goal -->
A scope statement. The open question is recorded as {{claim:c-selfplay-open}}.

<!-- explain: c-exp-repr -->
Setup facts for both experiments: heaps are written in binary with $k$ bits; the one-frame (1F) input is the current
board, the two-frame (2F) input concatenates previous and current boards (on a first move the previous frame is set equal
to the current one). Actions are "set heap $i$ to value $v$", giving $N\cdot2^k$ logits.

Two evaluation conventions are distinguished: restoration accuracy takes an *unmasked* argmax over all logits (an
illegal prediction counts as wrong), while game play and the rollout routines mask illegal moves.

<!-- formal: c-exp-repr -->
**How this is covered.** A description of the saved experimental implementation, taken from the paper; the edition
reproduces it unchanged and does not re-run anything. It is not formalised. The formal model of Section 2 (fixed-scale
literal-threshold gates) is different from these floating-point networks.

<!-- explain: table:arch -->
Both restoration agents use the same small multilayer perceptron: input, two hidden layers of width $H$ (the first with
LayerNorm and ReLU, the second with ReLU) and a linear output of $N\cdot2^k$ logits. There is no value head. The 2F model
has a wider input ($2Nk$ bits) and therefore $NkH$ more first-layer parameters (20,480 in the reported setting).

<!-- formal: table:arch -->
**How this is covered.** An empirical setup record from the saved notebook; not formalised. These are ordinary
floating-point networks, not instances of the fixed-scale gate model.

<!-- explain: c-exp-loss -->
The target for each input is a probability distribution spread evenly over all optimal restoration moves from the
current position, and the network is trained with cross-entropy against that soft target (on unmasked logits). No value
loss is used.

<!-- formal: c-exp-loss -->
**How this is covered.** Empirical setup; not formalised.

<!-- explain: c-exp-criteria -->
Two task-level measures are reported instead of full game tournaments: move-level restoration correctness (does the
predicted move reach nim-sum zero?), measured only on positions with nonzero nim-sum, since zero-nim-sum positions have
no winning move; and position-level $P/N$ classification by the shootout controller.

<!-- formal: c-exp-criteria -->
**How this is covered.** Empirical definitions. The mathematical fact they rely on, that positions with nim-sum zero have
no winning move, is checked ({{claim:thm:nim-win}}).

<!-- explain: c-restoration-equivalence -->
In NIM, "restore after the opponent leaves a $P$-position" is the same task as "find a winning move from the current
position", provided the previous position had nim-sum zero: any opponent move from a zero nim-sum produces a nonzero one
(a winning position for the agent), and every optimal reply returns to zero.

<!-- formal: c-restoration-equivalence -->
{{lean:NimAudit.Game.move_from_zero}} (every legal move from nim-sum zero reaches a nonzero nim-sum),
{{lean:NimAudit.Game.exists_move_to_zero}} (a move back to zero exists) and {{lean:NimAudit.Game.lose_iff}} (the positions
with nim-sum zero are exactly the losing ones, so "optimal" means "to nim-sum zero").

<!-- explain: c-exp-data -->
Each training example is built in three steps: take a random winning position and apply an optimal move (so the result
$p$ has nim-sum zero); apply one uniformly random legal move to get $p'$; label $p'$ with the uniform distribution over
all optimal moves. This reproduces exactly the restoration situation: the opponent departs from a $P$-position and the
agent must restore it. There are $10^6$ examples, split 80/10/10 with seed 0.

The paper notes two ways in which this helps the learner compared with earlier studies: binary heap encoding, and
perfectly labelled restoration targets instead of sparse win/loss outcomes. It also notes that the teacher's
first-winning-heap rule makes the distribution of predecessors nonuniform.

<!-- formal: c-exp-data -->
**How this is covered.** Empirical setup, described from the saved run. The fact that $p$ has nim-sum zero and that every
label move restores zero follows from {{claim:c-restoration-equivalence}}. The dataset itself is not part of this edition.

<!-- explain: c-exp-training -->
Both models are trained with Adam (learning rate $10^{-3}$, batch size 512) for 200 epochs, and ten checkpoints are saved
at epochs 1, 23, 45, 67, 89, 112, 134, 156, 178 and 200.

<!-- formal: c-exp-training -->
**How this is covered.** Empirical setup; not formalised. The edition uses the saved checkpoints' results only and does
not create intermediate checkpoints.

<!-- explain: c-exp-metric -->
A held-out example counts as correct if the argmax over *all* action logits is one of the optimal moves. Illegal
predictions are wrong; every legal optimal move is accepted.

A detail that matters for the decimals: the saved code averaged per-batch accuracies with equal weight, including the
shorter last batch. The reported numbers are those batch means, not exact counts divided by 100,000.

<!-- formal: c-exp-metric -->
**How this is covered.** An empirical definition, including the averaging convention of the saved implementation. Not
formalised.

<!-- explain: c-exp-result-1f2f -->
**The result.** In the saved run ($N=20$ heaps, $k=4$ bits, $10^6$ examples), the 1F model stays at low test restoration
accuracy throughout (about 0.075–0.081 across checkpoints). The 2F model learns: 0.209 at epoch 1, 0.538 at epoch 23,
0.876 at epoch 45, 0.989 at epoch 67 and 0.99998 by epoch 178 (still at least 0.99993 at epoch 200).

**What it shows.** Under this supervised protocol, transition information makes restoration much easier to learn.

**What it does not show.** That 1F is at a random-move baseline (no such baseline was measured), worst-case mastery,
self-play learning, robustness across seeds, or anything about the asymptotic lower bound.

<!-- formal: c-exp-result-1f2f -->
**How this is covered.** Empirical, from the saved checkpoint-accuracy file of run `20260214_120801_cd18fc9f`. The
independent audit's correspondence row for this section notes that the numerical baseline theorems do not certify
checkpoints or the cause of the plateau. Lean proves nothing about training runs.

<!-- explain: fig:valacc-H20k4 -->
The validation curve, one point per epoch: 1F stays near 0.08; 2F rises quickly to a plateau near 0.54, stays there
from about epoch 8 to about epoch 30 in the plot, then climbs steeply to near-perfect accuracy.

The plateau suggests a learning bottleneck that training eventually overcomes. It is a different thing from the
representational lower bound: the 2F model *can* represent the solution, and eventually finds it.

<!-- formal: fig:valacc-H20k4 -->
**How this is covered.** Empirical. The figure is a vector replot of the saved training-history CSV (400 rows; SHA-256
`705b6d5d031a…`) with no smoothing, subsampling or new experiment, as recorded in the figure provenance file supplied
with the manuscript. The edition converts the manuscript's PDF figure to SVG without re-plotting.

<!-- explain: fig:testacc-H20k4 -->
Test accuracy at the ten saved checkpoints. The checkpoints are sparse, so they confirm the improvement beyond the
plateau but do not show its timing; the denser validation curve does.

<!-- formal: fig:testacc-H20k4 -->
**How this is covered.** Empirical. Replotted from the saved checkpoint test-accuracy CSV (20 rows; SHA-256
`766f9934272d…`) without changes to the values; converted to SVG for this edition without re-plotting.

<!-- explain: c-plateau -->
Even with the transition in the input, learning goes in stages: fast progress, a plateau near 0.54, then a sharp rise.
The paper reads this as evidence about training dynamics in this one run, not as a further circuit lower bound.

<!-- formal: c-plateau -->
**How this is covered.** An empirical observation of the saved run. Its cause is not established, in the paper or here.

<!-- explain: c-diagnostic -->
A closer look at the saved checkpoints makes the plateau concrete. For a predicted move "set heap $i$ to $v$", compare
the change it makes, $p'_i\oplus v$, with the change needed (the nim-sum of $p'$):

- at epoch 23 the model makes only legal moves and gets the upper three bits of the change right on 99.998% of the
  100,000 test positions; of its 46,206 failures, 46,204 are wrong only in the lowest bit;
- at epoch 45 all 12,437 errors are in that bit; at epoch 178 only two errors remain, both of that kind.

These counts weight examples equally, unlike the batch-mean accuracies in the figures.

<!-- formal: c-diagnostic -->
**How this is covered.** An empirical diagnostic computed from the saved checkpoints on a reconstructed and independently
verified test set, as stated in the paper. Not formalised; the edition does not recompute it.

<!-- explain: c-plateau-interpretation -->
At the level of outputs, the later improvement consists of getting the lowest bit of the change right while keeping the
upper bits. That supports "staged acquisition". The paper is careful about what it does *not* conclude:

- it does not identify an internal representation or explain why optimisation follows this order;
- the plateau's closeness to $8/15\approx0.533$ does not establish a random-bit guessing mechanism (that number assumes a
  particular distribution and prediction rule);
- probes, interventions and independent runs would be needed.

<!-- formal: c-plateau-interpretation -->
Interpretation of empirical data. The arithmetic fact $8/15$ (the fraction of nonzero 4-bit nim-sums with lowest bit $1$)
is checked ({{claim:c-baseline-arith}}); whether it has anything to do with the plateau is not established.

<!-- explain: c-exp-provenance -->
The scope of the restoration result: one configuration ($N=20$, $k=4$, $10^6$ examples, seed 0), identified by its run
suffix and saved notebook. No robustness across hyperparameters, board sizes or seeds is claimed; independent seeds,
matched-parameter controls and out-of-distribution tests are listed as useful follow-ups.

<!-- formal: c-exp-provenance -->
**How this is covered.** A provenance statement. The run records are retained with the local review materials and are
not part of this edition.

<!-- explain: c-fsm-setup -->
The second experiment tests the single-frame rollout bypass with *learned* approximations of the structured policies,
controlled by the shootout automaton. Setting: $N=20$ heaps, $k=4$ bits, so $B=4$ heads; a balanced test set of 2,000
positions, half with $\sigma=0$ and half with $\sigma\ne0$. The trained floating-point networks are not claimed to
satisfy the formal gate restrictions.

<!-- formal: c-fsm-setup -->
**How this is covered.** Empirical setup from the saved notebook; not formalised.

<!-- explain: c-tie-breaking -->
When several heaps qualify for the same move of $\pi_j$ (for example several heaps of size at least $2^j$), the choice
does not matter for the outcome: every complete rollout has the same number of moves,
$\sum_i\lfloor h_i/2^j\rfloor+\sum_i(h_i\bmod2^j)$, whichever eligible heap is used each time. So the training labels can
spread probability evenly over all equivalent actions without changing the channel bit.

<!-- formal: c-tie-breaking -->
{{lean:NimAudit.Rollout.run_length}}: every complete run of $\pi_j$ ({{lean:NimAudit.Rollout.Run}}, built from
{{lean:NimAudit.Rollout.PolicyMove}} steps with arbitrary tie-breaking) has exactly that length.
{{lean:NimAudit.Rollout.run_parity}}: its parity is the channel bit of the nim-sum.

<!-- explain: c-fsm-training -->
The four heads share a trunk (two hidden layers of width 256 with LayerNorm) and have separate linear outputs of 320
logits each. They are trained by imitation of $\pi_0,\dots,\pi_3$ with soft targets: Adam, learning rate $10^{-3}$, batch
1024, 12 epochs, $2\times10^5$ examples, a 20,000-example validation set, seed 7.

<!-- formal: c-fsm-training -->
**How this is covered.** Empirical setup from the saved notebook; not formalised.

<!-- explain: c-fsm-metric -->
Two different things are measured. Per-head accuracy asks whether the learned head's rollout outcome equals the exact
teacher's outcome (the correct channel bit). The controller's classification uses the OR of the queried outcomes. A head
can be wrong on a channel without changing the final OR decision.

<!-- formal: c-fsm-metric -->
**How this is covered.** Empirical definitions. The exact teacher heads' channel values are the checked identities of
{{claim:prop:rollout-sufficiency}}; the OR rule is {{claim:par:shootout-controller}}.

<!-- explain: c-fsm-results -->
**Result.** The learned multi-head controller classifies all 2,000 test positions correctly, matching the teacher's
decisions.

**But.** The saved per-head channel accuracies are 1.0000, 1.0000, 0.7345 and 0.7400. So the learned model does *not*
recover every channel bit exactly. Early stopping leaves some channels unqueried, and queried errors need not change the
OR. These are transcribed saved outputs; a fresh end-to-end rerun and reached-head error counts would be needed for a
stronger claim.

<!-- formal: c-fsm-results -->
**How this is covered.** Empirical, transcribed from the saved notebook output. The audit's correspondence row for this
section records it as empirical with partly checked arithmetic.

<!-- explain: c-baseline-arith -->
The single-head baseline declares "$N$-position" exactly when $r_0=\sigma_0=1$. With 4 bits there are 15 nonzero
nim-sums, of which 8 are odd: $1,3,5,\dots,15$. So the classifier detects $8/15\approx0.533$ of $N$-positions and never errs
on $P$-positions ($\sigma=0$ has $\sigma_0=0$). On a balanced set its accuracy is
$\tfrac12\cdot1+\tfrac12\cdot\tfrac8{15}=\tfrac{23}{30}\approx0.767$.

Caveat: this describes that particular classifier. It is not the winning-move bound of [[thm:search-gap]] and not a limit
on other classifiers.

<!-- formal: c-baseline-arith -->
- {{lean:NimAudit.Misc.detected_count}}: among the $2^B-1$ nonzero $B$-bit values exactly $2^{B-1}$ are odd.
- {{lean:NimAudit.Misc.baseline_numbers}}: for $B=4$: $8$ odd values, $15$ nonzero values, and
  $\tfrac12\cdot1+\tfrac12\cdot\tfrac8{15}=\tfrac{23}{30}$.
- {{lean:NimAudit.Misc.baseline_P}}: the classifier never errs on $P$-positions.
- {{lean:NimAudit.Misc.board_recall}}: for uniformly random boards the detected fraction among nonzero nim-sums is
  $2^{B-1}/(2^B-1)$, so the value-level ratio is also the board-level ratio.

<!-- explain: c-baseline-observed -->
On the finite test set the single-head baseline scored 0.768 accuracy and 0.536 recall, close to the theoretical
0.767 and 0.533 and consistent with sampling variation on a finite test set. The exact teacher head gives the same
0.768 and 0.536 in Table 2.

<!-- formal: c-baseline-observed -->
**How this is covered.** Empirical (saved output). The theoretical values are checked in {{claim:c-baseline-arith}}.

<!-- explain: c-different-metrics -->
Two numbers near 0.53 appear in the paper: the single-head recall $8/15$ and the restoration plateau near 0.54. They
measure different things (detecting nonzero nim-sums through the lowest bit versus choosing a complete cancelling move),
and their resemblance is not evidence of a shared mechanism.

<!-- formal: c-different-metrics -->
An interpretive caution; nothing is formalised.

<!-- explain: c-early-stopping -->
The controller used 2.87 rollouts on average instead of the worst case 4, because every $N$-position with $\sigma_0=1$ is
detected by head 0 after one rollout; only positions with $\sigma_0=0$ need further heads (and $P$-positions always need
all four). The result is for the saved seed-7 configuration and does not establish correctness on all positions,
robustness across seeds, or self-play discovery.

<!-- formal: c-early-stopping -->
**How this is covered.** The 2.87 average is empirical. That the depicted controller stops after one query when head 0
reports 1, and uses at most $B$ queries, is checked ({{claim:fig:fsm-shootout-controller}}).

<!-- explain: tab:fsm-shootout -->
The table reports, for single-head and multi-head (FSM) evaluation, with the learned model and with the exact teacher
heads: the number of heads, the mean number of rollouts, overall $P/N$ accuracy and $N$-position recall. Model and teacher
rows coincide.

<!-- formal: tab:fsm-shootout -->
**How this is covered.** Empirical (saved outputs), apart from the theoretical values discussed in
{{claim:c-baseline-arith}}.

<!-- explain: c-reproducibility -->
The status of the experimental record: the notebooks and checkpoint file are retained with the local review materials,
but the public repository previously named for this work does not provide a reproducibility package. The paper therefore
does not claim public availability of code and data, and lists a versioned package and repeated evaluation as future
work.

<!-- formal: c-reproducibility -->
**Status: open (future work stated in the paper).** This edition bundles the Lean sources and their build, not the
experimental code or data.
