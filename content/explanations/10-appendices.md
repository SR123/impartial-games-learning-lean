<!-- Appendices A-H. -->

<!-- explain: app:precision -->
The representable parameters are the fixed grid $\mathcal Q_{W,D}=\{\ell/D:0\le\ell\le W\}$: step $1/D$, values up to
$W/D$, and the same set for every input length. The appendix stresses that this is a Boolean gate abstraction:
neither floating-point nor general signed fixed-point networks satisfy it automatically, and what drives the AC⁰
containment is that thresholds do not grow with fan-in, not that a number format is finite. Negations on wires are
allowed, as in AC⁰.

<!-- formal: app:precision -->
{{lean:NimAudit.AC0.Gate}} stores integer coefficients, negation flags and an integer threshold;
{{lean:NimAudit.AC0.Gate.Valid}} bounds them by $W$; {{lean:NimAudit.AC0.gate_rat_iff}} proves that with denominator
$D>0$ the rational form (weights $a_j/D$, threshold $b/D$, Heaviside) fires exactly when the integer form does.

<!-- explain: def:NN-formal -->
A literal-threshold network of depth $L$: layer $0$ is the input; each unit in layer $\ell$ looks at the previous layer's
outputs, possibly negates some of them, takes a weighted sum with grid weights, and outputs $1$ if the sum reaches its
grid threshold. The output is the last layer (or some of its coordinates). Widths are polynomial in $n$.

Example: with weights $1$ and threshold $1$, a unit is an OR of its (possibly negated) inputs; with one negated input it
is a NOT.

<!-- formal: def:NN-formal -->
- {{lean:NimAudit.AC0.Gate}}: coefficients $a_j$, negation bits $\eta_j$ and threshold $b$; the gate fires iff
  $b\le\sum_j a_j[z_j\oplus\eta_j]$.
- {{lean:NimAudit.AC0.Layer}} and {{lean:NimAudit.AC0.evalNet}}: layers of gates reading the previous layer, applied in
  order.
- {{lean:NimAudit.AC0.NetValid}}: every gate valid for the grid bound $W$.
- {{lean:NimAudit.AC0.gate_rat_iff}}: equivalence with the paper's rational Heaviside form.
- {{lean:NimAudit.FiniteNet.netFormula_spec}}: the explicit finite-input semantics (an $n$-bit input, zero-extended)
  and its simulation by one formula per output.

<!-- explain: def:RNN-formal -->
A recurrent model with a hidden state, updated by a fixed-depth threshold network that reads the current input and
earlier states within a window. The crucial restriction: each inference starts from an input-independent initial state
and makes at most $T$ updates *in total*; no state may smuggle in extra computation from before the window. Unrolled, it
is a feedforward network of depth $O(LT)$.

Caveat (stated in the definition): bounding only how far back each update looks does not bound the total unrolling;
the persistent model of Section 5.5 deliberately makes more than $T$ updates.

<!-- formal: def:RNN-formal -->
- {{lean:NimAudit.Windows.window_ac0}}: for a valid $L$-layer cell reading the input block and the $w$ most recent states
  ({{lean:NimAudit.Windows.winIn}}; state after $t$ updates {{lean:NimAudit.Windows.wState}}, with an input-independent
  initial state), the state after $T$ updates is computed by formulas of depth at most $3LT$ reading only the $T$ input
  blocks.
- {{lean:NimAudit.Windows.window_size_closed}}: a closed polynomial size bound for fixed $T$.
- {{lean:NimAudit.AC0.rnn_ac0}}: the one-state version with total unrolling $T$.

<!-- explain: def:LTST-formal -->
An "attention-style" model is admitted only in a gate-realised form: every score computation, input-dependent
coefficient selection, encoding and aggregation must itself be a polynomial-size, constant-depth network of the permitted
literal-threshold gates, with Boolean intermediate states and bounded total unrolling. Then the simulation theorem
applies by composition.

Caveat: merely restricting parameters or coefficients to a finite set is not enough, and nothing is claimed about
standard softmax attention.

<!-- formal: def:LTST-formal -->
{{lean:NimAudit.Windows.staged_ac0}}: a model given as a list of $K$ stages ({{lean:NimAudit.Windows.runStages}}), each a
valid network of at most $L$ layers with bounded widths, is computed by formulas of depth at most $3KL$ and explicit size,
reading only the inputs. Why a finite coefficient set alone is insufficient: {{claim:rem:ac0-scope.model}}.

<!-- explain: x-remark-scope-of-the-simulation -->
The remark names the reason the simulation works: $L$, $T$, $W$ and $D$ are constants, and each unit's parameters come
from a finite set that does not depend on $n$. Appendix B then gives the explicit circuit construction.

<!-- formal: x-remark-scope-of-the-simulation -->
An explanatory remark on the hypotheses of {{claim:thm:sim-ac0}}.

<!-- explain: lem:unit-ac0 -->
**Statement.** A single unit $f(z)=\mathbf H(\sum_j w_jz_j-\theta)$ with grid weights and threshold is computed by a
depth-2 AC⁰ circuit (an OR of ANDs) of size $O(m^W)$.

**Proof idea.** Multiply by $D$: $f(z)=1$ iff $\sum_j a_jz_j\ge b$ with integers $0\le a_j,b\le W$. If $b=0$ the unit is
constantly $1$. Otherwise each active input contributes at least $1$, so if the sum reaches $b$, greedily choosing active
inputs reaches $b$ after at most $b\le W$ steps. Hence $f(z)=1$ iff some set $T$ of at most $W$ inputs with
$\sum_{j\in T}a_j\ge b$ is all true: an OR over at most $\sum_{r\le W}\binom mr=O(m^W)$ ANDs.

**Example.** $W=2$, $D=1$, weights $(1,1,2)$, threshold $2$: $f=(z_1\wedge z_2)\vee z_3$.

<!-- formal: lem:unit-ac0 -->
- {{lean:NimAudit.AC0.Gate.bounded_witness}}: if the gate fires, an initial segment of its active literals, of length at
  most the threshold, already reaches the threshold.
- {{lean:NimAudit.AC0.gate_ac0}}: the DNF {{lean:NimAudit.AC0.dnf}} computes the gate exactly; depth at most $3$ when NOT
  nodes are counted; size at most $1+(m+1)^W(2W+1)$; it reads only the gate's inputs. Edge cases $b=0$, $m=0$ and $W=0$
  are included.
- {{lean:NimAudit.ClassicalBoundary.dnf_aoDepth}}: in the classical convention (negations on inputs not counted) the same
  DNF has AND/OR depth at most $2$, as the lemma states.

<!-- explain: x-remark-negations -->
If some inputs are negated before weighting, each term of the DNF simply uses $\neg z_j$ instead of $z_j$ for those
inputs. AC⁰ has NOT gates, so the lemma still applies.

<!-- formal: x-remark-negations -->
Negation flags are part of the Lean gate model from the start, so {{lean:NimAudit.AC0.gate_ac0}} and the DNF correctness
theorem {{lean:NimAudit.AC0.eval_dnf}} already cover negated inputs.

<!-- explain: lem:layer-ac0 -->
A layer is $m'$ units side by side. Apply the one-unit lemma to each and place the circuits in parallel: depth stays $2$
and size is $m'\cdot O(m^K)$, polynomial. Composing a constant number of layers then proves [[thm:sim-ac0]].

<!-- formal: lem:layer-ac0 -->
- {{lean:NimAudit.AC0.eval_compileLayer}}: substituting the previous layer's formulas into each gate's DNF computes the
  layer ({{lean:NimAudit.AC0.compileLayer}}).
- {{lean:NimAudit.AC0.compileLayer_size}}: each output's size is at most $G\cdot(S+1)$ with $G=1+(M+1)^W(2W+1)$, for
  previous formulas of size at most $S$ and fan-in at most $M$.
- {{lean:NimAudit.AC0.compileLayer_depth}}: depth grows by at most $3$ per layer.

<!-- explain: app:impl -->
Appendix C is the engineering behind the bypasses. All constructions share a few shallow operations: a heap is a $B$-bit
block; a move is a validity bit, a binary heap index and a $B$-bit value. The circuits have polynomial size in their
supplied input length and depth independent of $N$ and $B$. Every XOR called shallow combines *two* bits (or a fixed
number under a bounded-change promise); an XOR of arbitrarily many rows is never treated as a primitive.

<!-- formal: app:impl -->
The appendix is checked piece by piece; see {{claim:c-candidate-moves}}, {{claim:c-binary-index}},
{{claim:c-recurrent-update}}, {{claim:c-threshold-realisation}}, {{claim:c-depth-table}} and
{{claim:par:controller-costs}}. Headline theorems: {{lean:NimAudit.PriorityEncoder.encode_correct}} (binary output),
{{lean:NimAudit.ThresholdNet.compileF_spec}} and {{lean:NimAudit.ThresholdNet.compileF_fixed_grid}} (the threshold
compiler), {{lean:NimAudit.BoardStore.bs_net}} (one instance).

<!-- explain: c-candidate-moves -->
**Delta bits.** On a legal transition only one heap changes, so bit $k$ of the delta is the OR over heaps of
$x_{i,k}\oplus x'_{i,k}$: with at most one changed row, OR equals XOR.

**Candidate test.** For a target $\delta$, compute $y_i=x_i\oplus\delta$ for all heaps in parallel and test $y_i<x_i$ with
a shallow comparator: OR over the highest differing bit, with equality above it and $y_{i,k}=0$, $x_{i,k}=1$ there.

**Fallback.** If no heap cancels, subtract one from the first nonzero heap: bit $k$ of $x-1$ is bit $k$ of $x$ XOR "all
lower bits are zero". The move is invalid exactly on the terminal board.

<!-- formal: c-candidate-moves -->
- {{lean:NimAudit.LocalRestore.dC_eval}} and {{lean:NimAudit.LocalRestore.localDelta_eq}}: the OR-of-XORs delta, and its
  equality with $\operatorname{nim}(Q)\oplus\operatorname{nim}(Q')$ when at most one heap differs.
- {{lean:NimAudit.AttainCircuit.cancel_iff_bit}}: for $t\ne0$, $x\oplus t<x$ iff $x$ has $t$'s top bit.
- {{lean:NimAudit.SelectCircuit.genSel_correct}}: the generic first-index selector (primary test with its new value,
  fallback "subtract one from the first nonzero heap") is exact.
- {{lean:NimAudit.SelectCircuit.varSel_correct}}: with the target on input wires, the selector computes the specified move
  for every target value.

<!-- explain: c-binary-index -->
Several heaps may qualify; the circuit must pick the first and output its index in binary. With candidate flags $s_i$:
$f_i=s_i\wedge\bigwedge_{j<i}\neg s_j$ marks the first candidate, and index bit $k$ is the OR of the $f_i$ whose index has
bit $k$ set. Masking the candidate values by $f_i$ and taking ORs gives the value bits. All of this is constant depth and
polynomial size: no hidden "search for the first true flag".

<!-- formal: c-binary-index -->
- {{lean:NimAudit.PriorityEncoder.encode_correct}}: for every input assignment the encoder's binary output decodes to
  exactly the selection readout (first true flag and its value), and to "no move" when the readout is invalid or no flag
  is true, provided $N\le2^r$.
- {{lean:NimAudit.PriorityEncoder.encode_noflag}}, {{lean:NimAudit.PriorityEncoder.encode_least}},
  {{lean:NimAudit.PriorityEncoder.encode_zero}}, {{lean:NimAudit.PriorityEncoder.encode_one}}: the edge cases named in the
  paper (no candidate, several candidates, $N=0$, $N=1$ with zero index width).
- {{lean:NimAudit.PriorityEncoder.encode_bound}}: depth grows by at most $3$; each formula has size at most $4U^3$ with
  $U=(N+2)(S+2)$.

<!-- explain: c-recurrent-update -->
In scan mode the update XORs the row into the accumulator, two bits at a time. In replay mode it tests the row against the
stored summary, keeps the first cancelling candidate and a fallback, and increments a counter (bit $k$ flips when all lower
bits are one, also shallow). Mode, validity and reset flags select which registers change. On well-formed streams every
reachable register fits its width, and the emitted move uses the summary from the same board's first scan. The replayed
rows come from the input protocol; the controller does not secretly store the board.

<!-- formal: c-recurrent-update -->
- {{lean:NimAudit.ControllerBits.step_refines}} and {{lean:NimAudit.ControllerBits.brun_refines}}: the bit-level update
  (one formula per state and output bit, depth at most 8) tracks the semantic controller exactly, step by step and over
  whole runs, on states whose registers fit.
- {{lean:NimAudit.ControllerBits.bstep_reset}}: a reset token restores the initial encoding from any bit state whatsoever.
- {{lean:NimAudit.Controller.stream_fits}}: along well-formed streams every visited state fits its fields.
- {{lean:NimAudit.Family.ctrl_ac0}}: the update formulas form an AC⁰ family of depth at most 8.

<!-- explain: c-threshold-realisation -->
Any of these Boolean circuits can be turned into a network of the paper's fixed-scale gates with weights and thresholds in
$\{0,1\}$: an OR gate is a threshold-1 gate; NOT is a negated literal; AND is built by De Morgan from ORs and negations, so
no threshold ever needs to equal a growing fan-in. For $K$ output formulas of depth at most $d$ and total size $S$ on fewer
than $n$ inputs, the compiler builds one network with at most $2d+2$ layers, at most $(2d+1)S+K$ gates, and widths and
fan-ins at most $S+n$, and every output equals its formula on every input.

<!-- formal: c-threshold-realisation -->
- {{lean:NimAudit.ThresholdNet.compileF_spec}}: for formulas reading inputs below $n$ with depth at most $D$, the network
  {{lean:NimAudit.ThresholdNet.compileF}} has exact outputs (and false beyond them), is valid for $W=1$, reads only the $n$
  inputs in its first layer, has at most $2D+2$ layers, widths and fan-ins at most $S+n$, and at most $(2D+1)S+K$ gates.
- {{lean:NimAudit.ThresholdNet.compileF_fixed_grid}}: every compiled gate fires in the paper's rational form with $D=1$
  exactly when it fires in integer form.
- {{lean:NimAudit.ThresholdNet.compileF_bounded}}: the width and fan-in bound.

<!-- explain: c-depth-table -->
The table gives certified, unoptimised bounds for **one evaluation** of each component, as Boolean depth and as threshold
layers: two-frame move selector ≤20 / ≤42; multi-head readout given outcomes ≤19 / ≤40; one policy step ≤17 / ≤36; one
recurrent update ≤8 / ≤18; one shootout controller tick ≤34 / ≤70. Together with polynomial size bounds, they certify the
components' AC⁰ resources.

Caveat: these are per evaluation. A rollout or a row scan repeats evaluations, and that time is part of the algorithm.

<!-- formal: c-depth-table -->
Each row is a family certificate for the actual objects used elsewhere:

| Component | Formula family (depth) | Network family (layers) |
|---|---|---|
| Two-frame selector | {{lean:NimAudit.Family.rest_ac0}} (20) | {{lean:NimAudit.Family.rest_net}} (42) |
| Multi-head readout | {{lean:NimAudit.Family.mh_ac0}} (19) | {{lean:NimAudit.Family.mh_net}} (40) |
| One policy step | {{lean:NimAudit.Family.pol_ac0}} (17) | {{lean:NimAudit.Family.pol_net}} (36) |
| Recurrent update | {{lean:NimAudit.Family.ctrl_ac0}} (8) | {{lean:NimAudit.Family.ctrl_net}} (18) |
| Shootout tick | {{lean:NimAudit.Shootout.sh_ac0}} (34) | {{lean:NimAudit.Shootout.sh_net}} (70) |

The certificates assert existence of formulas of the stated depth with total size polynomial in the actual input length
of the component, uniformly over the admissible $(B,N)$; the network certificates use $W=1$.

<!-- explain: par:controller-costs -->
The shootout controller's memory: a working copy of the board, a few control flags, a head index of $r$ bits and the $B$
collected outcomes, $NB+4+r+B$ state bits in all (for $B,N\ge1$, $B\le2^r$). In addition, the original $NB$-bit board is
an input held fixed for the whole decision; it is counted separately, not as state. One circuit handles head selection,
board reload, outcome collection, increment and halting; the table's depth bound covers both schedules.

<!-- formal: par:controller-costs -->
The register layout is {{lean:NimAudit.Shootout.enc}}, and one tick reads $IW=2BN+B+r+5$ input wires
({{lean:NimAudit.Shootout.IW}}): the $NB+4+r+B$ register bits, a reset bit and the $NB$ bits of the original board.
{{lean:NimAudit.Shootout.sh_ac0}} and {{lean:NimAudit.Shootout.sh_net}} certify one tick for either schedule;
{{lean:NimAudit.Shootout.ee_spec}} (early exit) and {{lean:NimAudit.Shootout.ahSel_wins}} (all heads) give the semantics.

<!-- explain: c-controller-evals -->
Time accounting for the all-head schedule. If the rollouts make $M$ simulated legal moves in total, the implementation
uses $M+2B+2$ component evaluations: $M$ move updates, $B$ terminal tests, $B$ outcome-consumption updates, one initial
reset and one final move readout. Since $M\le BN(2^B-1)$, this matches the main text's bound while making control overhead
explicit. The early-exit schedule uses only the heads it visits and gives the same classification as the OR of all
outcomes.

These are counts of circuit evaluations, not processor time, and they certify the two specified schedules, not arbitrary
controller logic.

<!-- formal: c-controller-evals -->
- {{lean:NimAudit.Shootout.ahL_counts}}: on the executed move path, one reset tick plus exactly the total number of
  simulated moves plus $2B$ loop ticks, then one readout.
- {{lean:NimAudit.Shootout.ah_counts}}: the same count ($M+2B+1$ ticks plus one readout) and $M\le BN(2^B-1)$.
- {{lean:NimAudit.Shootout.ee_counts}}: early exit with $R$ heads queried uses $1+\sum_{h<R}L_h+2R$ ticks, with $R=1$ when
  head 0 reports 1.

<!-- explain: x-example-pairing-strategy -->
On boards made of equal pairs, $(a,a,b,b,c,c,\dots)$, the second player can copy every move on the partner heap. The
pairing is restored after each reply, so the second player always has a move and makes the last one.

The checked selector finds the first unequal pair and reduces its larger heap to match its partner; it has constant depth
and polynomial size and uses no nim-sum. For the first-player role every paired board is losing, so weak mastery there
would be vacuous.

<!-- formal: x-example-pairing-strategy -->
- {{lean:NimAudit.Misc.pairing_wins}}: from every paired board ({{lean:NimAudit.Misc.Paired}}) of width $B$, the reply rule
  computed by the local binary mirror circuit wins as second player against every legal opponent.
- {{lean:NimAudit.Misc.pairR_correct}}: after a legal move from a paired board, the mirror circuit outputs the copying
  reply.
- {{lean:NimAudit.Misc.pairBin_bound}}: constant depth (at most 10) and polynomial size.
- {{lean:NimAudit.Mastery.pairing_net_weak}}: the compiled network's strategy is weakly masterful for the second player on
  the paired families, in the general history model.
- {{lean:NimAudit.Mastery.pairing_first_vacuous}}: for the first player the paired family is losing, so weak mastery there
  is vacuous.

<!-- explain: c-weak-vs-strong -->
From the single heap $(3)$, the strategy "take all three stones" wins at once, so it weakly masters $(3)$ as first player,
whatever it would do elsewhere. But it prescribes nothing at $(1)$, and arbitrary legal play can reach $(3)\to(2)\to(1)$
with the first player to move. Strong mastery requires a winning move there, so this strategy is not strongly masterful.
That history is excluded from weak mastery because it contradicts the strategy's own first move.

<!-- formal: c-weak-vs-strong -->
{{lean:NimAudit.Mastery.sep3}} is the strategy "at $(3)$ play $(0)$, otherwise nothing".
{{lean:NimAudit.Mastery.sep3_weak}}: it is weakly masterful for the family $\{(3)\}$ and the first role.
{{lean:NimAudit.Mastery.sep3_not_strong}}: it is not strongly masterful (after the counterfactual $3\to2$ and $2\to1$ it has
no move at the $N$-position $(1)$). {{lean:NimAudit.Mastery.strong_weak}}: strong mastery always implies weak mastery.

<!-- explain: c-noise-model -->
The appendix's setting: an unknown bit $Y$ is observed through a symmetric channel; each observation agrees with $Y$ with
probability $(1+a)/2$, and observations are independent given $Y$. A decision rule (possibly randomised) maps the observed
bits to a guess. $m_*(a)$ is the least number of observations for which some rule has error at most $1/4$ *for each*
value of $Y$.

<!-- formal: c-noise-model -->
{{lean:NimAudit.RealNoise.pOf}} is the agreement probability $(1+a)/2$; {{lean:NimAudit.RealNoise.chan_law}} proves that
the $m$-sample channel law is a probability law; {{lean:NimAudit.RealNoise.Ach}} $a\ m$ says some randomised rule on $m$
samples has both errors at most $1/4$; {{lean:NimAudit.RealNoise.mMin}} is the least such $m$ (by convention $0$ when none
exists). {{lean:NimAudit.RealNoise.mMin_spec}}: for $0<a\le1$ the minimum exists, is attained and is minimal.

<!-- explain: prop:noise-samples -->
**Statement.** For $0<a\le1/2$: $\;3/(32a^2)\le m_*(a)\le\lceil4/a^2\rceil\le17/(4a^2)$, and majority vote with ties
declared $0$ achieves the middle bound.

**Upper bound idea.** The number of correct observations has mean $m(1+a)/2$ and variance at most $m/4$; Chebyshev's
inequality gives majority error at most $1/(ma^2)$, which is at most $1/4$ once $m\ge4/a^2$.

**Lower bound idea.** If $ma^2<3/32$, the two possible observation laws are so close (chi-square divergence below $1$,
hence total variation below $1/2$) that no rule, randomised or not, can have both errors at most $1/4$.

**Example.** $a=0.364$ (from $\varepsilon=0.01$, $L=50$): $\lceil4/a^2\rceil=31$ observations suffice.

<!-- formal: prop:noise-samples -->
- {{lean:NimAudit.RealNoise.majority_succeeds}}: for $0<a\le1$ majority (ties to $0$) has both errors at most $1/4$ for
  every $m\ge\lceil4/a^2\rceil$ ({{lean:NimAudit.RealNoise.mUp}}).
- {{lean:NimAudit.RealNoise.any_rule_needs}}: for $0<a\le1/2$ every randomised rule with both errors at most $1/4$ uses at
  least $3/(32a^2)$ samples.
- {{lean:NimAudit.RealNoise.mMin_spec}}: existence, attainment and minimality of $m_*(a)$.
- {{lean:NimAudit.RealNoise.mMin_bounds}}: $3/(32a^2)\le m_*(a)\le\lceil4/a^2\rceil<4/a^2+1$.
- {{lean:NimAudit.RealNoise.mMin_theta}}: $\tfrac3{32}a^{-2}\le m_*(a)\le\tfrac{17}4a^{-2}$.

All over Mathlib's reals; the adapters showing that the generic field operations are Mathlib's are part of the module.

<!-- explain: c-flip-cases -->
How the flip model of [[rem:noisy-rollout-decay]] fits this setting, and its boundary cases:

- with fresh independent blocks of $L$ flips, the observations follow exactly the channel law above with
  $a=(1-2\varepsilon)^L$;
- for $0<\varepsilon<1/2$ the small-bias condition $a\le1/2$ holds for every $L\ge\lceil1/(2\varepsilon)\rceil$;
- if $\varepsilon=0$ or $L=0$, one observation is exact;
- if $a=0$, no number of observations gets both errors below $1/2$;
- reusing the same corrupted bit adds no information.

<!-- formal: c-flip-cases -->
{{lean:NimAudit.RealNoise.flip_repeated}} (fresh blocks give the product channel law), {{lean:NimAudit.RealNoise.flip_mMin}}
(the sufficient counts in flip space are exactly $m\ge m_*(a)$), {{lean:NimAudit.RealNoise.eventually_small}}
($(1-2\varepsilon)^L\le1/2$ for $L\ge\lceil1/(2\varepsilon)\rceil$, via $(1-x)^L\le1/(1+Lx)$),
{{lean:NimAudit.RealNoise.flip_exact}} ($\varepsilon=0$ or $L=0$: $a=1$ and $m_*=1$),
{{lean:NimAudit.RealNoise.zero_signal_never}} ($a=0$: no $m$ suffices), {{lean:NimAudit.Noise.no_signal}} ($a=0$: every
rule has $\mathrm{err}_0+\mathrm{err}_1=1$, so worst-case error at least $1/2$) and {{lean:NimAudit.RealNoise.reuse_any_rule}}
(with one reused block every rule has total error at least $1-a$).

<!-- explain: app:rollout-proofs -->
The full proof of [[prop:rollout-sufficiency]]: count the rollout moves of $\pi_j$ in two phases (moves of size $2^j$,
then moves of size $1$); read off the parity of each phase from the heaps' bits; recover all bits of $\sigma$ from the $B$
outcomes; choose the first heap with $h_i\oplus\sigma<h_i$ (one exists: a heap with the top bit of $\sigma$); show that
this selector wins against any legal opponent (after the selected move every opponent move makes the nim-sum nonzero,
stones always decrease, and a nonterminal zero-nim-sum position cannot move straight to the end); and bound the total
simulated moves by $BN(2^B-1)$.

<!-- formal: app:rollout-proofs -->
Each step is checked: {{lean:NimAudit.Rollout.run_length}} (move count under any tie-breaking),
{{lean:NimAudit.Rollout.run_parity}} (its parity is the channel bit), {{lean:NimAudit.Game.reconstruct_eq}}
(reconstruction), {{lean:NimAudit.Rollout.exists_decreasing_heap}} (a cancelling heap exists),
{{lean:NimAudit.Game.agent_wins}} (the selector wins against every legal opponent) and
{{lean:NimAudit.Game.totalRolloutMoves_le}} (the step bound).

<!-- explain: app:search-gap-proof -->
The full proof of [[thm:search-gap]] has three parts.

**(i)** With uniform independent heaps, the nim-sum is exactly uniform on $\mathbb F_2^B$. Fix the observed bit $b$: the
readout becomes a fixed shallow circuit proposing a move, which determines a proposed nim-sum $g_b(P)$; the move wins
exactly when $g_\beta(P)=\sigma(P)$. Expand the event $\sigma=a$ into its $2^B$ parity characters; each nonconstant
character is a parity on at least $N$ input bits, so a shallow indicator has tiny correlation with it (the classical
input). Summing the disjoint events and conditioning on $\sigma\ne0$ gives $2/(q-1)+(q-1)\eta_N$. Fixing all coordinates
outside a character's support keeps the circuit shallow, which is how the classical bound for full parity applies.
Guessing one nonzero value per fibre attains the leading constant; for $B=2$ and $\pi_0$ the guesses $a_0=2$, $a_1=1$ win
with probability exactly $2/3$.

**(ii)** and **(iii)** are the multi-head and two-frame constructions.

<!-- formal: app:search-gap-proof -->
- {{lean:NimAudit.Prob.success_bound}}: the finite calculation, including uniformity of $\sigma$, character orthogonality,
  the exact-value expansion, disjointness and conditioning.
- {{lean:NimAudit.CorrBridge.circuit_readout_bound}}: the circuit indicators, restriction to a character's support and
  averaging over fixed coordinates, from the parity-correlation premise.
- {{lean:NimAudit.ClassicalBoundary.search_gap_asymptotic}}: the asymptotic conclusion from the named input `HastadNegl`.
- {{lean:NimAudit.Attain.attain_exact}} and {{lean:NimAudit.Attain.paper_example_two_thirds}}: attainability, and the
  $B=2$ example with success exactly $2/3$ for every $N\ge1$.

Parts (ii) and (iii) are {{claim:thm:search-gap.ii}} and {{claim:thm:search-gap.iii}}.

<!-- explain: eq:finite-correlation-bound -->
The finite form of the single-channel bound: if every readout indicator has correlation at most $\eta_N$ with every
nonconstant character of the nim-sum (under the unconditioned uniform distribution), then a legal winning move is found
with probability at most $2/(q-1)+(q-1)\eta_N$ given $\sigma\ne0$, where $q=2^B$. The premise is a two-sided correlation
bound; it does not assume independence between readout and nim-sum.

<!-- formal: eq:finite-correlation-bound -->
{{lean:NimAudit.Prob.success_bound}}, for every $B\ge1$, $N\ge1$, every readout and every $\eta$, with the premise
{{lean:NimAudit.Prob.CorrHyp}} as a hypothesis of the theorem (not an axiom). The inequality is proved outright from its
stated premise; the premise is supplied for AC⁰ readouts only through the classical input (see
{{claim:thm:search-gap.i}}).

<!-- explain: par:construction-example -->
The input already includes the missing clue: the preceding board had nim-sum zero. Comparing it with the new board
reveals the opponent's change. For $(3,5,6)\to(3,4,6)$ the change is $1$, so the replacements are $(2,5,7)$.
Only heap 0 can be reduced to its proposed value. With three-bit heaps and a two-bit index, the output is
validity $1$, index $00$, value $010$. These are fields, not a single integer.

<!-- formal: par:construction-example -->
An explanatory numerical instance of the checked construction, not a separately added Lean theorem.
{{lean:NimAudit.LocalRestore.dC_eval}} identifies the difference bits;
{{lean:NimAudit.ThresholdInst.restNet_correct}} proves the full network returns a legal move restoring zero under
the preceding-zero and legal-transition hypotheses. The binary interface is {{lean:NimAudit.PriorityEncoder.restBin}}.

<!-- explain: fig:construction-pipeline -->
Read the top row left to right, then the bottom row right to left. The boxes group algorithmic operations, not individual
gates or layers. The candidate tests run in parallel. Additional heaps enlarge the circuit's width; the first-candidate
selection uses a parallel priority encoder rather than a sequential search over heaps.

<!-- formal: fig:construction-pipeline -->
This is a schematic of the checked restoration construction, specialised to the numerical example in
{{claim:par:construction-example}}. It omits the general fallback and terminal branches for readability.
The full statements are available through {{claim:c-candidate-moves}} and {{claim:c-binary-index}}.

<!-- explain: fig:threshold-compilation -->
The compiler turns a Boolean formula into a network with weights and thresholds only 0 or 1. OR uses threshold 1.
AND first checks whether any negated input is true, then negates that answer. Values are copied forward until their
consumers are ready. This uniform schedule permits two layers per Boolean level plus input and output stages.

<!-- formal: fig:threshold-compilation -->
A schematic of {{lean:NimAudit.ThresholdNet.compileF}} and its certificate
{{lean:NimAudit.ThresholdNet.compileF_spec}}. The diagram's boxes are compiler operations, not four neural layers.
The exact network has $2d_{\max}+2$ layers for its actual maximum formula depth;
{{lean:NimAudit.ThresholdNet.compileF_length}} proves this, while a bound $d_{\max}\le d$ yields the stated upper bound.

<!-- explain: par:depth-accounting -->
The number 42 comes from conservative accounting, not a training experiment or a lower bound. Difference extraction
adds at most 4 Boolean levels; the candidate construction has bound 4; the generic selector allows 9 more; binary
index encoding allows 3 more. The total bound 20 is converted to $2\cdot20+2=42$ threshold layers. The generic
compiler pads dependencies and reserves the two-layer cost of AND at every Boolean level. A specialised network
may be smaller, but a sharper claim requires a new construction and proof.

<!-- formal: par:depth-accounting -->
The compositional bounds are {{lean:NimAudit.LocalRestore.restC_bound}} (depth $4+9+4$),
{{lean:NimAudit.PriorityEncoder.restBin_bound}} (depth $4+9+4+3$), and
{{lean:NimAudit.ThresholdInst.restNet_res}} (at most $2\cdot20+2$ layers).
The general conversion is {{lean:NimAudit.ThresholdNet.compileF_spec}}.
These existing theorems bound this construction; they do not prove depth optimality or learnability.
