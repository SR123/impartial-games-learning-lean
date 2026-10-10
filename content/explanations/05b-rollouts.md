<!-- Section 5.4: structured rollout policies, the single-channel bound, the shootout controller. -->

<!-- explain: c-search-intro -->
The single-frame barrier rules out computing the needed invariant in one shallow pass. The natural next question
is whether *planning* (simulating play) can make up for it. This subsection studies a deliberately simple
planning interface to answer that question precisely.

<!-- formal: c-search-intro -->
A restatement of {{claim:thm:singleframe-impossible.b}}, whose precise content is winning-move selection on the
encoded family; the paper's phrase "evaluate the nim-sum" is the informal reading of that result.

<!-- explain: def:rollout-policy -->
A rollout policy is a deterministic rule that, given a board, names one legal move. A *rollout* lets both players
follow that same rule from a start position until the board is empty; the only thing reported back is one bit:
did the first player win (make the last move)?

Example: the policy $\pi_0$ "subtract 1 from the leftmost nonzero heap" played from $(2,1)$ goes
$(2,1)\to(1,1)\to(0,1)\to(0,0)$: three moves, so the first player wins and the outcome bit is $1$.

Why only one bit: this isolates how much information repeated simulation can expose, without letting the interface
pass whole trajectories or move counts to the planner.

<!-- formal: def:rollout-policy -->
Lean formalises the structured policies $\pi_j$ that the results use. A legal $\pi_j$ step
({{lean:NimAudit.Rollout.PolicyMove}}) subtracts $2^j$ from some heap of size at least $2^j$, or, when every heap is
below $2^j$, subtracts $1$ from some nonzero heap; the tie-breaking rule is left arbitrary.
{{lean:NimAudit.Rollout.policyStep}} is the concrete first-eligible-heap version, and
{{lean:NimAudit.Game.rolloutWinner}} executes the rollout and returns whether the first player made the last move.
{{lean:NimAudit.Prob.rollout_outcome_linear}} proves that this executed outcome equals the linear functional
$\langle w_j,\sigma(P)\rangle$ of the nim-sum.

The general notion of an arbitrary AC⁰-bounded rollout policy is not a separate Lean object; no result depends on
it.

<!-- explain: def:agent-types -->
This definition fixes exactly what the single-channel lower bound allows.

- **Queries.** Start a rollout at the root board $P$, or at a board obtained by changing one heap of $P$ (for
  example a candidate successor). Rollouts from arbitrary transformed boards are not allowed.
- **One channel.** The policy is one fixed member $\pi_j$ of the structured family, chosen independently of $P$.
- **Bounded readout.** The final move must be computed by a polynomial-size, constant-depth circuit from $P$ and the
  observed bit $\beta$. Any value head, correction of queries or other processing counts towards that readout.

The multi-channel construction may query several members of the family and then apply such a readout. A "policy
head" means a rollout policy, not a parallel output neuron.

<!-- formal: def:agent-types -->
The interface appears in Lean through its consequences rather than as a single definition.

- One-heap queries: {{lean:NimAudit.Prob.single_policy_affine}} and
  {{lean:NimAudit.Misc.single_policy_correction}} show that a rollout from a board with one heap changed from $h$ to
  $h'$ returns the root outcome XOR a correction bit computable from $h\oplus h'$, so such queries add no new
  unknown bit.
- Why arbitrary starts are excluded: {{lean:NimAudit.Misc.bitBoard_query}} (next record).
- The readout bound: {{lean:NimAudit.BinReadout.BBound}} specifies binary readout formulas of depth at most $d$ and
  size at most $s$; the conditional theorem quantifies over all such readouts. The correlation premise for their
  indicators is {{lean:NimAudit.Prob.CorrHyp}}.

<!-- explain: c-arbitrary-starts -->
If the planner could start rollouts anywhere, the restriction would be meaningless. Example: build the board whose
heaps are the $k$-th bits of the heaps of $P$ (each heap becomes $0$ or $1$). A rollout of $\pi_0$ on it removes one
stone per move, so the outcome is the parity of the number of ones, which is bit $k$ of the nim-sum of $P$. Doing
this for each $k$ recovers the whole nim-sum with one policy. So the lower bound must restrict queries.

<!-- formal: c-arbitrary-starts -->
{{lean:NimAudit.Misc.bitBoard_query}}: one rollout of $\pi_0$ on the board of $k$-th bits of $P$ returns
$\sigma_k(P)$; {{lean:NimAudit.Misc.nimSum_bitBoard}} is the underlying identity (the low bit of that board's nim-sum
is bit $k$ of $\operatorname{nim}(P)$).

<!-- explain: rem:why-multi-head -->
Could one big circuit simply contain all $B$ policies? At the circuit level, yes: AC⁰ is closed under parallel
composition. The point is the *rollout interface*: one rollout follows one deterministic rule from start to end and
returns one bit. Merging circuits does not change that one trajectory yields one bit.

Several heads help because separate rollouts under different policies follow different trajectories, and their
outcome bits are *linearly independent* functions of the nim-sum: $\pi_0$ gives $\sigma_0$; $\pi_j$ gives
$\sigma_j\oplus\sigma_0$. Together they determine $\sigma$.

<!-- formal: rem:why-multi-head -->
- {{lean:NimAudit.Game.rolloutWinner_channel}}: the executed outcome of $\pi_j$ is the channel value
  {{lean:NimAudit.channel}} $j$ of the nim-sum: bit $0$ for $j=0$, bit $j$ XOR bit $0$ for $j\ge1$.
- {{lean:NimAudit.Prob.rollout_outcome_linear}}: the same as an inner product $\langle w_j,\sigma\rangle$ over
  $\mathbb F_2$ ($w_0=1$, $w_j=2^j\oplus1$).
- {{lean:NimAudit.Game.reconstruct_eq}}: the $B$ outcomes determine the full nim-sum on every $B$-bit board, which is
  the checked form of their independence.

<!-- explain: par:shootout-controller -->
The multi-channel classifier only needs to know whether *some* channel bit is $1$ (that is, whether
$\sigma\ne0$). So it may stop as soon as one rollout returns $1$. This early exit saves rollouts but leaves the
decision rule unchanged: it is still the OR of all channel bits.

Caveat: early stopping is a scheduling optimisation for classification. It does not give the single-channel
readout extra power, and it is not enough for move selection (see [[par:shootout-controller|the next paragraphs]]).

<!-- formal: par:shootout-controller -->
- {{lean:NimAudit.Misc.shootout_spec}}: started at head $0$ with fuel $B+1$, the depicted controller outputs the OR of
  the $B$ outcome bits, using at most $B$ queries, and exactly one query when head $0$ reports $1$.
- {{lean:NimAudit.Misc.channels_or}}: with the exact structured heads, the OR of the channel bits is
  "$\operatorname{nim}(P)\ne0$".
- {{lean:NimAudit.Shootout.ee_spec}}: the bit-level outer controller with the early-exit schedule stops after exactly
  the predicted number of ticks with decision $[\operatorname{nim}(P)\ne0]$, matching the abstract controller.

<!-- explain: c-fsm-definition -->
A finite-state shootout controller is a small automaton that sits outside the policy heads. In each state it names
a head to query; after seeing that rollout's outcome bit it moves to a new state; some states halt with a decision.
It sees nothing but outcome bits.

<!-- formal: c-fsm-definition -->
{{lean:NimAudit.Misc.FSM}} is a structure with an initial state, a head-selection map, a transition map on
(state, outcome bit) and an output for halting states; {{lean:NimAudit.Misc.FSM.run}} runs it with fuel against an
abstract outcome function `o : ℕ → Bool` and returns the decision and the number of queries. In the executed controller
({{claim:c-outer-controller}}) each outcome is obtained by actually running the rollout. {{lean:NimAudit.Misc.shootout}} is the controller
of [[fig:fsm-shootout-controller]].

<!-- explain: c-fsm-power -->
The controller does not make any single head more powerful: each head is still a shallow policy. What it adds is
organisation: which head to run next and when to stop. That is what turns separate channels into a practical
procedure.

<!-- formal: c-fsm-power -->
An interpretive paragraph. The precise statements about the controller are {{claim:par:shootout-controller}} and
{{claim:c-outer-controller}}.

<!-- explain: c-outer-controller -->
The checked implementation is a complete machine, not just the abstract automaton. In each tick it does exactly
one of: reset (load the board, select head $0$); one move of the selected head's rollout; a terminal test that finds
the current rollout finished; or consume a finished rollout (store its outcome, then stop or reload the original board
for the next head).

Two schedules are distinguished:

- **early exit** for classification: stop at the first outcome $1$;
- **all heads** for move selection: run every head, because choosing the move needs every invariant bit, not just
  "is it nonzero".

The original board is a read-only input during the whole decision. It is *not* an oracle for the nim-sum: the
nim-sum is only obtained by executing the rollouts.

<!-- formal: c-outer-controller -->
- {{lean:NimAudit.Shootout.ee_spec}} and {{lean:NimAudit.Shootout.ee_net}}: the early-exit classifier, semantically and
  as a threshold network, decides $[\operatorname{nim}(P)\ne0]$.
- {{lean:NimAudit.Shootout.ahSel_wins}}: the all-head controller plus readout wins from every nonzero position
  against every legal opponent.
- {{lean:NimAudit.Shootout.ahL_counts}}: the executed all-head path uses one reset tick, exactly the total number of
  simulated legal moves, and $2B$ further ticks, then one readout.
- {{lean:NimAudit.Shootout.sh_ac0}} and {{lean:NimAudit.Shootout.sh_net}}: one tick (either schedule) is an AC⁰ formula
  family of depth at most 34, and a $\{0,1\}$-weight threshold network family with at most 70 layers.

These are statements about one tick; the number of ticks grows with the board (see {{claim:c-controller-evals}}).

<!-- explain: fig:fsm-shootout-controller -->
The figure shows the early-exit controller: query $\pi_0$; if it returns $1$, declare "$\sigma\ne0$" ($N$-position);
otherwise query $\pi_1$, and so on. If all $B$ heads return $0$, declare "$\sigma=0$" ($P$-position). Because the
channel bits are linearly independent functions of $\sigma$, they are all zero exactly when $\sigma=0$.

<!-- formal: fig:fsm-shootout-controller -->
{{lean:NimAudit.Misc.shootout_spec}} (OR of the outcomes, at most $B$ queries) and
{{lean:NimAudit.Misc.shootout_decides}} (with the exact structured heads the decision is
$[\operatorname{nim}(P)\ne0]$, for every $B$-bit board).

<!-- explain: c-integration -->
A useful way to read Theorem 5.12(ii): each head is a *measurement channel* returning one bit that depends on the
hidden invariant. One head, queried repeatedly at the root, returns the same bit each time; one-heap modifications
return known corrections of it. Several heads give independent measurements. The controller is the *protocol* that
decides which channel to query next and when to stop.

<!-- formal: c-integration -->
An interpretive paragraph. Its formal content is {{claim:prop:single-policy-bound}} (one channel, affine
corrections) and {{claim:prop:rollout-sufficiency}} (all channels reconstruct $\sigma$).

<!-- explain: c-depth-amplification -->
A single shallow circuit cannot compute parity, but running a shallow policy for $L$ game steps is a computation of
depth proportional to $L$. That is how rollouts can reveal parity information: the depth comes from time.

Caveat: depth by itself does not prove anything. That the complete rollout procedure is not an AC⁰ family is a
separate, conditional result ({{claim:c-bypass-not-ac0}}), even though each step is shallow.

<!-- formal: c-depth-amplification -->
An interpretive remark. The checked counterparts are {{claim:prop:rollout-sufficiency}} (rollouts reveal all bits)
and {{claim:c-bypass-not-ac0}} (conditional on the classical parity bound, the complete multi-head decision map is not
an AC⁰ family).

<!-- explain: prop:rollout-sufficiency -->
**The policies.** For each bit position $j$, policy $\pi_j$ repeatedly subtracts $2^j$ from the leftmost heap of size
at least $2^j$; once all heaps are smaller than $2^j$ it subtracts $1$ from the leftmost nonzero heap.

**Why the outcome reveals a bit.** The rollout length is $\sum_i\lfloor h_i/2^j\rfloor + \sum_i (h_i \bmod 2^j)$. Its
parity is $\sigma_j\oplus\sigma_0$ for $j\ge1$ (and $\sigma_0$ for $j=0$). The first player wins exactly when the
length is odd.

**Example.** $P=(3,5)$, $\sigma=3\oplus5=6=110_2$. $\pi_0$ plays $3+5=8$ moves: even, outcome $0=\sigma_0$. $\pi_1$
plays $\lfloor3/2\rfloor+\lfloor5/2\rfloor=3$ moves of size $2$, then $1+1=2$ moves of size $1$: $5$ moves, outcome
$1=\sigma_1\oplus\sigma_0$. $\pi_2$ plays $0+1$ moves of size $4$ and $3+1$ moves of size $1$: $5$ moves, outcome
$1=\sigma_2\oplus\sigma_0$. So $\sigma=110_2$.

**The move.** With $\sigma\ne0$, take the first heap with $h_i\oplus\sigma<h_i$ and replace it by $h_i\oplus\sigma$.

**Costs.** $B$ rollouts, at most $BN(2^B-1)$ simulated moves in total. That is polynomial in $N$ only when $B=O(\log N)$.

<!-- formal: prop:rollout-sufficiency -->
- {{lean:NimAudit.Rollout.run_length}}: every complete run of $\pi_j$, under *any* tie-breaking rule, has exactly the
  length above.
- {{lean:NimAudit.Game.rolloutWinner_channel}}: the executed outcome is $\sigma_0$ or $\sigma_j\oplus\sigma_0$.
- {{lean:NimAudit.Game.agent_wins}}: the agent that runs the $B$ rollouts, reconstructs $\sigma$
  ({{lean:NimAudit.Game.reconstruct}}) and plays the selected move wins from every nonzero position against every
  legal opponent.
- {{lean:NimAudit.RolloutExec.mhExec_wins}}: the same for the fully executed version, in which each rollout runs on a
  finite register machine with one shallow step circuit per simulated move; no outcome bit is supplied for free.
- {{lean:NimAudit.RolloutExec.mhExec_evals}}: rollout $j$ makes $L_j+1$ policy evaluations; in total the number of
  simulated moves plus $B$, at most $B(N(2^B-1)+1)$.
- {{lean:NimAudit.Game.totalRolloutMoves_le}}: total simulated moves at most $BN(2^B-1)$.
- {{lean:NimAudit.Mastery.mh_strong}}: the network-driven multi-head player is strongly masterful (in the sense of
  [[def:mastery]]) on $B$-bit boards, for both roles.

The statement's "polynomial circuit size" for each policy update and the readout is certified separately
({{claim:c-depth-table}}).

<!-- explain: prop:single-policy-bound -->
With a single fixed head, every allowed query returns the same unknown bit up to a known correction. At the root, the
outcome is $\ell_j(\sigma)$. If one heap changes from $h$ to $h'$ (for example when evaluating a candidate move), the
nim-sum changes by $h\oplus h'$, and by linearity the outcome becomes $\ell_j(\sigma)\oplus\ell_j(h\oplus h')$, where
the correction is computable from the known heap values.

So one channel yields one unknown bit of the $B$-bit invariant, however often it is queried in this way.

Caveat: this concerns one member of the structured family, not arbitrary rollout policies.

<!-- formal: prop:single-policy-bound -->
- {{lean:NimAudit.Prob.rollout_outcome_linear}}: the executed outcome of $\pi_j$ equals $\langle w_j,\sigma(P)\rangle$.
- {{lean:NimAudit.Prob.single_policy_affine}}: if $P'$ differs from $P$ in one heap $h\to h'$, then
  $\mathrm{RO}_{\pi_j}(P') = \mathrm{RO}_{\pi_j}(P)\oplus\langle w_j, h\oplus h'\rangle$.
- {{lean:NimAudit.Misc.single_policy_correction}}: the same with the channel function.

<!-- explain: rem:noisy-rollout-decay -->
**The model.** Suppose the ideal outcome bit $Y$ reaches us flipped by $L$ independent coin flips, each with
probability $\varepsilon<1/2$. The observed bit agrees with $Y$ with probability $(1+a)/2$ where
$a=(1-2\varepsilon)^L$: each flip multiplies the bias by $1-2\varepsilon$.

**Example.** $\varepsilon=0.01$, $L=50$: $a\approx0.364$ and agreement $\approx0.682$, far from a fair coin.

**Repetitions.** With *fresh* independent flips each time (and $0\le\varepsilon<1/2$), about $1/a^2$ observations
are needed to decide $Y$ with error at most $1/4$ for *each* value of $Y$. When $0<a\le1/2$, every (possibly randomised)
decision rule needs at least $3/(32a^2)$ observations, while majority vote achieves the target with at most $17/(4a^2)$.
These bounds therefore enclose the *minimum* sufficient sample count. In the example, 31 fresh repetitions with majority vote
(ties declared $0$) suffice.

**Caveats.**

- Repeating the same corrupted observation (same randomness) gives no new information.
- Correlated flips can cancel in pairs, so the decay is not automatic.
- This models noise on the outcome channel, not erroneous game moves: a wrong move need not flip the outcome and can
  change everything that follows. Exact structured rollouts have no noise at all.

<!-- formal: rem:noisy-rollout-decay -->
All statements are checked over Mathlib's real numbers.

- The flip law: {{lean:NimAudit.RealNoise.flip_law}} (product Bernoulli$(\varepsilon)$ law on $\{0,1\}^L$: nonnegative,
  total mass $1$, marginals $\varepsilon$) and {{lean:NimAudit.RealNoise.flip_agree_real}} (agreement
  $(1+(1-2\varepsilon)^L)/2$).
- Fresh repetitions: {{lean:NimAudit.RealNoise.flip_repeated}} (with fresh blocks the $m$ observations have the product
  channel law) and {{lean:NimAudit.RealNoise.flip_mMin}} (for $0\le\varepsilon<1/2$ exactly the counts
  $m\ge m_*(a)$ suffice).
- Growth: {{lean:NimAudit.RealNoise.mMin_theta}}: $\tfrac{3}{32}a^{-2}\le m_*(a)\le\tfrac{17}{4}a^{-2}$ for
  $0<a\le1/2$. The lower bound applies to every randomised decision rule; majority vote establishes the upper bound.
- Reuse: {{lean:NimAudit.RealNoise.reuse_any_rule}}: with one reused error block, every rule has total error at least
  $1-a$.
- Numbers: {{lean:NimAudit.Misc.flip_example}} ($0.682\le$ agreement $\le0.6822$) and
  {{lean:NimAudit.RealNoise.remark_real}} ($0.364\le a\le0.3644$, $\lceil4/a^2\rceil=31$; optimality of 31 is not
  claimed).
- Correlated flips: {{lean:NimAudit.Misc.paired_flips_cancel}}.

The precise sample-count statement is {{claim:prop:noise-samples}}.

<!-- explain: c-init-boundary -->
Matching the last difference only says $\operatorname{nim}(R)=\operatorname{nim}(Q)$. If $Q$ did not have nim-sum zero,
neither does $R$. So restoration cannot, by itself, tell whether an arbitrary starting position is winning.

**Counterexample.** Complete a matching-delta policy by "subtract one from the first nonempty heap" whenever no
matching reply exists or no previous frame is available. From $(2)$, a winning position, the first player plays
$(2)\to(1)$ (no previous frame). The opponent's reply from $(1)$ is computed by the same policy: the difference to
match is $2\oplus1=3$, which cannot be realised from $(1)$, so it falls back and plays $(1)\to(0)$. The first player
has lost from a winning position.

What it shows: conditional restoration plus an unspecified fallback is not a verifier. It does not rule out every
possible verifier. Initial moves can come from the multi-channel construction or the recurrent scan instead.

<!-- formal: c-init-boundary -->
- {{lean:NimAudit.Misc.init_counterexample}} checks the counterexample step by step: $(2)$ is winning; the completed
  policy {{lean:NimAudit.Misc.mdPolicy}} plays $(2)\to(1)$; no move from $(1)$ cancels $2\oplus1$; the fallback plays
  $(1)\to(0)$; $(1)$ is winning and $(0)$ is losing.
- {{lean:NimAudit.Rollout.matching_deltas_do_not_force_zero}}: the universal statement "matching deltas forces nim-sum
  zero" is false without the zero promise; {{lean:NimAudit.no_zero_without_zero_promise}} is the concrete instance
  $1\oplus3=3\oplus1$ with $1\ne0$.

<!-- explain: fig:rollout_gap -->
The table compares what each bypass keeps shallow and what it adds:

- one structured channel: a shallow step and readout, but one complete rollout gives only one invariant bit;
- $B$ channels: still shallow steps, but $B$ complete rollouts supply all bits;
- two frames: shallow difference and selection, given a previous zero-nim-sum board and a legal transition;
- persistent row scan: one shallow update, but two scans per decision and $O(B+\log N)$ state bits.

<!-- formal: fig:rollout_gap -->
A summary table. Its entries are covered by {{claim:prop:single-policy-bound}}, {{claim:prop:rollout-sufficiency}},
{{claim:c-restore-selector}}, {{claim:c-replay}} and {{claim:prop:bypass-interfaces}}.

<!-- explain: thm:search-gap.i -->
**The setting.** Boards are uniformly random $N$-heap boards with $B$-bit heaps, conditioned on being winning
($\sigma\ne0$). The agent observes one structured channel $\beta=\mathrm{RO}_{\pi_j}(P)$ and must output a move with a
shallow circuit $F_N(P,\beta)$.

**The bound.** Its chance of playing a winning move is at most $2/(2^B-1)$ plus a quantity that vanishes faster than
any inverse polynomial in $N$. For $B=2$ that is about $2/3$; for $B=4$ about $0.13$.

**Intuition.** Knowing one linear bit $\ell(\sigma)$ narrows the $2^B-1$ possible nonzero nim-sums to a fibre of about
half of them. A shallow readout has essentially no correlation with the remaining parity information, so the best
it can do is guess one value per fibre: two lucky values out of $2^B-1$.

**Attainability.** Guessing one nonzero value in each fibre achieves $2/(2^B-1)$ exactly, so the constant is right.

**Caveats.** Fixed $B$; this distribution; this interface. The negligible term rests on Håstad's parity-correlation
bound, used as the named external input `HastadNegl`. It is not a bound on general single-policy search or on MCTS.

<!-- formal: thm:search-gap.i -->
**Finite part, no classical input.** {{lean:NimAudit.Prob.success_bound}}: for every readout and every $\eta$, the
correlation premise {{lean:NimAudit.Prob.CorrHyp}} ($|\mathbb E[H_{b,a}\chi_u]|\le\eta$ for all observed bits $b$,
values $a$ and nonzero $u$) implies conditional success at most $2/(q-1)+(q-1)\eta$, $q=2^B$.

**From circuits to the premise.** {{lean:NimAudit.CorrBridge.circuit_readout_bound}}: for readouts given by formulas
of depth $d$ and size $s$, the premise follows from the parity-correlation premise for formulas of depth $d+11$ and
polynomially larger size on every support size between $N+1$ and $B(N+1)$, where Lean indexes boards by $N+1$ heaps
(so this is $N$ to $BN$ in the paper's notation); restriction and averaging are checked.

**Asymptotic part, named classical input.** {{lean:NimAudit.ClassicalBoundary.search_gap_asymptotic}}: assuming
{{lean:NimAudit.ClassicalBoundary.HastadNegl}}, for fixed $B\ge2$, $j<B$ and readout families of fixed depth and
polynomial size there is a negligible $\eta$ ({{lean:NimAudit.ClassicalBoundary.Negligible}}) with success at most
$2/(2^B-1)+\eta(N)$. {{lean:NimAudit.ClassicalBoundary.search_gap_asymptotic_net}} is the same for fixed-scale network
readouts.

**Attainability.** {{lean:NimAudit.Attain.attain_exact}}: for $B\ge2$ and any nonzero functional, the
least-representative readout succeeds with conditional probability exactly $2/(2^B-1)$, for every $N\ge1$.

**Boundary.** The analytic derivation of Håstad's correlation bound is external. Everything that applies it to this
paper (indicators, restrictions, conditioning, the probability calculation) is checked.

<!-- explain: thm:search-gap.ii -->
With all $B$ structured heads, the rollout outcomes reconstruct the nim-sum exactly and a shallow readout plays an
optimal move. The cost is the rollouts themselves: $O(BN2^B)$ simulated moves per decision.

<!-- formal: thm:search-gap.ii -->
{{lean:NimAudit.Game.agent_wins}} and {{lean:NimAudit.RolloutExec.mhExec_wins}} (winning against every legal opponent
from every nonzero position, the second with fully executed rollouts) and
{{lean:NimAudit.Game.totalRolloutMoves_le}} (at most $BN(2^B-1)$ simulated moves). Details in
{{claim:prop:rollout-sufficiency}}.

<!-- explain: thm:search-gap.iii -->
Given a legal opponent move from a known zero-nim-sum board, a shallow two-frame selector restores nim-sum zero. A
player who keeps doing this after each opponent move maintains the invariant and wins. This part does not supply the
first winning move from an arbitrary position.

<!-- formal: thm:search-gap.iii -->
{{lean:NimAudit.Game.restore_correct}} (the restoration selector returns a legal move to nim-sum zero under the
promise), {{lean:NimAudit.LocalRestore.restore_equiv}} (the same move from the local circuit) and
{{lean:NimAudit.WholeGame.twoFrame_wins}} (the stateful whole-game guarantee). See {{claim:c-restore-selector}}.
