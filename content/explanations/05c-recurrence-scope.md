<!-- Sections 5.5-5.6: persistent recurrence and what the bypasses establish; Section 10: verification. -->

<!-- explain: c-stream -->
**The input protocol.** Positions are fed one row (heap) at a time, in a fixed heap order. After all rows of each position comes a
separator token `SEP`. Rows for empty heaps are still sent, so heap $i$ is always the $i$-th row.

**What the separator does.** It marks a complete position. It resets the *accumulator* for the next scan but keeps
selected information about the finished position (its summary). It does not wipe the whole memory.

**Example.** Positions $(3,5,6)$ then $(3,4,6)$ become the stream $3,5,6,\mathtt{SEP},3,4,6,\mathtt{SEP}$.

<!-- formal: c-stream -->
{{lean:NimAudit.Recurrent.serialize}} turns a list of positions into rows followed by `SEP`;
{{lean:NimAudit.Recurrent.step}} is one recurrent update. {{lean:NimAudit.Recurrent.sep_resets}}: after `SEP` the
accumulator is $0$, the summary is retained and the validity bit is set; rows never change the summary.
{{lean:NimAudit.Recurrent.fold_invariant}} describes the outputs for any finite sequence of positions, including the
first position and empty positions (consecutive separators).

<!-- explain: prop:streaming-nimsum -->
**The update.** Keep a $B$-bit accumulator $s$. For each row $x$: $s\leftarrow s\oplus x$. After $N$ rows, $s$ is the
nim-sum of the position. Each update XORs two $B$-bit numbers bit by bit, a constant-depth operation.

**Remembering the previous position.** Keep a second register $q$ and a validity bit $v$. At a separator: output $s$
(and $q\oplus s$ if $v=1$), then set $q\leftarrow s$, $s\leftarrow0$, $v\leftarrow1$. So the machine also reports
the difference between consecutive positions' nim-sums.

**Example.** For $3,5,6,\mathtt{SEP},3,4,6,\mathtt{SEP}$: $s$ goes $3, 6, 0$; at the first `SEP` it outputs $0$;
then $s$ goes $3,7,1$; at the second `SEP` it outputs $1$ and the difference $0\oplus1=1$.

**Why it matters.** The update is shallow; the computation as a whole takes $N$ updates. The bypass works by
letting the *number* of updates grow, which the simulation theorem forbids for fixed-latency models.

<!-- formal: prop:streaming-nimsum -->
- {{lean:NimAudit.Recurrent.fold_invariant}}: from any state with empty accumulator, for any finite sequence of
  positions, the $t$-th output is $(\sigma(P_t), \Delta)$ with $\Delta=\sigma(P_{t-1})\oplus\sigma(P_t)$ for $t\ge2$
  (and determined by the starting state for $t=1$).
- {{lean:NimAudit.Recurrent.stream_reports_delta}}: from the initial state the first output has no difference and the
  second reports $\operatorname{nim}(Q)\oplus\operatorname{nim}(Q')$.
- {{lean:NimAudit.Recurrent.circuit_update}} and {{lean:NimAudit.Recurrent.circuit_step_correct}}: $2B+1$ state bits
  suffice and explicit per-bit circuits compute the update.
- {{lean:NimAudit.Recurrent.circuit_resources}}: depth at most $4$, total size at most $28B+8$.
- {{lean:NimAudit.Recurrent.xorNet_correct}}: a fixed-scale threshold realisation of one XOR bit update.

<!-- explain: c-replay -->
A nim-sum alone does not say which heap to change: the rows have already gone by. The replay protocol sends the
current board **twice**: `rows(P), SEP, rows(P), SEP`.

- First scan: compute $\sigma=\operatorname{nim}(P)$; at the first `SEP` store it and switch to replay mode.
- Replay: for each row $i$, test whether $x_i\oplus\sigma<x_i$, keeping the first such row and a fallback
  (first nonempty heap).
- Second `SEP`: emit the move (cancel at the first qualifying row; else decrement the first nonempty heap; or report
  termination) and return to scan mode.

**Costs.** Exactly $2N+2$ updates per decision, plus one reset at the start of a game. With an $r$-bit counter,
$N<2^r$, the state has $4+5B+3r$ bits.

**Caveat.** The second copy of the board is supplied by the environment as part of the input protocol; the
controller does not secretly store the board.

<!-- formal: c-replay -->
- {{lean:NimAudit.Recurrent.replay_correct}}: with $\sigma$ from the first scan, the replay move is absent iff the board
  is terminal, every move is legal, and if $\sigma\ne0$ the move reaches nim-sum zero.
- {{lean:NimAudit.Controller.crun_decision}}: from an idle state, one decision emits the summary and then the move
  computed from the *stored* summary, and returns to an idle state.
- {{lean:NimAudit.Controller.ctrl_wins}}: the controller's decisions win from every nonzero board against every legal
  opponent.
- {{lean:NimAudit.Controller.stream_fits}}: along any well-formed stream every register fits its field; the counter
  never overflows (with $N<2^r$).
- {{lean:NimAudit.ThresholdInst.ctrl_counts}}: with $r=\lfloor\log_2N\rfloor+1$ (so $N<2^r$) the state has
  $7+5B+3\lfloor\log_2N\rfloor$ bits, which is the general width $4+5B+3r$ of
  {{lean:NimAudit.ControllerBits.stateWidth}}; each decision uses $2N+2$ updates.
- {{lean:NimAudit.WholeGame.replay_wins}} and {{lean:NimAudit.WholeGame.replay_game}}: the compiled threshold
  controller, driven by the protocol, wins from every nonzero position; one reset token starts a game from an
  arbitrary bit state.

<!-- explain: c-board-storage -->
The alternative stores the board while scanning it once: each row is written into an $NB$-bit board register as it
arrives, and at the separator a constant-depth selector picks the move from the stored board and the accumulated
nim-sum.

**Trade-off.** $N+1$ updates per decision instead of $2N+2$, and no replay, but $NB+B+r$ state bits instead of
$O(B+\log N)$. This matters for streams where each position is supplied only once.

<!-- formal: c-board-storage -->
- {{lean:NimAudit.BoardStore.bs_decision}} and {{lean:NimAudit.BoardStore.bits_decision}}: one decision `rows(P), SEP`
  stores $P$ and emits the summary and the move, semantically and at bit level.
- {{lean:NimAudit.BoardStore.bits_store_wins}}: with $N<2^r$, the one-pass bit-level machine wins from every nonzero
  board against every legal opponent.
- {{lean:NimAudit.BoardStore.bs_counts}}: $BN+B+r$ state bits and $N+1$ updates per decision.
- {{lean:NimAudit.BoardStore.bs_ac0}} and {{lean:NimAudit.BoardStore.bs_net}}: the update and output formulas have
  depth at most $16$ and polynomial size; as a $\{0,1\}$-weight network, at most $34$ layers.

<!-- explain: c-recurrence-history -->
**Connecting to the two-frame idea.** The retained summaries give $\sigma_{t-1}\oplus\sigma_t=\Delta(P_{t-1},P_t)$
for consecutive *supplied* boards. If one heap changed from $a$ to $b$, this is $a\oplus b$.

**Which boards are consecutive matters.** If the controller sees only the boards at the player's decision times,
consecutive boards are two moves apart (the player's own move and the opponent's), and the difference mixes both. To
isolate the opponent's move, the player's own post-move board must be supplied as the preceding frame.

**Initialisation.** The first scan computes the invariant from an arbitrary starting position, with no earlier
zero-nim-sum frame. That uses the growing recurrent horizon, an extra resource beyond the fixed-latency two-frame
construction.

<!-- formal: c-recurrence-history -->
- {{lean:NimAudit.Bypass.diff_of_transition}}: when consecutive supplied boards differ by one legal move, the
  threshold controller reports exactly that heap's XOR difference.
- {{lean:NimAudit.Bypass.diff_with_postMove}}: if the player's own post-move board $R$ (nim-sum zero) is supplied
  before the opponent's board $P'$, the reported difference is the opponent's delta, which equals
  $\operatorname{nim}(P')$, the restoration target.
- {{lean:NimAudit.Bypass.diff_decision_only}}: a concrete counterexample with decision-time boards only:
  $(1,2)\to(1,1)\to(0,1)$; supplying only $(1,2)$ and $(0,1)$, the controller reports difference $2$, while the
  opponent's delta was $1$.
- {{lean:NimAudit.Recurrent.stream_reports_delta}}: the summary-level statement.

<!-- explain: c-lower-bound-respected -->
**No contradiction with the lower bound.** $N$ shallow updates in sequence form a computation of depth about $N$,
which is outside the fixed-$T$ premise of [[thm:sim-ac0]]. A one-step dependency can still carry information
accumulated over the whole stream.

**Separators are not the bypass.** Merely writing positions and separators into the input of a fixed-depth network
adds nothing. The bypass is the sequential computation with retained state.

**Scope.** For larger heaps the accumulator needs $B$ bits; a fixed-width state is not claimed to store arbitrary
invariants. And the construction says nothing about whether training discovers the update; no recurrent training
experiments are reported.

<!-- formal: c-lower-bound-respected -->
{{lean:NimAudit.Barrier.no_ac0_rec}}: under {{lean:NimAudit.Barrier.ParityNotAC0}}, the complete recurrent decision map
{{lean:NimAudit.Barrier.recMove}} ($2N+2$ threshold-controller updates from the initial state) is not computed by any
single-frame AC⁰ formula family, even on the encoded boards. {{lean:NimAudit.Bypass.bypass_barriers}} collects this
together with the network form and the multi-head case. `ParityNotAC0` is derived from the named input `HastadNegl`.
The remarks about fixed-width states and training are informal.

<!-- explain: prop:bypass-interfaces -->
**What it says.** For each bypass, the shallow pieces are genuinely shallow (polynomial size, constant depth,
realisable with weights and thresholds in $\{0,1\}$), and running them as prescribed gives a strategy that wins
against every legal opponent:

1. **Two frames**: the selector maps a legal transition from a zero-nim-sum board to a restoring reply; keeping the
   reply as the next predecessor wins from the established invariant.
2. **Rollouts**: each policy step and the final readout are shallow; executing the rollouts, then the readout, wins
   from any nonzero board with at most $BN(2^B-1)$ simulated moves per decision.
3. **Recurrence**: the state update is shallow; iterating it over the replay protocol wins from any nonzero board
   with $O(B+\log N)$ memory and $2N+2$ updates per decision.

**The fine print.** "Polynomial size and constant depth" refer to one component evaluation, with depth independent
of $N$ and $B$. They do not bound how many evaluations happen in sequence.

<!-- formal: prop:bypass-interfaces -->
{{lean:NimAudit.Bypass.prop_bypass_interfaces}} states all three parts at once. For each bypass it gives an AC⁰ family
certificate ({{lean:NimAudit.Family.AC0Fam}}) and a $\{0,1\}$-weight network family certificate
({{lean:NimAudit.Family.NetFam}}) for the shallow components, with explicit depth and layer bounds, together with the
complete strategy:

- (i) two frames: formulas of depth at most 20, networks of at most 42 layers, and
  {{lean:NimAudit.WholeGame.twoFrame_wins}} in the stateful predicate {{lean:NimAudit.WholeGame.TwoFrameWins}};
- (ii) rollouts: policy step depth at most 17 (36 layers), register step depth at most 28 (58 layers), readout depth
  at most 19 (40 layers), and {{lean:NimAudit.RolloutExec.mhExec_wins}} with the move bound;
- (iii) recurrence: the controller update and the replay strategy, {{lean:NimAudit.WholeGame.replay_wins}}; the
  board-storage variant is {{lean:NimAudit.BoardStore.bits_store_wins}}.

**Semantics used.** The winning guarantees for (i) and (iii) are proved in their own stateful game predicates
(`TwoFrameWins`, {{lean:NimAudit.WholeGame.ReplayWins}}, `BitStoreWins`). The two-frame strategy is also connected to
the general weak-mastery history model; the recurrent strategies are not (see the open item below).

<!-- explain: c-replay-bridge-open -->
The recurrent strategies are proved to win in a game semantics written for them: a stateful interaction in which the
controller keeps its registers between decisions and every legal opponent response is quantified. The general
history model used for weak mastery ([[def:mastery]]) was formalised in a later phase of the development. A formal
proof that winning in the controller's stateful semantics is the same as winning in the history model has not been
written for the recurrent strategies.

So [[prop:bypass-interfaces]](iii) is checked in the controller's own semantics, not in the history model.

<!-- formal: c-replay-bridge-open -->
**Status: open (optional bridge, not built).** The existing theorems are
{{lean:NimAudit.WholeGame.replay_wins}}, {{lean:NimAudit.WholeGame.replay_game}} and
{{lean:NimAudit.BoardStore.bits_store_wins}}, in their own semantics ({{lean:NimAudit.WholeGame.ReplayWins}}). The
general model is {{lean:NimAudit.Mastery.WeakMastery}}, with bridges so far for `NimGame.Wins`
({{lean:NimAudit.Mastery.wins_secure}}), the pairing strategy ({{lean:NimAudit.Mastery.secondWins_secure}}) and the
two-frame strategy ({{lean:NimAudit.Mastery.twoFrame_secure}}). The independent audit records this bridge as optional
and absent. The website reports it rather than starting a new formalisation project.

<!-- explain: c-bypass-not-ac0 -->
**The three bypasses are not three shallow algorithms for parity.** They are three ways around the *same restricted
inference problem*:

- the two-frame construction changes the input and adds a promise;
- the rollout and recurrent constructions let the processing time grow.

The complete board-to-move maps of the last two cannot be AC⁰ families: otherwise, applied to the boards
$(2,b_1,\dots,b_m)$, they would compute parity, contradicting [[thm:singleframe-impossible]]. Parallel output heads
alone do not supply the rollout computation, and separators alone do not supply a recurrent scan.

<!-- formal: c-bypass-not-ac0 -->
{{lean:NimAudit.Bypass.bypass_barriers}}: under {{lean:NimAudit.Barrier.ParityNotAC0}}, (a) neither the complete
finite-register multi-head map nor the complete recurrent map is computed by any AC⁰ formula family on the encoding
family; (b) nor by any fixed-scale network family; (c) the promised two-frame map does compute parity on promised
pairs, but no AC⁰ family produces the promised predecessor from a single frame
({{lean:NimAudit.Barrier.no_ac0_predecessor}}). The individual barriers are {{lean:NimAudit.Barrier.no_ac0_mh}} and
{{lean:NimAudit.Barrier.no_ac0_rec}}. `ParityNotAC0` comes from the named input `HastadNegl`.

<!-- explain: c-verification-extent -->
This paragraph describes the Lean development: it connects the mathematics to explicit circuits, fixed-scale
networks and complete game strategies, and checks the parity reduction, the probability bound and its attainability,
binary move selection, rollout executors and both shootout schedules, and the recurrent protocols. The size figures
(1,588 theorem and lemma declarations, 38 files, 24,493 source lines) include auxiliary lemmas and exclude
Lean and Mathlib.

Caveat: these are counts of formal declarations, not of independent paper results.

<!-- formal: c-verification-extent -->
A description, not a formal claim. Its figures agree with the independent audit (38 modules; 1,588 theorem and lemma
declarations; 24,493 source lines) and with the fresh rebuild for this edition, which produced exactly one axiom
report for each of the 1,588 indexed theorems. See the [coverage page](coverage.html) and the
[build page](build.html).

<!-- explain: c-verification-boundary -->
The boundary of the verification, in the paper's words:

- **External inputs**: Håstad's parity hardness and correlation bounds, and the Linial–Mansour–Nisan and Tal spectral
  bounds, are not proved in Lean.
- **Conditional results**: the single-channel result is checked conditional on a stated negligible
  parity-correlation theorem, including its application to the readout and the probability calculation.
- **Spectral discussion**: the implication from a Fourier-tail bound to small parity correlation is checked; the
  connection of the tail premise to a published theorem is not.
- **Empirical results** rest on experimental code and saved results, not Lean proofs.

<!-- formal: c-verification-boundary -->
This paragraph is itself a description of coverage. The corresponding records: the named classical input `HastadNegl`
({{claim:rem:local-vs-global-parity.global}}); the conditional single-channel result ({{claim:thm:search-gap.i}});
the tail implication ({{claim:eq:tail-correlation}}) and the open tail-premise connection
({{claim:c-tailpremise-open}}); the empirical records of Section 7.

<!-- explain: c-tailpremise-open -->
The spectral discussion uses a hypothesis of the form "every bounded-depth, bounded-size formula has small Fourier
mass above degree $k$". Results of this kind are classical (Linial–Mansour–Nisan; Tal), but their exact statements use
particular conventions for size, depth and normalisation. Matching the Lean premise to one specific published
statement, with those conventions reconciled, has not been done.

The main results do not depend on this: the single-channel bound uses Håstad's correlation input instead.

<!-- formal: c-tailpremise-open -->
**Status: open.** {{lean:NimAudit.Fourier.TailPremise}} is an explicit, unproved hypothesis of the auxiliary conditional
application {{lean:NimAudit.Fourier.nimBit_corr_of_tail}}; the principal results do not depend on it. The checked
implication from band-limitation to small correlation is {{lean:NimAudit.RealFourier.bandLimited_corr_real}}.

<!-- explain: c-no-discovery -->
A reminder that neither the theorems nor the experiments show that gradient descent or self-play will find these
constructions in general. The theorems are about what can be represented and computed; the experiments are about
particular supervised and imitation runs.

<!-- formal: c-no-discovery -->
A scope statement; nothing is formalised. The corresponding open question is {{claim:c-selfplay-open}}.
