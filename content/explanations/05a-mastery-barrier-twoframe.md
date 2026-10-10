<!-- Sections 5.1-5.3: mastery notions, the single-frame barrier, two-frame restoration. -->

<!-- explain: def:mastery -->
The paper uses three standards of "playing NIM well".

- **Strong mastery**: at *every* winning position where it is to move, the agent chooses a winning move, including
  positions that only arise after mistakes by either player.
- **Weak mastery** (relative to an initial position and a role): if that role can win from the start, the agent's
  own strategy wins against every opponent. Positions that the agent's own play never reaches do not matter.
- **Restoration mastery**: whenever the opponent moves away from a zero-nim-sum position, the agent moves back to
  nim-sum zero.

**Example of the difference.** From the single heap $(3)$, the strategy "take all three stones" wins at once, so it
weakly masters $(3)$ as first player. It says nothing about $(1)$, which strong mastery would require after
$(3)\to(2)\to(1)$ (see [[app:weak]]).

**Caveats spelled out in the definition.** Strategies may use the whole history. Opponent moves are legal; a
missing or illegal agent move counts as a loss. If the designated role is losing from the initial position, weak
mastery asks nothing at all: it is vacuous there.

<!-- formal: def:mastery -->
**Histories and strategies.** A history ({{lean:NimAudit.Mastery.Hist}}) is the list of boards so far, most recent
first; a strategy ({{lean:NimAudit.Mastery.Strat}}) maps a history to a proposed next board or to "no action".

**Consistency.** {{lean:NimAudit.Mastery.Cons}} defines the histories consistent with the agent's own play from an
initial board $P_0$ in role $r$: on the agent's turns only its own prescribed legal action occurs; on the opponent's
turns every legal move may occur.

**The notions.**

- {{lean:NimAudit.Mastery.Guarantee}}: the strategy wins from $P_0$ in role $r$ against every legal opponent
  strategy (plays are finite because stones decrease).
- {{lean:NimAudit.Mastery.WeakMastery}} $F\ r\ \sigma$: from every initial board in the family $F$ from which role
  $r$ has some winning strategy ({{lean:NimAudit.Mastery.RoleWinnable}}), $\sigma$ has the guarantee.
- {{lean:NimAudit.Mastery.StrongMastery}} $F\ r\ \sigma$: at every legal history from $F$ (arbitrary actions by both
  players) where the agent is to move at a nonzero nim-sum, $\sigma$ moves to nim-sum zero.
- Restoration: {{lean:NimAudit.Game.restore_correct}} shows that the two-frame restoration selector has this
  property under its promise.

**Vacuity, made explicit.** {{lean:NimAudit.Mastery.weakMastery_vacuous}}: on a family of boards from which the role
is losing, every strategy, even one that never moves, is weakly masterful. Strong mastery implies weak mastery
({{lean:NimAudit.Mastery.strong_weak}}), and the separation example is {{claim:c-weak-vs-strong}}.

<!-- explain: c-weak-mastery-histories -->
This paragraph restates weak mastery in game-theoretic terms. In NIM the losing positions for the player to move
($P$-positions) are exactly those with nim-sum zero. A strategy weakly masters a family exactly when, starting from
any position its role can win, it moves to a $P$-position at *every* decision point that its own earlier play can
lead to, whatever the opponent does.

That lets a simple strategy master a family without solving positions it never meets. The pairing strategy in
[[app:weak]] is the standard example.

<!-- formal: c-weak-mastery-histories -->
- {{lean:NimAudit.Mastery.secure_iff_guarantee}}: winning against every legal opponent is equivalent to the history
  condition "on every consistent history at the agent's turn, the prescribed action exists and is legal". An absent
  or illegal action is therefore a loss, never a vacuous success.
- {{lean:NimAudit.Mastery.weakMastery_iff_optimal}}: weak mastery holds iff, from every winnable initial board, at
  every consistent history at the agent's turn the strategy plays a legal move to nim-sum zero.
- {{lean:NimAudit.Mastery.roleWinnable_first}}: the first player can win from $P_0$ iff its nim-sum is nonzero (the
  second player iff it is zero).

<!-- explain: thm:singleframe-impossible.a -->
**The reduction.** Look at boards $(2,b_1,\dots,b_m)$ where each $b_i$ is $0$ or $1$. The nim-sum is
$2\oplus(b_1\oplus\cdots\oplus b_m)$, which is $2$ or $3$, so every such board is winning. Only the first heap has
the $2$s bit, so a winning move must change the first heap, and the only value that makes the nim-sum zero is
$b_1\oplus\cdots\oplus b_m$.

**Example.** $(2,1,0,1)$: parity $0$, so the winning move is $2\to0$. $(2,1,1,1)$: parity $1$, so it is $2\to1$.

**Consequence.** Any agent that always finds the winning move on these boards computes the parity of $b$: read off
the new value of the first heap. With two bits per heap, encoding and decoding are mere wiring, so they keep size
and depth unchanged.

<!-- formal: thm:singleframe-impossible.a -->
- {{lean:NimAudit.Game.unique_zero_move}}: the only legal move from {{lean:NimAudit.Game.encode}} $b$ to nim-sum zero
  produces {{lean:NimAudit.Game.reduced}} $b$, the board with first heap $b_1\oplus\cdots\oplus b_m$ (for every $m$,
  including $m=0$).
- {{lean:NimAudit.Game.winning_selector_parity}}: any selector that plays a winning move at every winning position
  outputs the reduced board on these inputs.
- {{lean:NimAudit.ParityCircuit.extraction}}: circuit form. If a binary move selector (a formula family producing a
  valid bit, index bits and two value bits) of depth $d$ and size $s$ strongly masters 2-bit boards with $m+1$
  heaps, then a formula of the same depth and size, reading only the $m$ parity inputs, computes parity. The
  encoding is a leaf substitution, so no resources are added.

<!-- explain: thm:singleframe-impossible.b -->
**The barrier.** Put the reduction together with the simulation theorem: a polynomial-size, constant-depth
fixed-scale network that strongly masters NIM would give AC⁰ circuits computing parity of $m$ bits for every $m$.
Parity is not in AC⁰, so no such network family exists.

**Why it matters.** This is the obstruction behind the whole paper: a single board, processed by a shallow
fixed-scale network in one pass, does not give access to the global invariant.

**Caveats.** It is a worst-case statement within the restricted model (some boards defeat the network, and the
encoded family is enough). It does not say that every learned network fails on typical positions, and it says
nothing about networks outside the model.

<!-- formal: thm:singleframe-impossible.b -->
**Named classical input.** {{lean:NimAudit.Barrier.ParityNotAC0}} is the classical worst-case statement in family
form; it is a theorem *parameter*, never an axiom. {{lean:NimAudit.ClassicalBoundary.parityNotAC0_of_hastad}} derives
it from {{lean:NimAudit.ClassicalBoundary.HastadNegl}}, the negligible-correlation form of Håstad (2014).

**Checked barrier.**

- {{lean:NimAudit.Barrier.barrier_fam}}: under `ParityNotAC0`, no AC⁰ formula family of binary selectors plays a
  winning move on every encoded board.
- {{lean:NimAudit.Barrier.barrier_net}}: the same for fixed-scale network families (fixed $W$, at most $L$ layers,
  polynomial widths and fan-ins) whose output wires are decoded as a binary move. The proof compiles the networks to
  formulas ([[thm:sim-ac0]]) and applies the extraction.

**Relationship to the paper.** The paper says "must compute the parity"; Lean proves the extraction exactly. The
paper says "no network can strongly master NIM"; Lean proves that no family wins on every board of the encoded
subfamily, which is stronger. Parity hardness itself is the external input.

<!-- explain: def:nimber-difference -->
The nimber difference of two positions is the XOR of their nim-sums. Because XOR is its own inverse,
$\operatorname{nim}(P') = \operatorname{nim}(P)\oplus\Delta(P,P')$: the difference is exactly what has to be
"cancelled" to get from one invariant to the other.

<!-- formal: def:nimber-difference -->
Lean does not introduce a separate name: the difference is written `nimSum P ^^^ nimSum P'` wherever it is used.
The key property is {{lean:NimAudit.one_heap_difference}} (next record).

<!-- explain: c-delta-local -->
When a move changes only heap $i$ from $x_i$ to $x_i'$, all other heaps appear in both nim-sums and cancel, so
$\Delta(P,P') = x_i\oplus x_i'$. Example: $(3,5,6)\to(3,4,6)$ gives $\Delta = 5\oplus4 = 1$.

So computing $\Delta$ needs only the changed heap, not a parity over all heaps.

<!-- formal: c-delta-local -->
{{lean:NimAudit.one_heap_difference}}: for lists $\mathit{pre}$, $\mathit{post}$ and values $a,b$, the nim-sums of
$\mathit{pre}\mathbin{+\!\!+}[a]\mathbin{+\!\!+}\mathit{post}$ and $\mathit{pre}\mathbin{+\!\!+}[b]\mathbin{+\!\!+}
\mathit{post}$ differ by $a\oplus b$. {{lean:NimAudit.Misc.delta_bit_local}} gives the bitwise form for any legal move:
bit $k$ of the difference is $a_k\oplus b_k$.

<!-- explain: lem:nimber-diff-ac0 -->
**The statement.** If two boards differ in at most a fixed number $t$ of heaps, their nimber difference can be
computed by an AC⁰ circuit.

**Why.** Compare the two boards heap by heap to find which heaps changed (a local test), XOR each changed pair, and
XOR together at most $t$ such values, which is a constant-size parity. The circuit has to find *where* the changes
are; it does this by trying every possible set of at most $t$ changed heaps in parallel ($O(N^t)$ sets).

**Why it matters.** It is the formal core of the two-frame bypass: the transition is easy even though the state is
hard.

**Caveat.** $t$ must be a constant: the depth bound grows with $t$ and the size bound is polynomial with an exponent
depending on $t$. With an unbounded number of changes the problem becomes global parity again.

<!-- formal: lem:nimber-diff-ac0 -->
The two frames are laid out as one bit vector ({{lean:NimAudit.LocalRestore.tf}}). For each bit $q$, the circuit
{{lean:NimAudit.LocalRestore.bdC}} $B\ N\ t\ q$ is built from per-heap comparisons and exact "at least $k$ of these
heaps differ in bit $q$" counters (valid because at most $t$ heaps differ).

- {{lean:NimAudit.LocalRestore.bdC_eval}}: if at most $t$ heaps differ, the circuit outputs bit $q$ of
  $\operatorname{nim}(Q)\oplus\operatorname{nim}(Q')$.
- {{lean:NimAudit.LocalRestore.bdDelta_eq}}: the $B$ output bits assemble to exactly that number.
- {{lean:NimAudit.LocalRestore.bdC_res}}: depth at most $2t+8$, size at most $(2t+6)(N+t+11)^{3t+6}$, reading only the
  two frames.

The construction differs in detail from the subset enumeration of Appendix E (it counts instead of enumerating
subsets) but proves the same lemma with explicit bounds.

<!-- explain: prop:restore -->
**The idea.** A NIM position with nim-sum zero is "balanced": whoever must move from it loses against correct
play. Any move changes one heap, say from $x_i$ to $x_i'$, and this unbalances the position by exactly
$\delta = x_i \oplus x_i'$. If the reply changes some heap by the *same* XOR difference $\delta$, the two changes
cancel and the balance returns.

**A small example.** In [[fig:restoration-example]], $Q=(3,5,6)$ has nim-sum $3\oplus5\oplus6=0$. The opponent
plays $5\to4$, so $\delta=5\oplus4=1$. The reply $3\to2$ also has $3\oplus2=1$, and $R=(2,4,6)$ has nim-sum
$2\oplus4\oplus6=0$ again.

**Why it matters.** The reply never needs the nim-sum of the whole board. It needs only the two most recent
frames: $\delta$ is read off the one heap that changed, and a cancelling heap is found by a local bit test.
That is why a shallow two-frame network can play this response although no shallow single-frame network can
evaluate the nim-sum ([[thm:singleframe-impossible]]).

**Caveats.**

- The promise matters. If $\operatorname{nim}(Q)\neq0$, matching the difference only reproduces the old value,
  $\operatorname{nim}(R)=\operatorname{nim}(Q)$ (see [[par-the-initialisation-boundary-for-restoration|the initialisation boundary]]).
- Restoration is conditional: it keeps a won position won once a zero-nim-sum position has been established.
  It does not find the first winning move from an arbitrary position.
- The previous frame must be the board the opponent moved from, that is, the player's own post-move board.

<!-- formal: prop:restore -->
**Objects.** A board is a list of natural numbers; {{lean:NimAudit.nimSum}} folds XOR over it.

**The proposition.** Writing $q,q',r$ for the nim-sums of $Q,Q',R$, the paper's proof is the identity
$r = q' \oplus \Delta(Q',R) = q'\oplus (q\oplus q') = q$ under the hypothesis $\Delta(Q',R)=\Delta(Q,Q')$. Lean
states it in exactly this form, {{lean:NimAudit.conditional_restoration}}: if $q=0$ and
$q\oplus q' = q'\oplus r$ then $r=0$. No legality assumption is needed for this step.
{{lean:NimAudit.one_heap_difference}} checks the sentence before it: when one heap changes from $a$ to $b$, the
two nim-sums differ by $a\oplus b$.

**What else is checked.** The shallow selector mentioned right after the proposition, its network form and the
whole-game strategy are in {{claim:c-restore-selector}}. Without the zero-nim-sum promise, matching deltas does not
force zero ({{lean:NimAudit.Rollout.matching_deltas_do_not_force_zero}}; see {{claim:c-init-boundary}}).

<!-- explain: c-restore-selector -->
The proposition says *which* differences to match; this sentence says the matching move can be *found* by a shallow
circuit. Compute $\delta$ from the two frames, then pick (by a fixed tie-break) a heap $i$ with
$x_i'\oplus\delta < x_i'$ and set it to $x_i'\oplus\delta$. Under the promise, $\delta$ equals the current nim-sum, so
such a heap exists: any heap with the top bit of $\delta$ set works.

<!-- formal: c-restore-selector -->
- {{lean:NimAudit.LocalRestore.restore_equiv}}: for $B$-bit boards of equal length $N$, if $\operatorname{nim}(Q)=0$
  and $Q\to Q'$ is legal, the explicit circuit {{lean:NimAudit.LocalRestore.restC}} (which reads only per-heap bit
  differences of the two frames) outputs a move $(i,v)$; applying it gives exactly the board specified by the
  global definition {{lean:NimAudit.Game.restore}}; the move is legal; the result has nim-sum zero.
- {{lean:NimAudit.LocalRestore.restC_bound}}: depth at most 17 and polynomial size, reading only the two frames.
- {{lean:NimAudit.Family.rest_semantics}}: the same objects in the paper's binary output format (valid bit, binary
  index, binary value), both as formulas and as the compiled threshold network with weights and thresholds in
  $\{0,1\}$.
- {{lean:NimAudit.WholeGame.twoFrame_wins}}: a player that stores its own last board and answers every legal
  opponent move with the network's reply wins every play from an established zero-nim-sum board.

<!-- explain: fig:restoration-example -->
The figure works one restoration by hand: $Q=(3,5,6)$ has nim-sum $0$; the opponent's move $5\to4$ has difference
$\delta=1$ and leaves nim-sum $1$; the agent's move $3\to2$ has the same difference $3\oplus2=1$ and returns to nim-sum
$0$. Note that the agent changes a *different* heap from the one the opponent touched; what is mirrored is the XOR
difference, not the heap.

<!-- formal: fig:restoration-example -->
{{lean:NimAudit.Misc.restoration_figure}} checks every number in the figure: the three nim-sums, the legality of both
moves, $5\oplus4=1$, and that the restoration selector {{lean:NimAudit.Game.restore}} applied to
$((3,5,6),(3,4,6))$ returns $(2,4,6)$.

<!-- explain: c-mirror-delta -->
Two local facts make the response pattern shallow. First, when the opponent changes one heap, $\delta$ is that
heap's old value XOR its new value. Second, whether changing heap $i$ realises $\delta$ legally is a test on heap
$i$ alone: $x_i\oplus\delta<x_i$ holds exactly when $x_i$ has a 1 at the highest set bit of $\delta$.

<!-- formal: c-mirror-delta -->
{{lean:NimAudit.AttainCircuit.cancel_iff_bit}}: for $t\neq0$, $x\oplus t<x$ iff bit $\lfloor\log_2 t\rfloor$ of $x$ is
set (one input literal). {{lean:NimAudit.LocalRestore.localDelta_eq}}: the OR-of-XORs delta read off the two frames
equals $\operatorname{nim}(Q)\oplus\operatorname{nim}(Q')$ whenever the frames differ in at most one heap.

<!-- explain: c-mcts-sentence -->
The advantage of two frames is about what a network can *represent*: a two-frame policy can condition on the
locally computable difference, while a single-frame policy must reconstruct the global invariant from one board.

<!-- formal: c-mcts-sentence -->
An interpretive paragraph; the formal contrast is {{claim:prop:restore}} versus
{{claim:thm:singleframe-impossible.b}}.

The reported Section 7 results concern supervised restoration and imitation-trained rollout policies, with no value
head ([[sec:arch]]). They do not establish self-play discovery. An auxiliary MCTS tournament exists in the restoration
notebook, but it is separate from those reported results and is not self-play training. The manuscript's earlier
reference to experimental policy/value networks was corrected in the focused revision.

<!-- explain: c-impl-overview -->
The two-frame player decomposes into four shallow parts: encode heap sizes in binary; detect which heaps changed;
compute $\Delta$ on the changed heaps; select a response that realises a target $\delta$. Each part is a
constant-depth circuit; composing a fixed number of them keeps constant depth.

<!-- formal: c-impl-overview -->
Each item has a checked counterpart: changed-heap detection {{lean:NimAudit.LocalRestore.chgC_eval}}; the delta
{{lean:NimAudit.LocalRestore.localDelta_eq}} (one change) and {{claim:lem:nimber-diff-ac0}} (at most $t$ changes);
the variable-target selector {{lean:NimAudit.SelectCircuit.varSel_correct}} (the target arrives on input wires);
binary output via the priority encoder {{lean:NimAudit.PriorityEncoder.encode_correct}}.
