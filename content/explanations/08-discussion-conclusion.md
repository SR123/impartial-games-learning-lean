<!-- Sections 8 and 9: discussion and conclusion. -->

<!-- explain: c-discussion -->
The common design principle behind the three bypasses: match the information and computation available to the agent
to the invariant it must maintain. Two frames expose local transition information; several rollout heads provide
complementary channels; persistent recurrence accumulates the invariant, with memory connecting positions and a growing
processing horizon supplying the depth that parity needs.

<!-- formal: c-discussion -->
A summary; the formal content is {{claim:prop:bypass-interfaces}}.

<!-- explain: c-idealisation -->
The theorem's gates (nonnegative weights on Boolean literals, bounded thresholds) and the experiments' networks
(floating-point signed linear layers, ReLU, LayerNorm, Log-Softmax loss) differ in more than normalisation. Two
consequences: a failure at one finite board size does not prove an asymptotic impossibility, and success on a finite
dataset does not prove strong mastery. What the experiment supports is narrower: under this supervised protocol, the
transition representation is much easier to learn.

<!-- formal: c-idealisation -->
A scope statement relating {{claim:thm:sim-ac0}} to the empirical records; nothing further is formalised.

<!-- explain: c-condorcet -->
Exposing local invariants may help combinatorial search elsewhere. The paper mentions its authors' work on large
Condorcet domains, which used structural constructions and local restrictions, and says explicitly that this is a
motivating analogy: not an AC⁰ reduction and not a parity lower bound for that problem.

<!-- formal: c-condorcet -->
An analogy citing related work; nothing is claimed formally.

<!-- explain: c-geography -->
Every finite impartial game position has a nimber, but computing it can be very hard. For directed vertex Geography the
winner problem is PSPACE-complete (Schaefer, 1978); unless P = PSPACE, no polynomial-time algorithm solves all instances.
Existence of a nimber gives no efficient way to compute it.

<!-- formal: c-geography -->
A classical external result, cited; not formalised.

<!-- explain: c-othergames-scope -->
NIM is useful precisely because we know an efficient optimal strategy. It lets us ask whether an architecture can express
that strategy and whether training finds it. Harder impartial games add another challenge: discovering strategic structure
that is only partly understood or expensive to obtain by exact search.

<!-- formal: c-othergames-scope -->
A scope statement; nothing is formalised.

<!-- explain: c-harder-benchmarks -->
The proposed games test different kinds of structure. Sprouts involves evolving planar regions; Chomp involves board
shape and move choice even when an opening winner is known; Grundy's game involves learning component values and combining
them. These are proposals for future evaluations, not games solved by the present paper.

The game names alone do not define a benchmark. The starting-position distribution, allowed information, training sizes,
held-out sizes and search budget must all be specified. An agent that predicts a familiar opening pattern may still fail
to choose a winning move in a new intermediate position.

<!-- formal: c-harder-benchmarks -->
No new Lean theorem is asserted. The paper cites the published Sprouts solver study and the open-problems literature;
the learning challenges are the author's proposed applications. The existing NIM formalisation does not certify these
games' rules, outcome conjectures, strategies or learnability.

<!-- explain: c-benchmark-evaluation -->
Use exact solvers to measure move quality where possible. On larger instances, compare against strong search opponents
under stated budgets, while keeping the claim proportional to the evidence: higher win rates show stronger play, not
optimal play against every opponent. Generalisation beyond training sizes is central to the proposed tests.

<!-- formal: c-benchmark-evaluation -->
An evaluation proposal, not a mathematical consequence of the AC⁰ lower bound. No experiment on these harder games is
reported here, and no generalisation guarantee is formalised.

<!-- explain: c-development-disclosure -->
The final section distinguishes the earlier version, developed solely by the author with editorial AI feedback, from
the present version, developed interactively with Astra and Claude and informed by feedback from the Lean formalisation. Responsibility for the paper remains with the sole author. This disclosure is part of the paper itself;
the personal historical motivation remains separately behind the landing page's Author's perspective link.

<!-- formal: c-development-disclosure -->
An author disclosure, not a theorem. Neither Lean nor the website can verify an account of how the manuscript was written.

<!-- explain: c-author-verification-scope -->
There are two distinct checks: whether Lean accepts a proof of a formal statement, and whether that statement correctly
expresses the intended paper claim. The author reports reviewing the second interface without manually reading every
helper proof. The linked statements, definitions and source allow readers to examine both levels.

<!-- formal: c-author-verification-scope -->
The reported development contains 1,588 theorem/lemma declarations and 24,493 lines across 38 Lean modules, including
auxiliary results. A successful build checks formal proofs relative to definitions and explicit hypotheses; it does not
discharge an external hypothesis, validate experimental data, or prove that an English paraphrase is faithful. See
[[sec:development]] and the coverage record for the boundaries. The new disclosure does not change any Lean source.

<!-- explain: c-rollout-separation -->
Theorem 5.12(i) is narrow on purpose: fixed bit-width, a specified family of root and one-heap measurements, and a
polynomial-size, constant-depth readout. It does not bound general single-policy search. Within that interface, $B$
channels reconstruct the invariant. The extra resource is the sequential rollout, not the number of output neurons.
Changing the allowed queries or controller computation changes the model and can remove the restriction.

<!-- formal: c-rollout-separation -->
An interpretation of {{claim:thm:search-gap.i}} and {{claim:c-arbitrary-starts}} (which shows how arbitrary queries
would remove the restriction).

<!-- explain: c-opt-gap -->
The constructions show that the needed computations *can* be expressed with the stated resources. That removes one
obstacle before training starts. It does not decide whether gradient descent finds them, whether sparse game rewards give
enough signal, or whether the resulting behaviour generalises.

<!-- formal: c-opt-gap -->
A statement about the scope of the results; not formalised.

<!-- explain: c-opt-gap-evidence -->
The restoration experiment illustrates the gap: even with transition information and correct labels, learning passes
through a plateau before becoming near-perfect, and the diagnostic ties the later improvement to the lowest bit of the
selected move's change. So there is empirical evidence of a remaining learning bottleneck, alongside a theorem about a
different, representational obstruction. How many mechanisms produce the stages, and why, is not established.

<!-- formal: c-opt-gap-evidence -->
An interpretation of the empirical records {{claim:c-plateau}} and {{claim:c-diagnostic}}.

<!-- explain: c-selfplay-open -->
The open experimental question: can AlphaZero-style self-play discover the restoration rule, complementary rollout
policies or the recurrent accumulator *without* supervised targets? A follow-up would compare outcome-only training with
curricula and auxiliary supervision and inspect the learned computations, not just win rates. For recurrence it would
also test accurate accumulation and state retention across separators.

<!-- formal: c-selfplay-open -->
**Status: open (stated as such in the paper).** No theorem or experiment here addresses it.

<!-- explain: c-significance -->
Three broader implications: for learning theory, representational sufficiency and learnability are separate questions;
for architecture, short histories or difference features, multiple rollout heads, or persistent recurrence are
principled ways around parity-like barriers; for practice, circuit complexity can generate architectural hypotheses, as
long as the implemented model satisfies the mathematical assumptions and tests separate representation, training
dynamics, data distribution and compute.

<!-- formal: c-significance -->
Interpretive; nothing is formalised.

<!-- explain: c-conclusion -->
The first conclusion paragraph restates the two main theorems: a fixed-depth Boolean literal-threshold model with
nonnegative fixed-grid weights and bounded thresholds is simulable in AC⁰, and the NIM parity reduction then rules out
strong single-frame mastery in that model.

<!-- formal: c-conclusion -->
A restatement of {{claim:thm:sim-ac0}} (checked) and {{claim:thm:singleframe-impossible.b}} (checked conditional on the
named classical input `HastadNegl`).

<!-- explain: c-conclusion-bypasses -->
The second paragraph summarises what the constructions supply: two-frame access gives constant-depth restoration when
the preceding position has nim-sum zero; distinct structured rollout policies reveal complementary invariant bits, with a
single-channel limitation only under the explicit query and readout restrictions; persistent recurrence implements
running XOR over heap rows, trading fixed total latency for a growing number of simple updates; cross-position memory
supports comparisons; replay or board storage supplies the heaps needed for move selection.

<!-- formal: c-conclusion-bypasses -->
A summary of {{claim:prop:bypass-interfaces}}, {{claim:thm:search-gap.i}}, {{claim:c-replay}} and
{{claim:c-board-storage}}.

<!-- explain: c-conclusion-experiments -->
The third paragraph says what the saved experiments show: a large supervised two-frame restoration advantage, and perfect
finite-test $P/N$ classification by a learned multi-head controller despite imperfect individual channels; learning can
proceed in stages even after transition information is supplied. It also says what they do not show: the formal gate
assumptions, worst-case mastery, or self-play discovery.

<!-- formal: c-conclusion-experiments -->
A summary of the empirical records {{claim:c-exp-result-1f2f}}, {{claim:c-fsm-results}} and {{claim:c-plateau}}.
