<!-- Handwritten explanations for the interactive edition (levels 2 and 3).
     Front matter and Section 1.  Each entry starts with <!-- explain: ID --> or <!-- formal: ID -->.
     References: [[label]] links into the paper, {{lean:Name}} to a Lean declaration,
     {{claim:id}} to another claim record. -->

<!-- explain: c-abstract -->
The abstract compresses the whole paper into a few sentences. Each sentence corresponds to a precise statement
inside the paper, and several of them carry conditions that the abstract can only hint at:

- "lies in AC⁰" is [[thm:sim-ac0]], for an explicitly restricted model of fixed-scale threshold networks, not for
  neural networks in general;
- "prevents optimal single-position play" is [[thm:singleframe-impossible]], which uses the classical fact that
  parity is not in AC⁰;
- the three routes around the obstruction are [[prop:restore]] (two frames, given a zero-nim-sum predecessor),
  [[prop:rollout-sufficiency]] (several rollout policies, executed in sequence) and [[prop:streaming-nimsum]]
  (a recurrent scan whose length grows with the board, with retained state, a reset, and a replay of the board or
  board storage to choose a move);
- the experiments are single saved supervised and imitation runs ([[sec:supervised-restoration]],
  [[sec:exp-fsm-shootout]]).

The learnability qualification says what is *not* claimed: the constructions are representational possibilities, not
guarantees that training will find them, and AC⁰ membership is not a test of learnability.

<!-- formal: c-abstract -->
The abstract itself is not formalised; it summarises. Its mathematical sentences are covered by the records of
the statements listed above, each with its own category. Its verification statement, that core results were checked in
Lean with classical complexity results as explicit external inputs, is reflected on the
[coverage page](coverage.html): conditional results name their classical input, `HastadNegl`, and empirical
results are marked as such.

The abstract cites the interactive edition and the complete Lean source repository. Their full addresses appear as plain text in the references, in both the PDF and the interactive article. Section 10 cites the same resources.

<!-- explain: c-intro-zhou -->
This paragraph places the paper in the author's earlier work. Zhou and Riis trained AlphaZero-style agents on
impartial games and observed that performance on NIM deteriorated as boards grew. A follow-up study looked at
parity tasks learned through a curriculum with noisy labels, and Zhou's thesis collects the work.

Why it matters here: those observations motivate the question of the paper, namely why a game with a short,
exact solution rule can still be hard for a learner. The present paper does not re-run those experiments.

<!-- formal: c-intro-zhou -->
This is a report of published empirical work, cited as background (Zhou and Riis, 2026, first preprint 2022;
Zhou and Riis, 2023; Zhou, 2024). Nothing in the Lean development concerns it, and the edition does not
re-examine those experiments.

<!-- explain: c-intro-ac0 -->
**What AC⁰ is.** AC⁰ is the class of Boolean functions computed by circuits of AND, OR and NOT gates (with any
number of inputs per gate) whose size grows at most polynomially and whose number of layers stays fixed as the
input grows.

**What it cannot do.** Such circuits can combine many local tests, but they cannot compute the parity of all their
input bits once the input is large: this is a classical theorem of circuit complexity.

**Why it is used.** The earlier experiments pointed to parity as the difficulty; AC⁰ gives a precise model in which
a version of that limitation is provable. Whether it explains the training failures is a separate question.

**Caveat.** The paper does not assume that neural networks are AC⁰ circuits. It proves AC⁰ membership only for a
restricted model of fixed-scale threshold networks ([[thm:sim-ac0]]). The class is AC⁰, not ACC⁰: ACC⁰ allows
counting-modulo gates, which can compute parity directly.

<!-- formal: c-intro-ac0 -->
The definition of AC⁰ is standard. The parity lower bound is a classical external result (Furst, Saxe and
Sipser; Håstad). In the Lean development it enters as the named hypothesis `HastadNegl`, from which the
worst-case statement `ParityNotAC0` is derived ({{lean:NimAudit.ClassicalBoundary.parityNotAC0_of_hastad}}); see
{{claim:rem:local-vs-global-parity.global}}. The restricted neural model and its simulation are
{{claim:thm:sim-ac0}}.

<!-- explain: c-intro-necessary -->
This sentence states the logical role of AC⁰ in the paper.

- **Necessary within the model.** By [[thm:sim-ac0]], anything a fixed-latency network of the restricted kind can
  compute is in AC⁰. So if a decision rule is provably *not* in AC⁰, no such network can implement it.
- **Not sufficient for training.** A function can be in AC⁰ and still be hard to learn by gradient descent or
  self-play.
- **Not universal.** Networks outside the model (scale-adaptive thresholds, growing depth, ordinary
  floating-point layers) are not constrained by this argument.

The "barrier-to-bypass" idea is to use the obstruction constructively: it tells us what an architecture must add.

<!-- formal: c-intro-necessary -->
This is an interpretation of [[thm:sim-ac0]]. The formal content is that theorem (checked in Lean, see
{{claim:thm:sim-ac0}}); the statements about training and about networks outside the model are deliberately
not formal claims.

<!-- explain: c-intro-transition -->
**The key distinction.** A *state* (a single NIM board) can be hard to process, while a *transition* (one board
and the next) can be easy: if the previous board had nim-sum zero, the difference $\delta$ that the reply must
cancel depends only on the heap that changed, and a reply realising $\delta$ is found by a separate local test on
each heap.

**Three routes.** Two frames expose that transition; several rollout policies extract complementary bits of the
invariant; a recurrent scan accumulates it row by row.

**Shallow parts versus the whole computation.** In all three routes each *component* is shallow. But the
rollout and recurrent routes run a sequence of shallow steps whose number grows with the board, and the complete
computation is not itself an AC⁰ circuit. That is how the bypasses coexist with the lower bound.

<!-- formal: c-intro-transition -->
An overview paragraph. Its precise counterparts are {{claim:prop:restore}} (with
{{claim:c-restore-selector}}), {{claim:prop:bypass-interfaces}} (shallow components and winning strategies) and
{{claim:c-bypass-not-ac0}}, which proves, conditional on the classical parity bound, that the complete
multi-head and recurrent board-to-move maps are not AC⁰ families.

<!-- explain: fig:barrier-blueprint -->
**Terminology.** FSQI means fixed-scale quantised inference. Fixed latency means that the number of sequential computation steps stays bounded as the board grows, rather than a fixed measured running time in seconds.

The figure is a map of the paper. Row (a) is the obstruction: a single network that sees one board cannot
compute global parity under the fixed-scale model. Rows (b)–(d) are the three bypasses, each supplying something
different: (b) the transition between two boards, given a zero-nim-sum predecessor; (c) the outcomes of complete rollouts under several policy
heads; (d) a recurrent state carried over many row updates, so that total latency grows with the number of heaps.

Caveat: a check mark in the figure means "this computation becomes available", not "learning succeeds".

<!-- formal: fig:barrier-blueprint -->
A schematic, not a formal statement. Each row corresponds to checked results: (a)
{{claim:thm:singleframe-impossible.b}}; (b) {{claim:prop:restore}} and {{claim:c-restore-selector}}; (c)
{{claim:prop:rollout-sufficiency}}; (d) {{claim:prop:streaming-nimsum}} and {{claim:c-replay}}.

<!-- explain: c-contributions -->
The first item distinguishes gate restrictions from input layout: attention operations must be built from the permitted gates, while board sizes can grow across the family of networks. Within a play sequence, aligned heap rows and fixed bit width make consecutive boards comparable.

The list names six contributions. Read with the paper, each item is a pointer: the first four are theorems or
propositions (simulation, barrier, two-frame bypass, rollout analysis), the fifth is the recurrent construction,
and the sixth is the controlled experiments plus a discussion of the modelling choice. The wording in the list is
deliberately qualified: "conditional restoration mastery, not an arbitrary-start verifier"; "a restricted
measurement interface … rather than a general model of MCTS"; "relaxes fixed total latency, not fixed-scale
quantisation".

<!-- formal: c-contributions -->
A summary list. Its items are covered by the records of the statements it cites; see the coverage table for their
categories. In particular, the probability bound in the fourth item is a *checked conditional theorem using a
named classical input* ({{claim:thm:search-gap.i}}), and the sixth item is *empirical*.

<!-- explain: c-scope -->
This list states what kind of results the paper contains:

- they are **worst-case representational** statements under explicit constraints;
- the formal model (nonnegative weights on Boolean literals, bounded thresholds) differs from the experimental
  networks (floating-point, signed weights, ReLU, LayerNorm);
- the single-channel lower bound concerns a **stylised planning interface**, not general MCTS;
- nothing guarantees **learnability**; self-play discovery is left open.

<!-- formal: c-scope -->
Scope statements, not claims to be proved. They match the hypotheses of the formal results: the gate model of
{{claim:def:NN-formal}}, the interface of {{claim:def:agent-types}}, and the empirical status of the experiments
({{claim:c-exp-result-1f2f}}).

<!-- explain: c-intro-games -->
NIM has heaps of tokens. On each turn, remove at least one token from one heap; taking the last token wins. For example, $(3,5,6)$ can become $(3,4,6)$, but a single move cannot alter both the first and second heaps.

Impartial games allow the same moves to either player. Shared pieces are a useful intuition; the formal condition concerns legal moves, not ownership. Chess is partisan because the players move different colours. The striking link to NIM is explained in {{claim:c-sprague-grundy}}: every finite terminating normal-play impartial position can be replaced, in sums, by one NIM heap. This is a structural statement, not an efficient method for solving every impartial game.

<!-- formal: c-intro-games -->
This introduction combines the classical impartial-game definition, {{claim:def:impartial}}, with the NIM rules, {{claim:def:nim}}, and the external Sprague–Grundy theorem, {{claim:c-sprague-grundy}}. The Lean development checks NIM, rather than the general Sprague–Grundy theorem.

<!-- explain: c-history-context -->
History does not change what the correct move is in NIM. It can change how easily a restricted computation finds it. With a preceding zero-nim-sum board, unchanged heaps cancel and a local difference supplies the current nim-sum. A recurrent scanner instead accumulates the current nim-sum over time, and can retain earlier summaries to compare positions.

The recurrent route does not require an earlier game position for initialisation: remembering the partial result while scanning the current board already suffices.

<!-- formal: c-history-context -->
This is an interpretation of {{claim:prop:restore}}, {{claim:prop:streaming-nimsum}} and {{claim:c-recurrence-history}}. The game state and legal moves are defined in {{claim:def:nim}}. No theorem claims that past positions are necessary for every optimal recurrent strategy.
