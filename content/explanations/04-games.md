<!-- Section 4: impartial games and NIM. -->

<!-- explain: def:impartial -->
The phrase “shared pieces” is a useful board-game intuition. The precise condition is that the same position permits the same moves for either player; it also covers games without physical pieces. In partisan games the available moves can depend on the player's identity.

An impartial game is one in which both players have the same moves from every position (unlike chess, where each
player moves their own pieces). "Finite terminating" means play always ends; under *normal play* the player who
makes the last move wins.

Example: NIM is impartial, since any player may reduce any heap.

<!-- formal: def:impartial -->
General impartial games and Sprague–Grundy theory are classical background (Berlekamp, Conway and Guy). The Lean
development formalises NIM itself, not general impartial games; its normal-play semantics are in
{{claim:def:nim}} and {{claim:thm:nim-win}}.

<!-- explain: c-terminal -->
A terminal position is one with no legal moves. In NIM, these are exactly the boards whose heaps are all empty; the
player to move there has lost (normal play).

<!-- formal: c-terminal -->
{{lean:NimAudit.Game.Terminal}} defines a terminal board as one whose heaps are all zero, and
{{lean:NimAudit.Game.terminal_iff_no_move}} proves that this is equivalent to having no legal move.

<!-- explain: def:nim -->
A NIM position is a list of heap sizes. A move picks one nonempty heap and replaces it by any strictly smaller
size. Example: from $(3,5,6)$ one legal move is $(3,4,6)$; $(3,5,7)$ is not a move (heaps never grow), and neither
is $(2,4,6)$ (two heaps changed).

<!-- formal: def:nim -->
{{lean:NimAudit.Game.Move}}: $q$ is reached from $p$ when $p = \mathit{pre} \mathbin{+\!\!+} [x] \mathbin{+\!\!+}
\mathit{post}$ and $q = \mathit{pre}\mathbin{+\!\!+}[y]\mathbin{+\!\!+}\mathit{post}$ with $y<x$: exactly one heap
strictly decreases and the heap positions stay aligned. {{lean:NimAudit.Game.move_sum_lt}} proves that every move
lowers the total number of stones, which is how termination is proved throughout.

<!-- explain: c-sprague-grundy -->
**What equivalence means.** In a disjunctive sum, each turn changes exactly one component. Replacing a component by its equivalent NIM heap preserves the winning or losing status with every other normal-play impartial component. This makes NIM central to the theory of a very broad class of games, even though computing the equivalent heap size can be difficult.

The Sprague–Grundy theorem says that every finite impartial game position behaves, in sums of games, like a single
NIM heap of some size (its nimber or Grundy value). For NIM itself, the Grundy value of a position is the XOR of
its heap sizes.

Caveat: the theorem guarantees that a nimber exists, not that it is easy to compute (see [[sec:othergames]]).

<!-- formal: c-sprague-grundy -->
The general theorem is classical background and is not formalised. For NIM, the fact that matters (losing exactly
when the XOR is zero) is checked as {{claim:thm:nim-win}}.

<!-- explain: def:nimsum -->
The nim-sum of heap sizes is their bitwise XOR: write each size in binary and, in each bit position, count the
ones; the result has a 1 exactly where that count is odd. Example: $3\oplus5\oplus6$: $011\oplus101\oplus110 =
000$, so the nim-sum is $0$.

Each bit of the nim-sum is therefore a *parity* over all heaps, which is what makes it hard for shallow circuits.

<!-- formal: def:nimsum -->
{{lean:NimAudit.nimSum}} folds Lean's bitwise XOR over the list of heaps (empty board: $0$).
{{lean:NimAudit.nimSum_append}} proves that the nim-sum of two concatenated lists is the XOR of their nim-sums, the
basic tool for local reasoning about one changed heap.

<!-- explain: thm:nim-win -->
**The statement.** A position is lost for the player to move exactly when the nim-sum is zero. From any position
with nonzero nim-sum there is a move that makes it zero.

**Example.** $(3,5,6)$ has nim-sum $0$: whatever you do, the opponent can restore zero, and eventually you face the
empty board. $(3,4,6)$ has nim-sum $1$: reducing $3$ to $2$ makes it zero.

**Why it matters.** Optimal play is "always move to nim-sum zero". The rule is short and exact, yet it requires the
XOR of all heaps, a global parity computation.

**How to find the move.** Let $s\ne0$ be the nim-sum and $k$ its highest set bit. Some heap $x$ has bit $k$ set;
then $x\oplus s<x$, and replacing $x$ by $x\oplus s$ makes the nim-sum $0$.

<!-- formal: thm:nim-win -->
**Semantics.** {{lean:NimAudit.Game.Win}} and {{lean:NimAudit.Game.Lose}} are defined together, by induction, as the
normal-play notions for the player to move: a position is winning if some move reaches a losing position; it is
losing if every move reaches a winning position (so a terminal position is losing).

**Checked statements.**

- {{lean:NimAudit.Game.lose_iff}}: `Lose p ↔ nimSum p = 0`, for every board.
- {{lean:NimAudit.Game.win_iff}}: `Win p ↔ nimSum p ≠ 0`.
- {{lean:NimAudit.Game.exists_move_to_zero}}: from a nonzero nim-sum some legal move reaches nim-sum zero (the
  top-bit argument above, proved in {{lean:NimAudit.Rollout.exists_decreasing_heap}}).
- {{lean:NimAudit.Game.move_from_zero}}: every legal move from a zero nim-sum reaches a nonzero one.

The theorem is the classical one; Lean checks it in exactly the paper's form, for any number of heaps.

<!-- explain: c-why-nim -->
NIM isolates one obstruction cleanly: for a sum of independent impartial games the Grundy value is the XOR of the
components' values, so whenever those values can vary independently, the aggregation step contains a parity
problem. NIM is that aggregation step with nothing else around it.

Caveats stated in the paper: Sprague–Grundy theory does not give an efficient way to compute component nimbers,
and not every impartial game has a hard parity aggregation. The lower bound is proved for NIM; other games need an
explicit encoding and reduction.

<!-- formal: c-why-nim -->
A motivating paragraph. The only formal statement is about NIM, {{claim:thm:singleframe-impossible.b}}; no claim
about other games is made or checked.

<!-- explain: c-ending-encodings -->
“Normal play” means that a player with no legal move loses. Many other decisive endings can be expressed with this convention. If a move wins by achieving a configuration, declare that configuration terminal. If the player making the move instead loses on reaching it, give the opponent one forced move to a new terminal position, so the opponent makes the last move.

This preserves the winner of the individual play, provided the encoding tracks the decisive event correctly. To obtain an impartial game, the resulting move rule must still be independent of player identity. It does not make chess impartial or resolve draws and infinite play. Nor does preserving an isolated game's winner imply that its sums under the original ending rule are equivalent: Sprague–Grundy theory applies to the resulting normal-play rules.

<!-- formal: c-ending-encodings -->
This is an explanatory encoding observation, not a new Lean-checked theorem. The formalisation checks NIM with its usual last-move-wins rule; see {{claim:def:nim}} and {{claim:thm:nim-win}}. General impartial games and their Sprague–Grundy theory remain classical background.
