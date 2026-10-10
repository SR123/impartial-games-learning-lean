<!-- intro -->
The board arrives as a stream of rows, one heap per token, with separators (SEP) between positions and a reset at the
start of a game. Step through the replay controller: in scan mode it XORs each row into the accumulator; the first
separator outputs the summary, stores it and switches to replay mode; during replay the same rows arrive again and
each is tested against the stored summary, keeping the first cancelling candidate and a fallback; the second separator
outputs the move. The board-storage variant instead writes the rows into memory and chooses the move at its single
separator. In the replay controller a separator clears the accumulator and keeps the summary of the position just
completed, with its validity bit; an extra separator is read as an empty position, whose summary is 0. Only a reset
returns every register, validity included, to its initial value. The board-storage separator clears its accumulator
and pointer and keeps the stored board. The third protocol shows the summary mechanism of
[[prop:streaming-nimsum]] alone: it reports summaries and differences but chooses no move.

<!-- notes -->
**How this relates to the Lean proof.** Each update is one step of {{lean:NimAudit.Controller.cstep}} (replay) or
{{lean:NimAudit.BoardStore.bsStep}} (board storage) on the token streams {{lean:NimAudit.Controller.dtoks}} and
{{lean:NimAudit.BoardStore.btoks}}. The whole-game theorems {{lean:NimAudit.WholeGame.replay_wins}} and
{{lean:NimAudit.BoardStore.bits_store_wins}} prove that, from every board with nonzero nim-sum, iterating these
updates wins against every legal opponent. The summary mechanism is {{lean:NimAudit.Recurrent.step}}.
The comparison of decision-time boards with the post-move board is
{{lean:NimAudit.Bypass.diff_with_postMove}} and {{lean:NimAudit.Bypass.diff_decision_only}}.

**What this does not show.** Each single update is shallow; the number of updates per decision ($2N+2$, or $N+1$
with board storage) grows with the board. That no shallow family computes the complete board-to-move map is a
separate statement, conditional on the named classical input that parity is not in $\mathrm{AC}^0$. The edge cases
(an extra separator, a reset) lie outside the protocol streams that the theorems quantify over; the update rule is
simply applied. The recurrent strategies are proved in their own stateful game semantics; connecting them to the
later history model of weak mastery is a separate adapter that has not been built
([coverage record](claims/c-replay-bridge-open.html)). No recurrent network was trained.
