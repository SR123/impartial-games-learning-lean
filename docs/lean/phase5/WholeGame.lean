import ThresholdInst

/- Phase 5, task 3: whole-game strategies driven by the actual implementations.
   Written by Claude (10 October 2026).  Lean 4.26.0, core/Std only.

   A. TWO-FRAME RESTORATION.  The player stores its last established zero-nim-sum
      board Q.  After any legal opponent move Q → Q' it evaluates the compiled
      fixed-scale network for the LOCAL binary restoration circuit on the two frames
      (Q, Q'), decodes the output wires to (i, v), plays Q' → Q'.set i v and stores that
      board.  `TwoFrameWins` is a new, explicitly stateful game predicate (the strategy
      needs the predecessor, so the history-free NimGame.Wins does not apply directly);
      `twoFrame_sound` connects it to NimGame's Lose.  No claim is made about finding an
      initial move from an arbitrary winning position.
   B. MULTI-HEAD.  Rollouts are executed with the compiled π_j networks (one network
      evaluation per simulated game move); their terminal parities feed the compiled
      multi-head network; the resulting history-free selector wins against every legal
      opponent (NimGame.Wins) from every nonzero position.
   C. RECURRENT REPLAY.  The compiled threshold controller is driven by the explicit
      protocol rows SEP rows SEP (the ENVIRONMENT supplies the replay of the same board;
      it is an input-protocol assumption, not hidden memory), its emitted move is applied
      to the board, the internal state persists across decisions, and a reset token
      starts each game from an arbitrary bit state. -/

namespace NimAudit
namespace WholeGame

open Game Rollout Prob Attain Recurrent AC0 AC0.Circ CorrBridge AttainCircuit Bridge SelectCircuit
  BinReadout Controller ControllerBits PriorityEncoder ThresholdNet ThresholdInst FiniteNet

theorem move_length {p q : List Nat} (h : Move p q) : q.length = p.length := by
  obtain ⟨pre, x, post, y, rfl, rfl, _⟩ := h; simp

/-! ## A. Two-frame restoration with a stored predecessor -/

/-- The player's reply: evaluate the compiled restoration network on (Q, Q'), decode its
    output wires and apply the decoded move to Q'.  Index width r = log₂N + 1. -/
def restReply (B : Nat) (Q Q' : List Nat) : Option (List Nat) :=
  applyM Q' (netBinSem (restNet B Q'.length (Q'.length.log2 + 1)) Q'.length (Q'.length.log2 + 1) B
    (LocalRestore.tf B Q'.length Q Q'))

/-- Stateful two-frame game predicate (opponent to move at the stored board Q): every
    legal opponent move is answered by a legal reply, the reply's board becomes the new
    stored board, and play continues.  Being inductive, every such play is finite; at a
    terminal stored board the opponent cannot move and loses. -/
inductive TwoFrameWins (reply : List Nat → List Nat → Option (List Nat)) : List Nat → Prop
  | intro (Q : List Nat) :
      (∀ Q', Move Q Q' → (reply Q Q').isSome = true) →
      (∀ Q' R, Move Q Q' → reply Q Q' = some R → Move Q' R) →
      (∀ Q' R, Move Q Q' → reply Q Q' = some R → TwoFrameWins reply R) →
      TwoFrameWins reply Q

/-- Soundness for the game semantics: the opponent, to move at the stored board, loses. -/
theorem twoFrame_sound {reply : List Nat → List Nat → Option (List Nat)} {Q : List Nat}
    (h : TwoFrameWins reply Q) : Lose Q := by
  induction h with
  | intro Q hsome hmove _ ih =>
    refine Lose.intro Q (fun Q' hm => ?_)
    cases hr : reply Q Q' with
    | none => have := hsome Q' hm; rw [hr] at this; cases this
    | some R => exact Win.intro Q' R (hmove Q' R hm hr) (ih Q' R hm hr)

/-- ONE STEP: from a stored board with the zero invariant and any legal opponent move,
    the network reply is legal, equals NimGame.restore, and the new stored board keeps
    the length, the bit width and the zero invariant. -/
theorem restReply_step {B : Nat} {Q Q' : List Nat} (hw : Width B Q) (h0 : nimSum Q = 0) (hm : Move Q Q') :
    ∃ R, restReply B Q Q' = some R ∧ restore Q Q' = some R ∧ Move Q' R ∧ nimSum R = 0 ∧
      R.length = Q.length ∧ Width B R := by
  have hl := move_length hm
  have hw' := width_move hw hm
  obtain ⟨i, v, h1, h2, h3, h4⟩ := restNet_correct (B := B) (N := Q'.length) (r := Q'.length.log2 + 1)
    (width_log _) (by omega) rfl hw hw' h0 hm
  refine ⟨Q'.set i v, ?_, h2, h3, h4, by rw [move_length h3, hl], width_move hw' h3⟩
  unfold restReply; rw [h1]; rfl

/-- TWO-FRAME WHOLE-GAME THEOREM: from an established zero-nim-sum stored board (opponent
    to move), the network-driven two-frame player answers every legal opponent move
    legally, keeps the zero invariant, the board length and the bit width, and every play
    terminates with the player making the last move.  Includes terminal and empty
    boards (no opponent move exists). -/
theorem twoFrame_wins {B : Nat} : ∀ (Q : List Nat), Width B Q → nimSum Q = 0 →
    TwoFrameWins (restReply B) Q := by
  intro Q
  induction Q using (measure List.sum).wf.induction with
  | h Q ih =>
    intro hw h0
    refine TwoFrameWins.intro Q (fun Q' hm => ?_) (fun Q' R hm hR => ?_) (fun Q' R hm hR => ?_)
    · obtain ⟨R, h1, _⟩ := restReply_step hw h0 hm
      rw [h1]; rfl
    · obtain ⟨R', h1, _, h3, _⟩ := restReply_step hw h0 hm
      rw [h1] at hR; cases hR; exact h3
    · obtain ⟨R', h1, _, h3, h4, _, h6⟩ := restReply_step hw h0 hm
      have hRR : R' = R := by rw [h1] at hR; exact Option.some.inj hR
      subst hRR
      refine ih R' ?_ h6 h4
      have := move_sum_lt hm; have := move_sum_lt h3
      show R'.sum < Q.sum; omega

/-- Edge case: at a terminal (e.g. empty) stored board the opponent has no move. -/
theorem twoFrame_terminal {B : Nat} {Q : List Nat} (hw : Width B Q) (ht : Terminal Q) :
    TwoFrameWins (restReply B) Q ∧ ∀ Q', ¬ Move Q Q' :=
  ⟨twoFrame_wins Q hw (terminal_nimSum_zero ht), (terminal_iff_no_move Q).1 ht⟩

theorem twoFrame_lose {B : Nat} {Q : List Nat} (hw : Width B Q) (h0 : nimSum Q = 0) : Lose Q :=
  twoFrame_sound (reply := restReply B) (twoFrame_wins Q hw h0)

/-! ## B. Multi-head strategy with network-executed rollouts -/

/-- Index width used for N heaps. -/
def rIdx (N : Nat) : Nat := N.log2 + 1

/-- One π_j step executed by the compiled policy network. -/
def polStepN (B j : Nat) (P : List Nat) : Option (List Nat) :=
  applyM P (netBinSem (polNet B P.length j (rIdx P.length)) P.length (rIdx P.length) B (boardBits B P))

theorem polStepN_eq {B j : Nat} {P : List Nat} (hw : Width B P) : polStepN B j P = policyStep j P :=
  polNet_correct (r := rIdx P.length) (width_log _) rfl hw

theorem policyStep_move {j : Nat} {p q : List Nat} (h : policyStep j p = some q) : Move p q := by
  obtain ⟨pre, x, post, d, hp, hq, hd, hdx, _⟩ := policyMove_legal (policyStep_some h)
  exact ⟨pre, x, post, x - d, hp, hq, by omega⟩

/-- A rollout executed by the policy network: one network evaluation per simulated game
    move; the result is the number of simulated moves. -/
def rollMoves (B j : Nat) : Nat → List Nat → Nat
  | 0, _ => 0
  | f + 1, P => match polStepN B j P with
    | none => 0
    | some Q => rollMoves B j f Q + 1

theorem rolloutMoves_some {j : Nat} {p q : List Nat} (h : policyStep j p = some q) :
    rolloutMoves j p = rolloutMoves j q + 1 := by
  rw [rolloutMoves]; split <;> simp_all

theorem rolloutMoves_none {j : Nat} {p : List Nat} (h : policyStep j p = none) : rolloutMoves j p = 0 := by
  rw [rolloutMoves]; split <;> simp_all

/-- The network-executed rollout performs exactly the structured rollout. -/
theorem rollMoves_eq {B j : Nat} : ∀ (f : Nat) (P : List Nat), Width B P → P.sum ≤ f →
    rollMoves B j (f + 1) P = rolloutMoves j P
  | f, P, hw, hf => by
    simp only [rollMoves, polStepN_eq hw]
    cases h : policyStep j P with
    | none => rw [rolloutMoves_none h]
    | some Q =>
      simp only
      have hm := policyStep_move h
      have hlt := move_sum_lt hm
      rw [rolloutMoves_some h]
      cases f with
      | zero => omega
      | succ f => rw [rollMoves_eq f Q (width_move hw hm) (by omega)]

/-- The rollout outcome observed by the player (first player wins iff odd). -/
def rollOut (B j : Nat) (P : List Nat) : Bool := (rollMoves B j (P.sum + 1) P).testBit 0

theorem rollOut_eq {B j : Nat} {P : List Nat} (hw : Width B P) : rollOut B j P = rolloutWinner j P := by
  rw [rollOut, rollMoves_eq P.sum P hw (Nat.le_refl _), rolloutWinner_eq]

/-- The multi-head player: run the B network rollouts, feed their outcomes and the board
    to the compiled multi-head network, decode its output wires and apply the move. -/
def mhSelect (B : Nat) (P : List Nat) : Option (List Nat) :=
  applyM P (netBinSem (mhNet B P.length (rIdx P.length)) P.length (rIdx P.length) B
    (obsIn B P.length P (fun j => rollOut B j P)))

theorem mhSelect_eq {B : Nat} {P : List Nat} (hw : Width B P) : mhSelect B P = ctrlSel P := by
  have ho : (fun j => rollOut B j P) = outcomes P := by funext j; exact rollOut_eq hw
  unfold mhSelect ctrlSel
  rw [ho, mhNet_correct (r := rIdx P.length) (width_log _) rfl hw]
  cases decisionMove P <;> rfl

theorem wins_congr {B : Nat} {sel sel' : List Nat → Option (List Nat)}
    (h : ∀ Q, Width B Q → sel Q = sel' Q) {P : List Nat} (hw : Width B P) (hP : Wins sel' P) :
    Wins sel P := by
  induction hP with
  | intro p q hsel hm _ ih =>
    refine Wins.intro p q (by rw [h p hw, hsel]) hm (fun r hr => ih r hr ?_)
    exact width_move (width_move hw hm) hr

/-- MULTI-HEAD WHOLE-GAME THEOREM: from every nonzero position of bit width B, the player
    driven by network-executed rollouts and the compiled multi-head network wins against
    every legal opponent. -/
theorem mhSelect_wins {B : Nat} {P : List Nat} (hw : Width B P) (h : nimSum P ≠ 0) : Wins (mhSelect B) P :=
  wins_congr (fun Q hQ => mhSelect_eq hQ) hw (ctrl_wins P h)

/-- Terminal behaviour: the player halts exactly on terminal boards, and every selected
    move is legal and keeps the bit width. -/
theorem mhSelect_terminal {B : Nat} {P : List Nat} (hw : Width B P) :
    (mhSelect B P = none ↔ Terminal P) ∧
    (∀ R, mhSelect B P = some R → Move P R ∧ Width B R) := by
  rw [mhSelect_eq hw]
  obtain ⟨h1, h2, _⟩ := decision_correct P
  refine ⟨?_, fun R hR => ?_⟩
  · unfold ctrlSel; rw [← h1]; cases decisionMove P <;> simp
  · unfold ctrlSel at hR
    cases hd : decisionMove P with
    | none => rw [hd] at hR; cases hR
    | some m =>
      obtain ⟨i, v⟩ := m
      rw [hd] at hR; simp only [Option.map_some, Option.some.injEq] at hR; subst hR
      obtain ⟨x, _, _, hmv⟩ := h2 i v hd
      exact ⟨hmv, width_move hw hmv⟩

/-- ROLLOUT COST: the B network rollouts perform exactly totalRolloutMoves B P simulated
    game moves (one network evaluation each), at most B·Σ heaps ≤ B·N·(2^B − 1). -/
theorem mhSelect_cost {B : Nat} {P : List Nat} (hw : Width B P) :
    ((List.range B).map (fun j => rollMoves B j (P.sum + 1) P)).sum = totalRolloutMoves B P ∧
    totalRolloutMoves B P ≤ B * P.sum ∧ B * P.sum ≤ B * (P.length * (2 ^ B - 1)) := by
  have e : ((List.range B).map (fun j => rollMoves B j (P.sum + 1) P)) =
      (List.range B).map (fun j => rolloutMoves j P) :=
    List.map_congr_left (fun j _ => rollMoves_eq P.sum P hw (Nat.le_refl _))
  refine ⟨by rw [e]; rfl, ?_, ?_⟩
  · unfold totalRolloutMoves
    have := sum_map_le_mem (l := List.range B) (f := fun j => rolloutMoves j P) (g := fun _ => P.sum)
      (fun j _ => by
        show rolloutMoves j P ≤ P.sum
        rw [rolloutMoves_eq]; unfold rolloutCount
        have h := sum_map_le_mem (l := P) (f := heapCount j) (g := id) (fun h _ => heapCount_le j h)
        simpa using h)
    rw [List.map_const', List.sum_replicate_nat, List.length_range] at this
    exact this
  · apply Nat.mul_le_mul_left
    have h : ∀ x ∈ P, x ≤ 2 ^ B - 1 := fun x hx => by have := hw x hx; omega
    have := sum_map_le_mem (l := P) (f := id) (g := fun _ => 2 ^ B - 1) h
    simp [List.map_const', List.sum_replicate_nat] at this
    simpa [Nat.mul_comm] using this

/-! ## C. Recurrent replay strategy with the threshold controller -/

/-- The first move output in a list of controller outputs. -/
def moveOf : List COut → Option (Nat × Nat)
  | [] => none
  | COut.move m :: _ => m
  | COut.summary _ _ :: rest => moveOf rest

/-- One decision: feed rows, SEP, the same rows again (replay supplied by the environment),
    SEP to the threshold controller; return the new state vector and the emitted move. -/
def decide (B r : Nat) (v : Nat → Bool) (P : List Nat) : (Nat → Bool) × Option (Nat × Nat) :=
  ((trun B r v (dtoks P)).1, moveOf (trun B r v (dtoks P)).2)

/-- Machine state after a decision on board P. -/
def afterState (P : List Nat) : CState := ⟨false, 0, nimSum P, true, nimSum P, 0, none, none⟩

theorem decide_spec {B r N : Nat} (hN : N < 2 ^ r) {s : CState} (hs : Idle s) (hf : Fits B N s)
    {P : List Nat} (hP : P.length = N) (hw : Width B P) :
    decide B r (sbits B r s) P = (sbits B r (afterState P), decisionMove P) ∧
    (∀ st ∈ crunStates s (dtoks P), FitsR B r st) := by
  have hstream : stream [P] = dtoks P := by simp [stream]
  have hfits := stream_fits s hs hf [P] (by simp [hP, hw])
  rw [hstream] at hfits
  have hall := allDec_of_fits (B := B) hN s (dtoks P) hfits (by
    rw [← hstream]; exact tok_bound_stream [P] (by simp [hw]))
  have hrun := trun_refines s (dtoks P) hall
  have hdec := crun_decision s hs P
  refine ⟨?_, fun st hst => ?_⟩
  · unfold decide; rw [hrun, hdec]; rfl
  · obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hfits st hst
    exact ⟨h1, h2, h3, by omega, fun i v hiv => ⟨by have := (h5 i v hiv).1; omega, (h5 i v hiv).2⟩,
      fun i v hiv => ⟨by have := (h6 i v hiv).1; omega, (h6 i v hiv).2⟩⟩

theorem afterState_ok {B N : Nat} {P : List Nat} (hw : Width B P) :
    Idle (afterState P) ∧ Fits B N (afterState P) := by
  have h := nimSum_lt hw
  refine ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
  refine ⟨Nat.two_pow_pos B, h, h, Nat.zero_le _, ?_, ?_⟩ <;> simp [afterState]

/-- Stateful interaction predicate (player to move at P; the controller holds the
    canonical encoding of the semantic state s).  At each decision: every intermediate
    controller state fits the registers, the emitted move is applied to the board and is
    legal, the controller's new vector encodes `afterState P` (the stored summary feeds
    the next decision), and after every legal opponent reply the interaction continues. -/
inductive ReplayWins (B r : Nat) : CState → List Nat → Prop
  | intro (s : CState) (P R : List Nat) :
      (∀ st ∈ crunStates s (dtoks P), FitsR B r st) →
      applyM P (decide B r (sbits B r s) P).2 = some R → Move P R →
      (decide B r (sbits B r s) P).1 = sbits B r (afterState P) →
      (∀ P', Move R P' → ReplayWins B r (afterState P) P') → ReplayWins B r s P

theorem replayWins_sound {B r : Nat} {s : CState} {P : List Nat} (h : ReplayWins B r s P) : Win P := by
  induction h with
  | intro s P R _ _ hm _ _ ih => exact Win.intro P R hm (Lose.intro R ih)

/-- RECURRENT WHOLE-GAME THEOREM: with N < 2^r heaps of width B, from any idle controller
    state whose registers fit (the initial state, and every state reached after earlier
    decisions), the threshold controller driven by the replay protocol wins from every
    nonzero position against every legal opponent; the move applied is exactly the
    emitted one; all controller states over the whole interaction fit the registers. -/
theorem replay_wins {B r N : Nat} (hN : N < 2 ^ r) : ∀ (P : List Nat), P.length = N → Width B P →
    nimSum P ≠ 0 → ∀ s, Idle s → Fits B N s → ReplayWins B r s P := by
  intro P
  induction P using (measure List.sum).wf.induction with
  | h P ih =>
    intro hP hw h0 s hs hf
    obtain ⟨hdec, hfit⟩ := decide_spec hN hs hf hP hw
    obtain ⟨i, v, hd, hz⟩ := (decision_correct P).2.2 h0
    obtain ⟨x, _, _, hmv⟩ := (decision_correct P).2.1 i v hd
    refine ReplayWins.intro s P (P.set i v) hfit (by rw [hdec, hd]; rfl) hmv (by rw [hdec]) ?_
    intro P' hm'
    have hlt1 := move_sum_lt hmv
    have hlt2 := move_sum_lt hm'
    obtain ⟨hidle, hfit'⟩ := afterState_ok (N := N) hw
    exact ih P' (by show P'.sum < P.sum; omega) (by rw [move_length hm', move_length hmv, hP])
      (width_move (width_move hw hmv) hm') (move_from_zero hm' hz) _ hidle hfit'

/-- GAME START from an arbitrary bit state: one reset token produces the encoding of the
    initial state, from which the replay strategy wins. -/
theorem replay_game {B r N : Nat} (hN : N < 2 ^ r) (v : Nat → Bool) {P : List Nat} (hP : P.length = N)
    (hw : Width B P) (h0 : nimSum P ≠ 0) :
    (tstep B r v Tok.reset).1 = sbits B r cinit ∧ ReplayWins B r cinit P := by
  refine ⟨by rw [tstep_reset], ?_⟩
  exact replay_wins hN P hP hw h0 cinit cinit_idle
    ⟨Nat.two_pow_pos B, Nat.two_pow_pos B, Nat.two_pow_pos B, Nat.zero_le _, by simp [cinit], by simp [cinit]⟩

/-- Update accounting: each decision uses exactly 2N + 2 controller updates; a game adds
    one reset update; the state has 4 + 5B + 3r bits (7 + 5B + 3·log₂N for r = log₂N + 1). -/
theorem replay_counts (B N : Nat) (P : List Nat) (hP : P.length = N) :
    (dtoks P).length = 2 * N + 2 ∧ (Tok.reset :: dtoks P).length = 2 * N + 3 ∧
    stateWidth B (N.log2 + 1) = 7 + 5 * B + 3 * N.log2 := by
  refine ⟨by rw [dtoks_length, hP], by simp [dtoks_length, hP], (counter_width (B := B) N).2⟩


/-! ## Axiom audit -/

#print axioms move_length
#print axioms twoFrame_sound
#print axioms restReply_step
#print axioms twoFrame_wins
#print axioms twoFrame_terminal
#print axioms twoFrame_lose
#print axioms polStepN_eq
#print axioms policyStep_move
#print axioms rolloutMoves_some
#print axioms rolloutMoves_none
#print axioms rollMoves_eq
#print axioms rollOut_eq
#print axioms mhSelect_eq
#print axioms wins_congr
#print axioms mhSelect_wins
#print axioms mhSelect_terminal
#print axioms mhSelect_cost
#print axioms decide_spec
#print axioms afterState_ok
#print axioms replayWins_sound
#print axioms replay_wins
#print axioms replay_game
#print axioms replay_counts
end WholeGame
end NimAudit
