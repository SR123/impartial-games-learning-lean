import RolloutExec

/- Phase 6, Priority 1c: the paper's Proposition prop:bypass-interfaces, the barrier side,
   and the recurrent-history caveat.  Written by Claude (10 October 2026).
   Lean 4.26.0, core/Std only.

   Each bypass is stated as: (a) family certificates for its SHALLOW COMPONENT (formula
   family and threshold-network family, the same objects as in (b)); (b) the component's
   semantics on its declared domain; (c) the complete strategy against every legal
   opponent, with its protocol and time/count bounds.  Polynomial size and constant depth
   are claims about ONE component evaluation; they never bound the number of sequential
   evaluations.

   WHICH HYPOTHESIS OF THE SINGLE-FRAME BARRIER EACH BYPASS RELAXES.
   (i)   two-frame restoration keeps one shallow evaluation per decision but changes the
         INPUT: a promised pair (nim(Q) = 0, legal Q → Q'), not a single arbitrary board.
         The circuit reads only the 2BN bits of the two frames; no global nim-sum enters.
   (ii)  multi-head keeps every component shallow but performs B SEQUENTIAL rollouts
         (Σ_j (L_j + 1) clocked policy steps, unbounded in N) before the readout.
   (iii) recurrence keeps one update shallow but performs 2N + 2 SEQUENTIAL updates.
   Under ParityNotAC0 the complete board-to-move maps of (ii) and (iii) are not AC0
   families (bypass_barriers); (i) is not a counterexample because the promised frame
   carries the parity and cannot itself be produced by an AC0 family. -/

namespace NimAudit
namespace Bypass

open Game Rollout Prob Attain Recurrent AC0 AC0.Circ CorrBridge AttainCircuit Bridge SelectCircuit
  BinReadout Controller ControllerBits PriorityEncoder ThresholdNet ThresholdInst FiniteNet WholeGame
  Family Barrier RolloutExec

/-! ## (i) Two-frame restoration -/

/-- The restoration circuit's input is exactly the two frames (Q at wires < BN, Q' after). -/
theorem tf_frames (B N : Nat) (Q Q' : List Nat) (j : Nat) :
    LocalRestore.tf B N Q Q' j = if j < B * N then boardBits B Q j else boardBits B Q' (j - B * N) := rfl

theorem bypass_twoFrame :
    AC0Fam restAdm restLen (fun i => bForms (restS i)) 20 ∧
    NetFam restAdm restLen restN 1 42 ∧
    (∀ (B N : Nat) (Q Q' : List Nat), Q.length = N → Q'.length = N → Width B Q → Width B Q' →
      nimSum Q = 0 → Move Q Q' →
      ∃ i v, netBinSem (restN (B, N)) N (rIdx N) B (LocalRestore.tf B N Q Q') = some (i, v) ∧
        Move Q' (Q'.set i v) ∧ nimSum (Q'.set i v) = 0 ∧ restore Q Q' = some (Q'.set i v)) ∧
    (∀ (B : Nat) (Q : List Nat), Width B Q → nimSum Q = 0 → TwoFrameWins (restReply B) Q ∧ Lose Q) := by
  refine ⟨rest_ac0, rest_net, fun B N Q Q' hQ hQ' hw hw' h0 hm => ?_, fun B Q hw h0 =>
    ⟨twoFrame_wins Q hw h0, twoFrame_lose hw h0⟩⟩
  obtain ⟨i, v, _, h2, h3, h4, h5⟩ := rest_semantics hQ hQ' hw hw' h0 hm
  exact ⟨i, v, h2, h4, h5, h3⟩

/-- The two-frame strategy uses exactly the certified network on the two frames. -/
theorem restReply_uses_restN (B : Nat) (Q Q' : List Nat) :
    restReply B Q Q' = applyM Q' (netBinSem (restN (B, Q'.length)) Q'.length (rIdx Q'.length) B
      (LocalRestore.tf B Q'.length Q Q')) := rfl

/-! ## (ii) Multi-head rollouts with finite-register execution -/

theorem bypass_multiHead :
    AC0Fam polAdm polLen (fun i => bForms (polS i)) 17 ∧ NetFam polAdm polLen polN 1 36 ∧
    AC0Fam polAdm stepLen stepF 28 ∧ NetFam polAdm stepLen stepN 1 58 ∧
    AC0Fam mhAdm mhLen (fun i => bForms (mhS i)) 19 ∧ NetFam mhAdm mhLen mhN 1 40 ∧
    (∀ (B : Nat) (P : List Nat), Width B P →
      mhExec B P = decisionMove P ∧ (nimSum P ≠ 0 → Wins (mhExecSel B) P) ∧
      (∀ j, outBit B j P = rolloutWinner j P ∧ polEvals B j P = rolloutMoves j P + 1) ∧
      ((List.range B).map (fun j => polEvals B j P)).sum = totalRolloutMoves B P + B ∧
      totalRolloutMoves B P ≤ B * P.sum ∧ B * P.sum ≤ B * (P.length * (2 ^ B - 1)) ∧
      totalRolloutMoves B P + B ≤ B * clockBound B P.length) := by
  refine ⟨pol_ac0, pol_net, step_ac0, step_net, mh_ac0, mh_net, fun B P hw => ?_⟩
  obtain ⟨_, h2, h3⟩ := mhSelect_cost hw
  obtain ⟨e1, e2, e3⟩ := mhExec_evals hw
  exact ⟨mhExec_eq hw, mhExec_wins hw, fun j => ⟨outBit_eq hw, e1 j⟩, e2, h2, h3, e3⟩

/-! ## (iii) Persistent recurrence with replay -/

theorem bypass_recurrent :
    AC0Fam ctrlAdm ctrlLen ctrlF 8 ∧ NetFam ctrlAdm ctrlLen ctrlN 1 18 ∧
    (∀ (B N : Nat) (v : Nat → Bool) (t : Tok), tstep B (rIdx N) v t = bstep B (rIdx N) v t) ∧
    (∀ (B N : Nat) (v : Nat → Bool) (P : List Nat), P.length = N → Width B P → nimSum P ≠ 0 →
      (tstep B (rIdx N) v Tok.reset).1 = sbits B (rIdx N) cinit ∧ ReplayWins B (rIdx N) cinit P) ∧
    (∀ (B N : Nat) (P : List Nat), P.length = N →
      (dtoks P).length = 2 * N + 2 ∧ (Tok.reset :: dtoks P).length = 2 * N + 3 ∧
      stateWidth B (rIdx N) = 7 + 5 * B + 3 * N.log2 ∧ inWidth B (rIdx N) = stateWidth B (rIdx N) + (2 + B)) := by
  refine ⟨ctrl_ac0, ctrl_net, fun B N v t => tstep_eq _ _ v t, fun B N v P hP hw h0 =>
    replay_game (rIdx_counter N) v hP hw h0, fun B N P hP => ?_⟩
  obtain ⟨a, b, c⟩ := replay_counts B N P hP
  exact ⟨a, b, c, (ctrl_widths B N).1⟩

/-- PROPOSITION prop:bypass-interfaces (all three parts): for each bypass the formula
    family AND the {0,1}-weight threshold-network family (W = 1) of its shallow components,
    and the complete strategy with its protocol and count bounds. -/
theorem prop_bypass_interfaces :
    (AC0Fam restAdm restLen (fun i => bForms (restS i)) 20 ∧ NetFam restAdm restLen restN 1 42 ∧
      ∀ (B : Nat) (Q : List Nat), Width B Q → nimSum Q = 0 → TwoFrameWins (restReply B) Q) ∧
    (AC0Fam polAdm polLen (fun i => bForms (polS i)) 17 ∧ NetFam polAdm polLen polN 1 36 ∧
      AC0Fam polAdm stepLen stepF 28 ∧ NetFam polAdm stepLen stepN 1 58 ∧
      AC0Fam mhAdm mhLen (fun i => bForms (mhS i)) 19 ∧ NetFam mhAdm mhLen mhN 1 40 ∧
      ∀ (B : Nat) (P : List Nat), Width B P → nimSum P ≠ 0 →
        Wins (mhExecSel B) P ∧ totalRolloutMoves B P ≤ B * (P.length * (2 ^ B - 1)) ∧
        ((List.range B).map (fun j => polEvals B j P)).sum = totalRolloutMoves B P + B) ∧
    (AC0Fam ctrlAdm ctrlLen ctrlF 8 ∧ NetFam ctrlAdm ctrlLen ctrlN 1 18 ∧
      ∀ (B N : Nat) (v : Nat → Bool) (P : List Nat), P.length = N → Width B P → nimSum P ≠ 0 →
        (tstep B (rIdx N) v Tok.reset).1 = sbits B (rIdx N) cinit ∧ ReplayWins B (rIdx N) cinit P ∧
        (dtoks P).length = 2 * N + 2 ∧ stateWidth B (rIdx N) = 7 + 5 * B + 3 * N.log2) := by
  obtain ⟨t1, t2, _, t4⟩ := bypass_twoFrame
  obtain ⟨m1, m2, m3, m4, m5, m6, m7⟩ := bypass_multiHead
  obtain ⟨r1, r2, _, r4, r5⟩ := bypass_recurrent
  refine ⟨⟨t1, t2, fun B Q hw h0 => (t4 B Q hw h0).1⟩, ⟨m1, m2, m3, m4, m5, m6, fun B P hw h0 => ?_⟩,
    ⟨r1, r2, fun B N v P hP hw h0 => ⟨(r4 B N v P hP hw h0).1, (r4 B N v P hP hw h0).2, (r5 B N P hP).1,
      (r5 B N P hP).2.2.1⟩⟩⟩
  obtain ⟨_, hwin, _, h4, h5, h6, _⟩ := m7 B P hw
  exact ⟨hwin h0, Nat.le_trans h5 h6, h4⟩

/-! ## The barrier side -/

theorem mhExec_winsOnEnc : WinsOnEnc (mhExec 2) :=
  winsOnEnc_congr (fun y => mhExec_eq (width2_encode y)) decisionMove_winsOnEnc

/-- ALL-BOARDS FORMS for the executed multi-head map and for network families: a family
    agreeing with mhExec 2 (resp. recMove 2) on every width-2 board of m+1 heaps agrees on
    the encoding family, so the barriers apply. -/
theorem no_ac0_mhExec_allBoards (hard : ParityNotAC0) (S : Nat → BCirc) (r : Nat → Nat) (d : Nat)
    (hfam : AC0Fam encAdm encLen (fun m => bForms (S m)) d)
    (hidx : ∀ m, 1 ≤ m → (S m).idx.length = r m ∧ (S m).val.length = 2 ∧ m + 1 ≤ 2 ^ r m)
    (hcomp : ∀ m, 1 ≤ m → ∀ P : List Nat, P.length = m + 1 → Width 2 P →
      ParityCircuit.binMove (S m) (m + 1) P = mhExec 2 P) : False :=
  no_ac0_mh_allBoards hard S r d hfam hidx (fun m hm P hP hw => (hcomp m hm P hP hw).trans (mhExec_eq_mhMove hw))

theorem no_net_mhExec_allBoards (hard : ParityNotAC0) (net : Nat → List Layer) (r : Nat → Nat) (W L : Nat)
    (hnet : NetFam encAdm encLen net W L) (hr : ∀ m, 1 ≤ m → m + 1 ≤ 2 ^ r m)
    (hcomp : ∀ m, 1 ≤ m → ∀ P : List Nat, P.length = m + 1 → Width 2 P →
      netBinSem (net m) (m + 1) (r m) 2 (boardBits 2 P) = mhExec 2 P) : False :=
  no_net_mh hard net r W L hnet hr (fun m hm y hy => by
    rw [← mhExec_eq_mhMove (width2_encode y)]
    exact hcomp m hm _ (by rw [ParityCircuit.length_encode, hy]) (width2_encode y))

theorem no_net_rec_allBoards (hard : ParityNotAC0) (net : Nat → List Layer) (r : Nat → Nat) (W L : Nat)
    (hnet : NetFam encAdm encLen net W L) (hr : ∀ m, 1 ≤ m → m + 1 ≤ 2 ^ r m)
    (hcomp : ∀ m, 1 ≤ m → ∀ P : List Nat, P.length = m + 1 → Width 2 P →
      netBinSem (net m) (m + 1) (r m) 2 (boardBits 2 P) = recMove 2 P) : False :=
  no_net_rec hard net r W L hnet hr (fun m hm y hy =>
    hcomp m hm _ (by rw [ParityCircuit.length_encode, hy]) (width2_encode y))

/-- BYPASS BARRIERS.  Under ParityNotAC0:
    (a) the complete finite-register multi-head map mhExec and the complete recurrent map
        recMove are not computed by any AC0 formula family on the encoding family;
    (b) nor by any fixed-scale network family (fixed W, constant layers, polynomial size);
    (c) the promised two-frame map does compute parity on promised pairs, but no AC0
        family produces the promised predecessor from the single frame. -/
theorem bypass_barriers (hard : ParityNotAC0) :
    (∀ (S : Nat → BCirc) (r : Nat → Nat) (d : Nat), AC0Fam encAdm encLen (fun m => bForms (S m)) d →
      (∀ m, 1 ≤ m → (S m).idx.length = r m ∧ (S m).val.length = 2 ∧ m + 1 ≤ 2 ^ r m) →
      ¬ (∀ m, 1 ≤ m → ∀ y : List Bool, y.length = m → ParityCircuit.binMove (S m) (m + 1) (Game.encode y) = mhExec 2 (Game.encode y))) ∧
    (∀ (S : Nat → BCirc) (r : Nat → Nat) (d : Nat), AC0Fam encAdm encLen (fun m => bForms (S m)) d →
      (∀ m, 1 ≤ m → (S m).idx.length = r m ∧ (S m).val.length = 2 ∧ m + 1 ≤ 2 ^ r m) →
      ¬ (∀ m, 1 ≤ m → ∀ y : List Bool, y.length = m → ParityCircuit.binMove (S m) (m + 1) (Game.encode y) = recMove 2 (Game.encode y))) ∧
    (∀ (net : Nat → List Layer) (r : Nat → Nat) (W L : Nat), NetFam encAdm encLen net W L →
      (∀ m, 1 ≤ m → m + 1 ≤ 2 ^ r m) →
      ¬ (∀ m, 1 ≤ m → ∀ y : List Bool, y.length = m →
        netBinSem (net m) (m + 1) (r m) 2 (boardBits 2 (Game.encode y)) = mhExec 2 (Game.encode y))) ∧
    (∀ (net : Nat → List Layer) (r : Nat → Nat) (W L : Nat), NetFam encAdm encLen net W L →
      (∀ m, 1 ≤ m → m + 1 ≤ 2 ^ r m) →
      ¬ (∀ m, 1 ≤ m → ∀ y : List Bool, y.length = m →
        netBinSem (net m) (m + 1) (r m) 2 (boardBits 2 (Game.encode y)) = recMove 2 (Game.encode y))) ∧
    (∀ (G : Nat → List Circ) (d : Nat), AC0Fam encAdm (fun m => m) G d →
      ¬ (∀ m, 1 ≤ m → ∀ y : List Bool, y.length = m → ∃ Q : List Nat, Q.length = m + 1 ∧
        nimSum Q = 0 ∧ Move Q (Game.encode y) ∧
        ∀ w, w < 2 * (m + 1) → eval (vfun y) (getC (G m) w) = boardBits 2 Q w)) := by
  refine ⟨fun S r d hf hi hc => barrier_map hard _ mhExec_winsOnEnc S r d hf hi hc,
    fun S r d hf hi hc => no_ac0_rec hard S r d hf hi hc,
    fun net r W L hn hr hc => barrier_net hard _ mhExec_winsOnEnc net r W L hn hr hc,
    fun net r W L hn hr hc => no_net_rec hard net r W L hn hr hc,
    fun G d hf hp => no_ac0_predecessor hard G d hf hp⟩

/-- On every promised pair over the encoding family the certified two-frame network
    outputs (0, parity y): the parity is read off the supplied predecessor. -/
theorem twoFrame_promised_parity (y : List Bool) {Q : List Nat} (hQ : Q.length = y.length + 1)
    (hw : Width 2 Q) (h0 : nimSum Q = 0) (hm : Move Q (Game.encode y)) :
    netBinSem (restN (2, y.length + 1)) (y.length + 1) (rIdx (y.length + 1)) 2
      (LocalRestore.tf 2 (y.length + 1) Q (Game.encode y)) = some (0, (parity y).toNat) ∧
    lowXorOr Q (Game.encode y) = parity y :=
  ⟨twoFrame_on_encoding y hQ hw h0 hm, promised_pred_parity y h0 hm⟩

/-! ## Recurrent history caveat -/

theorem one_transition_diff {Q Q' : List Nat} (hm : Move Q Q') :
    ∃ pre x post z, Q = pre ++ x :: post ∧ Q' = pre ++ z :: post ∧ z < x ∧ nimSum Q ^^^ nimSum Q' = x ^^^ z := by
  obtain ⟨pre, x, post, z, h1, h2, h3⟩ := move_split hm
  refine ⟨pre, x, post, z, h1, h2, h3, ?_⟩
  rw [h1, h2]; exact one_heap_difference pre post x z

/-- The controller's outputs on two consecutively supplied boards: the second summary's
    difference is nim(Q) ⊕ nim(Q'). -/
theorem ctrlOuts_two (v : Bool) (q : Nat) (Q Q' : List Nat) (rest : List (List Nat)) :
    (ctrlOuts v q (Q :: Q' :: rest))[2]? = some (COut.summary (nimSum Q') (some (nimSum Q ^^^ nimSum Q'))) := by
  simp [ctrlOuts]

/-- ONE-LEGAL-TRANSITION FORM: when consecutive supplied boards differ by one legal move,
    the threshold controller reports exactly that heap's XOR difference. -/
theorem diff_of_transition {B N : Nat} {Q Q' : List Nat} (hN : N < 2 ^ rIdx N) (hQ : Q.length = N)
    (hQ' : Q'.length = N) (hw : Width B Q) (hw' : Width B Q') (hm : Move Q Q') :
    ∃ pre x post z, Q = pre ++ x :: post ∧ Q' = pre ++ z :: post ∧
      (trun B (rIdx N) (sbits B (rIdx N) cinit) (stream [Q, Q'])).2[2]? =
        some (COut.summary (nimSum Q') (some (x ^^^ z))) := by
  obtain ⟨pre, x, post, z, h1, h2, _, h4⟩ := one_transition_diff hm
  refine ⟨pre, x, post, z, h1, h2, ?_⟩
  rw [trun_stream hN [Q, Q'] (by
    intro P hP; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hP
    rcases hP with rfl | rfl
    · exact ⟨hQ, hw⟩
    · exact ⟨hQ', hw'⟩), ctrlOuts_two, h4]

/-- POST-MOVE BOARD SUPPLIED: if the protocol also supplies the player's own post-move
    board R (nim(R) = 0) before the opponent's board P', the reported difference at P'
    is the opponent's one-heap delta x ⊕ z, which equals nim(P') (the restoration target). -/
theorem diff_with_postMove {B N : Nat} {P0 R P' : List Nat} (hN : N < 2 ^ rIdx N)
    (h0 : P0.length = N ∧ Width B P0) (h1 : R.length = N ∧ Width B R) (h2 : P'.length = N ∧ Width B P')
    (hz : nimSum R = 0) (hm : Move R P') :
    ∃ pre x post z, R = pre ++ x :: post ∧ P' = pre ++ z :: post ∧
      (trun B (rIdx N) (sbits B (rIdx N) cinit) (stream [P0, R, P'])).2[4]? =
        some (COut.summary (nimSum P') (some (x ^^^ z))) ∧ x ^^^ z = nimSum P' := by
  obtain ⟨pre, x, post, z, e1, e2, _, e4⟩ := one_transition_diff hm
  refine ⟨pre, x, post, z, e1, e2, ?_, by rw [← e4, hz, Nat.zero_xor]⟩
  rw [trun_stream hN [P0, R, P'] (by
    intro P hP; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hP
    rcases hP with rfl | rfl | rfl
    · exact h0
    · exact h1
    · exact h2), ← e4]
  simp [ctrlOuts]

/-- DECISION-TIME BOARDS ONLY: the reported difference spans two moves and is in general
    NOT the opponent's delta.  Concretely: P0 = [1,2] (player to move), the player moves to
    R = [1,1] (nim 0), the opponent moves to P1 = [0,1] (delta 1); supplying only P0 and P1,
    the threshold controller reports difference 2. -/
theorem diff_decision_only :
    Move [1, 2] [1, 1] ∧ nimSum [1, 1] = 0 ∧ Move [1, 1] [0, 1] ∧ (1 ^^^ 0 : Nat) = 1 ∧
    (trun 2 (rIdx 2) (sbits 2 (rIdx 2) cinit) (stream [[1, 2], [0, 1]])).2[2]? =
      some (COut.summary 1 (some 2)) := by
  refine ⟨⟨[1], 2, [], 1, rfl, rfl, by decide⟩, by decide, ⟨[], 1, [1], 0, rfl, rfl, by decide⟩, by decide, ?_⟩
  rw [trun_stream (rIdx_counter 2) _ (by
    intro P hP; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hP
    rcases hP with rfl | rfl
    · exact ⟨rfl, by intro x hx; simp at hx; omega⟩
    · exact ⟨rfl, by intro x hx; simp at hx; omega⟩), ctrlOuts_two]
  rfl

/-- The replay strategy's MOVE does not depend on the stored history: from any idle
    fitting state it equals decisionMove of the current board (recomputed by the scan). -/
theorem replay_move_current {B r N : Nat} (hN : N < 2 ^ r) {s : CState} (hs : Idle s) (hf : Fits B N s)
    {P : List Nat} (hP : P.length = N) (hw : Width B P) :
    (WholeGame.decide B r (sbits B r s) P).2 = decisionMove P :=
  by rw [(decide_spec hN hs hf hP hw).1]

/-! ## Axiom audit -/

#print axioms tf_frames
#print axioms bypass_twoFrame
#print axioms restReply_uses_restN
#print axioms bypass_multiHead
#print axioms bypass_recurrent
#print axioms prop_bypass_interfaces
#print axioms mhExec_winsOnEnc
#print axioms no_ac0_mhExec_allBoards
#print axioms no_net_mhExec_allBoards
#print axioms no_net_rec_allBoards
#print axioms bypass_barriers
#print axioms twoFrame_promised_parity
#print axioms one_transition_diff
#print axioms ctrlOuts_two
#print axioms diff_of_transition
#print axioms diff_with_postMove
#print axioms diff_decision_only
#print axioms replay_move_current


