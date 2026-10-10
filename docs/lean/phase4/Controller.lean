import NimRecurrent
import AttainCircuit

/- Phase 4, Priority 3: one explicit two-pass recurrent controller.  Written by
   Claude (10 October 2026).  Lean 4.26.0, core/Std only.

   Tokens: row x | sep | reset.  Modes: scan / replay.  Registers: acc, prev, valid
   (summary part, as in phase 3), sig (stored summary fed to replay), idx (replay
   counter), sel and fnz (selected cancelling move and fallback move).
     scan,  row x : acc := acc XOR x
     scan,  sep   : emit summary (acc, diff if valid); prev := acc; valid := true;
                    sig := acc; acc := 0; idx := 0; sel := fnz := none; mode := replay
     replay,row x : replay step with summary sig (phase-3 `replayStep`)
     replay,sep   : emit move (sel, else fnz, else halt); idx := 0; sel := fnz := none;
                    mode := scan
     reset        : back to the initial state (between games)
   Input protocol for one decision on board P: rows of P, sep, rows of P again, sep.
   Proved here: the combined protocol (summary THEN the move computed from the stored
   summary), legality / zero successor / terminal handling, winning against every
   legal opponent via the game semantics, reset, reachable-register bounds (no counter
   overflow).  The bit-level per-update circuits and their refinement are in
   ControllerBits.lean. -/

namespace NimAudit
namespace Controller

open Game Rollout Prob Attain Recurrent AC0 AC0.Circ

inductive Tok where
  | row (x : Nat)
  | sep
  | reset

structure CState where
  replayMode : Bool
  acc : Nat
  prev : Nat
  valid : Bool
  sig : Nat
  idx : Nat
  sel : Option (Nat × Nat)
  fnz : Option (Nat × Nat)

inductive COut where
  | summary (s : Nat) (diff : Option Nat)
  | move (m : Option (Nat × Nat))

def cinit : CState := ⟨false, 0, 0, false, 0, 0, none, none⟩

/-- One update of the controller. -/
def cstep (s : CState) : Tok → CState × Option COut
  | .reset => (cinit, none)
  | .row x =>
    if s.replayMode then
      (⟨s.replayMode, s.acc, s.prev, s.valid, s.sig, (replayStep s.sig ⟨s.idx, s.sel, s.fnz⟩ x).idx,
        (replayStep s.sig ⟨s.idx, s.sel, s.fnz⟩ x).sel, (replayStep s.sig ⟨s.idx, s.sel, s.fnz⟩ x).fnz⟩,
       none)
    else (⟨s.replayMode, s.acc ^^^ x, s.prev, s.valid, s.sig, s.idx, s.sel, s.fnz⟩, none)
  | .sep =>
    if s.replayMode then
      (⟨false, s.acc, s.prev, s.valid, s.sig, 0, none, none⟩, some (.move (firstSome s.sel s.fnz)))
    else
      (⟨true, 0, s.acc, true, s.acc, 0, none, none⟩,
       some (.summary s.acc (if s.valid then some (s.prev ^^^ s.acc) else none)))

def crun : CState → List Tok → CState × List COut
  | s, [] => (s, [])
  | s, t :: ts => ((crun (cstep s t).1 ts).1, (cstep s t).2.toList ++ (crun (cstep s t).1 ts).2)

/-- All states visited (initial state included). -/
def crunStates : CState → List Tok → List CState
  | s, [] => [s]
  | s, t :: ts => s :: crunStates (cstep s t).1 ts

/-- The tokens of one decision: scan, separator, replay, separator. -/
def dtoks (P : List Nat) : List Tok := P.map Tok.row ++ [Tok.sep] ++ P.map Tok.row ++ [Tok.sep]

def stream (Ps : List (List Nat)) : List Tok := Ps.flatMap dtoks

/-- Games separated by reset tokens (a reset precedes every game). -/
def gameStream (gs : List (List (List Nat))) : List Tok := gs.flatMap (fun g => Tok.reset :: stream g)

/-- Idle: scan mode with empty accumulator and cleared replay registers. -/
def Idle (s : CState) : Prop := s.replayMode = false ∧ s.acc = 0 ∧ s.idx = 0 ∧ s.sel = none ∧ s.fnz = none

theorem crun_append (s : CState) (ts us : List Tok) :
    crun s (ts ++ us) = ((crun (crun s ts).1 us).1, (crun s ts).2 ++ (crun (crun s ts).1 us).2) := by
  induction ts generalizing s with
  | nil => simp [crun]
  | cons t ts ih => simp only [List.cons_append, crun, ih, List.append_assoc]

theorem crunStates_append (s : CState) (ts us : List Tok) :
    ∀ st ∈ crunStates s (ts ++ us), st ∈ crunStates s ts ∨ st ∈ crunStates (crun s ts).1 us := by
  induction ts generalizing s with
  | nil => intro st h; right; simpa [crun] using h
  | cons t ts ih =>
    intro st h
    simp only [List.cons_append, crunStates, List.mem_cons] at h
    rcases h with rfl | h
    · left; simp [crunStates]
    · rcases ih _ st h with h' | h'
      · left; simp [crunStates, h']
      · right; simpa [crun] using h'

theorem crun_mem_states (s : CState) (ts : List Tok) : (crun s ts).1 ∈ crunStates s ts := by
  induction ts generalizing s with
  | nil => simp [crun, crunStates]
  | cons t ts ih => simp only [crun, crunStates, List.mem_cons]; right; exact ih _

/-! ## The combined protocol -/

theorem crun_scan_rows (s : CState) (hs : s.replayMode = false) (P : List Nat) :
    crun s (P.map Tok.row) = (⟨false, s.acc ^^^ nimSum P, s.prev, s.valid, s.sig, s.idx, s.sel, s.fnz⟩, []) := by
  induction P generalizing s with
  | nil => cases s; simp_all [crun, nimSum]
  | cons x P ih =>
    simp only [List.map_cons, crun, cstep, hs, Bool.false_eq_true, if_false]
    rw [ih _ rfl]
    simp [nimSum, Nat.xor_assoc, Option.toList]

theorem crun_replay_rows (s : CState) (hs : s.replayMode = true) (P : List Nat) :
    crun s (P.map Tok.row) =
      (⟨true, s.acc, s.prev, s.valid, s.sig, (replay s.sig ⟨s.idx, s.sel, s.fnz⟩ P).idx,
        (replay s.sig ⟨s.idx, s.sel, s.fnz⟩ P).sel, (replay s.sig ⟨s.idx, s.sel, s.fnz⟩ P).fnz⟩, []) := by
  induction P generalizing s with
  | nil => cases s; simp_all [crun, replay]
  | cons x P ih =>
    simp only [List.map_cons, crun, cstep, hs, if_true]
    rw [ih _ (by rfl)]
    simp [replay, Option.toList]

/-- ONE DECISION: from an idle state, the controller emits the summary and then the
    move computed by replay FROM THE STORED SUMMARY, and returns to an idle state that
    retains the summary. -/
theorem crun_decision (s : CState) (hs : Idle s) (P : List Nat) :
    crun s (dtoks P) =
      (⟨false, 0, nimSum P, true, nimSum P, 0, none, none⟩,
       [COut.summary (nimSum P) (if s.valid then some (s.prev ^^^ nimSum P) else none),
        COut.move (replayMove (nimSum P) P)]) := by
  obtain ⟨hm, ha, hi, hsel, hf⟩ := hs
  unfold dtoks
  rw [crun_append, crun_append, crun_append, crun_scan_rows s hm]
  simp only [crun, cstep, Bool.false_eq_true, if_false, ha, Nat.zero_xor, Option.toList]
  rw [crun_replay_rows _ rfl]
  simp only [crun, cstep, if_true, Option.toList, List.nil_append, List.append_nil,
    List.cons_append, List.singleton_append]
  unfold replayMove
  simp

/-- Expected outputs of a stream of decisions. -/
def ctrlOuts : Bool → Nat → List (List Nat) → List COut
  | _, _, [] => []
  | v, q, P :: Ps =>
    COut.summary (nimSum P) (if v then some (q ^^^ nimSum P) else none) ::
      COut.move (replayMove (nimSum P) P) :: ctrlOuts true (nimSum P) Ps

/-- STREAM THEOREM: for any finite sequence of boards (empty boards allowed), from an
    idle state the outputs are summary/move pairs; every move is computed from the
    summary stored at that board's separator. -/
theorem crun_stream (s : CState) (hs : Idle s) (Ps : List (List Nat)) :
    (crun s (stream Ps)).2 = ctrlOuts s.valid s.prev Ps ∧ Idle (crun s (stream Ps)).1 := by
  induction Ps generalizing s with
  | nil => exact ⟨rfl, hs⟩
  | cons P Ps ih =>
    have e : stream (P :: Ps) = dtoks P ++ stream Ps := by simp [stream]
    rw [e, crun_append, crun_decision s hs P]
    have hidle : Idle (⟨false, 0, nimSum P, true, nimSum P, 0, none, none⟩ : CState) :=
      ⟨rfl, rfl, rfl, rfl, rfl⟩
    obtain ⟨h1, h2⟩ := ih _ hidle
    exact ⟨by simp [ctrlOuts, h1], h2⟩

theorem cinit_idle : Idle cinit := ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- RESET: a reset token returns the controller to the initial state from ANY state
    (no accidental persistence between games). -/
theorem crun_reset (s : CState) (ts : List Tok) : crun s (Tok.reset :: ts) = crun cinit ts := by
  simp [crun, cstep, Option.toList]

/-- GAMES: from any state whatsoever, a stream of games each preceded by a reset
    produces, game by game, the outputs of a fresh controller. -/
theorem crun_games (s : CState) (gs : List (List (List Nat))) :
    (crun s (gameStream gs)).2 = gs.flatMap (ctrlOuts false 0) := by
  induction gs generalizing s with
  | nil => rfl
  | cons g gs ih =>
    have e : gameStream (g :: gs) = (Tok.reset :: stream g) ++ gameStream gs := by
      simp [gameStream]
    rw [e, crun_append, crun_reset]
    obtain ⟨h1, _⟩ := crun_stream cinit cinit_idle g
    simp only [List.flatMap_cons]
    rw [ih, h1]
    rfl

/-- Empty boards and consecutive separators: an empty board is the token pair
    sep, sep; the controller reports summary 0 and halts (move none). -/
theorem empty_board (s : CState) (hs : Idle s) :
    dtoks [] = [Tok.sep, Tok.sep] ∧
    (crun s (dtoks [])).2 = [COut.summary 0 (if s.valid then some (s.prev ^^^ 0) else none),
      COut.move none] := by
  refine ⟨rfl, ?_⟩
  rw [crun_decision s hs]
  simp [nimSum, replayMove, replay, firstSome]

/-! ## The decision is correct and wins -/

/-- The move output of a decision (independent of the retained summary state). -/
def decisionMove (P : List Nat) : Option (Nat × Nat) := replayMove (nimSum P) P

/-- DECISION CORRECTNESS: legal move; zero successor from nonzero positions; halt
    exactly on terminal boards. -/
theorem decision_correct (P : List Nat) :
    (decisionMove P = none ↔ Terminal P) ∧
    (∀ i v, decisionMove P = some (i, v) → ∃ x, P[i]? = some x ∧ v < x ∧ Move P (P.set i v)) ∧
    (nimSum P ≠ 0 → ∃ i v, decisionMove P = some (i, v) ∧ nimSum (P.set i v) = 0) := by
  obtain ⟨h1, h2, h3⟩ := replay_correct P
  refine ⟨h1, fun i v h => ?_, h3⟩
  obtain ⟨x, hx, hlt⟩ := h2 i v h
  exact ⟨x, hx, hlt, set_move hx hlt⟩

/-- The controller as a strategy on boards. -/
def ctrlSel (P : List Nat) : Option (List Nat) := (decisionMove P).map (fun m => P.set m.1 m.2)

/-- WINNING AGAINST EVERY LEGAL OPPONENT (checked game semantics): from every board
    with nonzero nim-sum, the controller's decisions win. -/
theorem ctrl_wins (P : List Nat) (h : nimSum P ≠ 0) : Wins ctrlSel P := by
  obtain ⟨i, v, hd, hz⟩ := (decision_correct P).2.2 h
  obtain ⟨x, hx, hlt, hm⟩ := (decision_correct P).2.1 i v hd
  refine Wins.intro P (P.set i v) (by simp [ctrlSel, hd]) hm ?_
  intro r hr
  have h1 := move_sum_lt hm
  have h2 := move_sum_lt hr
  exact ctrl_wins r (move_from_zero hr hz)
termination_by P.sum

/-! ## Reachable registers fit in B and r bits -/

/-- Register bounds for N heaps of B bits and an r-bit counter (N < 2^r). -/
def Fits (B N : Nat) (s : CState) : Prop :=
  s.acc < 2 ^ B ∧ s.prev < 2 ^ B ∧ s.sig < 2 ^ B ∧ s.idx ≤ N ∧
  (∀ i v, s.sel = some (i, v) → i < N ∧ v < 2 ^ B) ∧
  (∀ i v, s.fnz = some (i, v) → i < N ∧ v < 2 ^ B)

theorem replayStep_fits {B σ : Nat} {r : Replay} {x : Nat} (hx : x < 2 ^ B)
    (hsel : ∀ i v, r.sel = some (i, v) → i < r.idx ∧ v < 2 ^ B)
    (hfnz : ∀ i v, r.fnz = some (i, v) → i < r.idx ∧ v < 2 ^ B) :
    (replayStep σ r x).idx = r.idx + 1 ∧
    (∀ i v, (replayStep σ r x).sel = some (i, v) → i < r.idx + 1 ∧ v < 2 ^ B) ∧
    (∀ i v, (replayStep σ r x).fnz = some (i, v) → i < r.idx + 1 ∧ v < 2 ^ B) := by
  refine ⟨rfl, ?_, ?_⟩
  · intro i v h
    simp only [replayStep] at h
    cases hs : r.sel with
    | some m =>
      rw [hs] at h; simp only [Option.some.injEq] at h; subst h
      obtain ⟨h1, h2⟩ := hsel _ _ hs; exact ⟨by omega, h2⟩
    | none =>
      rw [hs] at h
      simp only at h
      split at h
      · next hc => simp only [Option.some.injEq, Prod.mk.injEq] at h
                   obtain ⟨rfl, rfl⟩ := h; exact ⟨by omega, Nat.lt_trans hc.2 hx⟩
      · cases h
  · intro i v h
    simp only [replayStep] at h
    cases hs : r.fnz with
    | some m =>
      rw [hs] at h; simp only [Option.some.injEq] at h; subst h
      obtain ⟨h1, h2⟩ := hfnz _ _ hs; exact ⟨by omega, h2⟩
    | none =>
      rw [hs] at h
      simp only at h
      split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h; exact ⟨by omega, by omega⟩
      · cases h

theorem scan_rows_fit {B N : Nat} (s : CState) (hm : s.replayMode = false) (hf : Fits B N s)
    (P : List Nat) (hw : Width B P) : ∀ st ∈ crunStates s (P.map Tok.row), Fits B N st := by
  induction P generalizing s with
  | nil => intro st h; simp [crunStates] at h; subst h; exact hf
  | cons x P ih =>
    intro st h
    simp only [List.map_cons, crunStates, List.mem_cons] at h
    rcases h with rfl | h
    · exact hf
    · have hx : x < 2 ^ B := hw x (by simp)
      have hf' : Fits B N (cstep s (Tok.row x)).1 := by
        simp only [cstep, hm, Bool.false_eq_true, if_false]
        exact ⟨Nat.xor_lt_two_pow hf.1 hx, hf.2.1, hf.2.2.1, hf.2.2.2.1, hf.2.2.2.2.1, hf.2.2.2.2.2⟩
      have hm' : (cstep s (Tok.row x)).1.replayMode = false := by simp [cstep, hm]
      exact ih _ hm' hf' (fun y hy => hw y (List.mem_cons_of_mem _ hy)) st h

theorem replay_rows_fit {B N : Nat} (s : CState) (hm : s.replayMode = true)
    (hregs : s.acc < 2 ^ B ∧ s.prev < 2 ^ B ∧ s.sig < 2 ^ B)
    (hsel : ∀ i v, s.sel = some (i, v) → i < s.idx ∧ v < 2 ^ B)
    (hfnz : ∀ i v, s.fnz = some (i, v) → i < s.idx ∧ v < 2 ^ B)
    (P : List Nat) (hlen : s.idx + P.length ≤ N) (hw : Width B P) :
    ∀ st ∈ crunStates s (P.map Tok.row), Fits B N st := by
  induction P generalizing s with
  | nil =>
    intro st h; simp [crunStates] at h; subst h
    exact ⟨hregs.1, hregs.2.1, hregs.2.2, by simpa using hlen,
      fun i v h => ⟨by have := (hsel i v h).1; simp at hlen; omega, (hsel i v h).2⟩,
      fun i v h => ⟨by have := (hfnz i v h).1; simp at hlen; omega, (hfnz i v h).2⟩⟩
  | cons x P ih =>
    intro st h
    simp only [List.map_cons, crunStates, List.mem_cons] at h
    have hx : x < 2 ^ B := hw x (by simp)
    simp only [List.length_cons] at hlen
    rcases h with rfl | h
    · exact ⟨hregs.1, hregs.2.1, hregs.2.2, by omega,
        fun i v h => ⟨by have := (hsel i v h).1; omega, (hsel i v h).2⟩,
        fun i v h => ⟨by have := (hfnz i v h).1; omega, (hfnz i v h).2⟩⟩
    · obtain ⟨hi, hs', hf'⟩ := replayStep_fits (σ := s.sig) (r := ⟨s.idx, s.sel, s.fnz⟩) hx hsel hfnz
      dsimp only at hi hs' hf'
      apply ih (cstep s (Tok.row x)).1 (by simp [cstep, hm])
      · simp only [cstep, hm, if_true]; exact hregs
      · simp only [cstep, hm, if_true]; rw [hi]; exact hs'
      · simp only [cstep, hm, if_true]; rw [hi]; exact hf'
      · simp only [cstep, hm, if_true]; rw [hi]; omega
      · exact fun y hy => hw y (List.mem_cons_of_mem _ hy)
      · exact h

/-- REACHABLE-STATE BOUNDS: along a well-formed stream of boards of N heaps below 2^B,
    started from an idle fitting state, EVERY visited state has acc, prev, sig < 2^B,
    counter ≤ N, and selected/fallback moves with index < N and value < 2^B.  With
    N < 2^r, every register fits its r- or B-bit field; the counter never overflows. -/
theorem stream_fits {B N : Nat} (s : CState) (hs : Idle s) (hf : Fits B N s) (Ps : List (List Nat))
    (hP : ∀ P ∈ Ps, P.length = N ∧ Width B P) : ∀ st ∈ crunStates s (stream Ps), Fits B N st := by
  induction Ps generalizing s with
  | nil => intro st h; simp [stream, crunStates] at h; subst h; exact hf
  | cons P Ps ih =>
    have e : stream (P :: Ps) = dtoks P ++ stream Ps := by simp [stream]
    rw [e]
    intro st h
    obtain ⟨hlenP, hwP⟩ := hP P (by simp)
    rcases crunStates_append s _ _ st h with h1 | h1
    · -- inside the decision
      unfold dtoks at h1
      rcases crunStates_append s _ _ st h1 with h2 | h2
      · rcases crunStates_append s _ _ st h2 with h3 | h3
        · rcases crunStates_append s _ _ st h3 with h4 | h4
          · exact scan_rows_fit s hs.1 hf P hwP st h4
          · rw [crun_scan_rows s hs.1] at h4
            simp only [crunStates, cstep, Bool.false_eq_true, if_false, List.mem_cons,
              List.mem_singleton] at h4
            have ha : s.acc ^^^ nimSum P < 2 ^ B := Nat.xor_lt_two_pow hf.1 (nimSum_lt hwP)
            rcases h4 with rfl | rfl | h4
            · exact ⟨ha, hf.2.1, hf.2.2.1, hf.2.2.2.1, hf.2.2.2.2.1, hf.2.2.2.2.2⟩
            · exact ⟨Nat.two_pow_pos B, ha, ha, Nat.zero_le _, by simp, by simp⟩
            · simp at h4
        · rw [crun_append, crun_scan_rows s hs.1] at h3
          simp only [crun, cstep, Bool.false_eq_true, if_false] at h3
          have ha : s.acc ^^^ nimSum P < 2 ^ B := Nat.xor_lt_two_pow hf.1 (nimSum_lt hwP)
          exact replay_rows_fit _ rfl ⟨Nat.two_pow_pos B, ha, ha⟩ (by simp) (by simp) P
            (by simp [hlenP]) hwP st h3
      · rw [crun_append, crun_append, crun_scan_rows s hs.1] at h2
        simp only [crun, cstep, Bool.false_eq_true, if_false] at h2
        have ha : s.acc ^^^ nimSum P < 2 ^ B := Nat.xor_lt_two_pow hf.1 (nimSum_lt hwP)
        generalize hS1 : (⟨true, 0, s.acc ^^^ nimSum P, true, s.acc ^^^ nimSum P, 0, none, none⟩ :
          CState) = S1 at h2
        have hS1m : S1.replayMode = true := by rw [← hS1]
        simp only [crunStates, List.mem_cons, List.mem_singleton] at h2
        rcases h2 with rfl | rfl | h2
        · subst hS1
          exact replay_rows_fit _ rfl ⟨Nat.two_pow_pos B, ha, ha⟩ (by simp) (by simp) P
            (by simp [hlenP]) hwP _ (crun_mem_states _ _)
        · rw [crun_replay_rows _ hS1m]
          subst hS1
          simp only [cstep, if_true]
          exact ⟨Nat.two_pow_pos B, ha, ha, Nat.zero_le _, by simp, by simp⟩
        · simp at h2
    · rw [crun_decision s hs P] at h1
      have hidle : Idle (⟨false, 0, nimSum P, true, nimSum P, 0, none, none⟩ : CState) :=
        ⟨rfl, rfl, rfl, rfl, rfl⟩
      have hfit : Fits B N (⟨false, 0, nimSum P, true, nimSum P, 0, none, none⟩ : CState) :=
        ⟨Nat.two_pow_pos B, nimSum_lt hwP, nimSum_lt hwP, Nat.zero_le _, by simp, by simp⟩
      exact ih _ hidle hfit (fun Q hQ => hP Q (by simp [hQ])) st h1


/-! ## Axiom audit -/

#print axioms crun_append
#print axioms crunStates_append
#print axioms crun_mem_states
#print axioms crun_scan_rows
#print axioms crun_replay_rows
#print axioms crun_decision
#print axioms crun_stream
#print axioms cinit_idle
#print axioms crun_reset
#print axioms crun_games
#print axioms empty_board
#print axioms decision_correct
#print axioms ctrl_wins
#print axioms replayStep_fits
#print axioms scan_rows_fit
#print axioms replay_rows_fit
#print axioms stream_fits
end Controller
end NimAudit
