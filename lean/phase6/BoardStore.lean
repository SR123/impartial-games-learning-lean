import Bypass

/- Phase 6, Priority 3b: the board-storage (one-pass) alternative of Section
   sec:recurrent-bypass, at bit level.  Written by Claude (10 October 2026).
   Lean 4.26.0, core/Std only.

   REGISTERS (finite, B·N + B + r bits): the stored board (N heaps × B bits, the boardBits
   layout), the accumulator acc (B bits, LSB first) and the write pointer idx (r bits, LSB
   first, N < 2^r so that idx can hold N).
   TOKENS: row x | sep | reset (one-hot tag bits and B row bits, LSB first).
     row x : board[idx] := x (multiplexed write via an equality decoder), acc := acc ⊕ x,
             idx := idx + 1 (ripple increment);
     sep   : output the summary acc and the move computed by the CONSTANT-DEPTH selector
             varBin (phase 5) on the stored board with target acc; acc := 0, idx := 0;
     reset : board := 0, acc := 0, idx := 0.
   One decision is rows(P), SEP: N + 1 updates, one pass, no replay; the price is the
   B·N-bit board register.  Proved: bit-level refinement of every update on fitting
   states, the decision theorem (summary nim(P) and move decisionMove P), persistence and
   reset, a stateful winning theorem against every legal opponent, and family
   certificates for the update and output formulas (constant depth, polynomial size,
   fixed-scale networks). -/

namespace NimAudit
namespace BoardStore

open Game Rollout Prob Attain Recurrent AC0 AC0.Circ CorrBridge AttainCircuit Bridge SelectCircuit
  BinReadout Controller ControllerBits PriorityEncoder ThresholdNet ThresholdInst FiniteNet WholeGame
  Family Barrier RolloutExec

/-! ## Semantics -/

structure BS where
  board : List Nat
  acc : Nat
  idx : Nat

def bsInit (N : Nat) : BS := ⟨List.replicate N 0, 0, 0⟩

/-- Output at a separator: summary and selected move. -/
structure BOut where
  sum : Nat
  move : Option (Nat × Nat)

def bsStep (N : Nat) (s : BS) : Tok → BS × Option BOut
  | .reset => (bsInit N, none)
  | .row x => (⟨s.board.set s.idx x, s.acc ^^^ x, s.idx + 1⟩, none)
  | .sep => (⟨s.board, 0, 0⟩, some ⟨s.acc, attainT s.acc s.board⟩)

def bsRun (N : Nat) : BS → List Tok → BS × List BOut
  | s, [] => (s, [])
  | s, t :: ts => ((bsRun N (bsStep N s t).1 ts).1, (bsStep N s t).2.toList ++ (bsRun N (bsStep N s t).1 ts).2)

/-- The tokens of one decision: one pass over the rows, then a separator. -/
def btoks (P : List Nat) : List Tok := P.map Tok.row ++ [Tok.sep]

theorem btoks_length (P : List Nat) : (btoks P).length = P.length + 1 := by simp [btoks]

/-- Writing a list of rows into the board from position k. -/
def writes : List Nat → Nat → List Nat → List Nat
  | b, _, [] => b
  | b, k, x :: L => writes (b.set k x) (k + 1) L

theorem bsRun_append (N : Nat) (s : BS) (ts us : List Tok) :
    bsRun N s (ts ++ us) = ((bsRun N (bsRun N s ts).1 us).1, (bsRun N s ts).2 ++ (bsRun N (bsRun N s ts).1 us).2) := by
  induction ts generalizing s with
  | nil => simp [bsRun]
  | cons t ts ih => simp only [List.cons_append, bsRun, ih, List.append_assoc]

theorem bsRun_rows (N : Nat) : ∀ (L : List Nat) (b : List Nat) (a k : Nat),
    bsRun N ⟨b, a, k⟩ (L.map Tok.row) = (⟨writes b k L, a ^^^ nimSum L, k + L.length⟩, [])
  | [], b, a, k => by simp [bsRun, writes, nimSum]
  | x :: L, b, a, k => by
    simp only [List.map_cons, bsRun, bsStep, Option.toList, List.nil_append]
    rw [bsRun_rows N L]
    simp [writes, nimSum, Nat.xor_assoc]; omega

theorem take_set_succ (b : List Nat) (k x : Nat) (hk : k < b.length) :
    (b.set k x).take (k + 1) = b.take k ++ [x] := by
  apply List.ext_getElem
  · simp; omega
  · intro n h1 h2
    simp only [List.length_take, List.length_set] at h1
    rw [List.getElem_take]
    by_cases hn : n < k
    · rw [List.getElem_append_left (by simp; omega), List.getElem_take, List.getElem_set_ne (by omega)]
    · have : n = k := by omega
      subst this
      rw [List.getElem_append_right (by simp; omega)]
      simp

theorem writes_eq : ∀ (L b : List Nat) (k : Nat), k + L.length = b.length → writes b k L = b.take k ++ L
  | [], b, k, h => by simp [writes]; rw [List.take_of_length_le (by simp at h; omega)]
  | x :: L, b, k, h => by
    simp only [writes]
    rw [writes_eq L (b.set k x) (k + 1) (by simp at h ⊢; omega)]
    rw [take_set_succ b k x (by simp at h; omega)]
    simp

/-- ONE DECISION: from any idle state whose board has N slots, rows(P), SEP stores P,
    reports nim(P) and the winning-move selector's move, and returns to idle. -/
theorem bs_decision {N : Nat} (b : List Nat) (hb : b.length = N) (P : List Nat) (hP : P.length = N) :
    bsRun N ⟨b, 0, 0⟩ (btoks P) = (⟨P, 0, 0⟩, [⟨nimSum P, decisionMove P⟩]) := by
  unfold btoks
  rw [bsRun_append, bsRun_rows N P b 0 0, writes_eq P b 0 (by omega)]
  simp [bsRun, bsStep, attainT_eq_replayMove, decisionMove]

/-- RESET from any state. -/
theorem bs_reset (N : Nat) (s : BS) (ts : List Tok) : bsRun N s (Tok.reset :: ts) = bsRun N (bsInit N) ts := by
  simp [bsRun, bsStep, Option.toList]

/-- The move output by one decision. -/
def bsMove (N : Nat) (s : BS) (P : List Nat) : Option (Nat × Nat) :=
  ((bsRun N s (btoks P)).2.head?).bind BOut.move

/-- Stateful interaction (player to move at P, machine in state s). -/
inductive StoreWins (N : Nat) : BS → List Nat → Prop
  | intro (s : BS) (P R : List Nat) :
      applyM P (bsMove N s P) = some R → Move P R →
      (bsRun N s (btoks P)).1 = ⟨P, 0, 0⟩ →
      (∀ P', Move R P' → StoreWins N ⟨P, 0, 0⟩ P') → StoreWins N s P

theorem storeWins_sound {N : Nat} {s : BS} {P : List Nat} (h : StoreWins N s P) : Win P := by
  induction h with
  | intro s P R _ hm _ _ ih => exact Win.intro P R hm (Lose.intro R ih)

/-- WHOLE-GAME THEOREM (semantic board-storage controller): from any idle state with N
    slots and every nonzero board of length N, the one-pass controller wins against every
    legal opponent; the stored board persists between decisions. -/
theorem store_wins {N : Nat} : ∀ (P : List Nat), P.length = N → nimSum P ≠ 0 →
    ∀ b, b.length = N → StoreWins N ⟨b, 0, 0⟩ P := by
  intro P
  induction P using (measure List.sum).wf.induction with
  | h P ih =>
    intro hP h0 b hb
    have hdec := bs_decision b hb P hP
    obtain ⟨i, v, hd, hz⟩ := (decision_correct P).2.2 h0
    obtain ⟨x, _, _, hmv⟩ := (decision_correct P).2.1 i v hd
    refine StoreWins.intro _ P (P.set i v) ?_ hmv (by rw [hdec]) ?_
    · unfold bsMove; rw [hdec]; simp [hd, applyM]
    · intro P' hm'
      have hlt1 := move_sum_lt hmv
      have hlt2 := move_sum_lt hm'
      exact ih P' (by show P'.sum < P.sum; omega) (by rw [move_length hm', move_length hmv, hP])
        (move_from_zero hm' hz) P hP

/-! ## Bit level -/

/-- State width B·N + B + r. -/
def sw (B N r : Nat) : Nat := B * N + B + r

def accW (B N q : Nat) : Nat := B * N + q
def idxW (B N q : Nat) : Nat := B * N + B + q

def bsBits (B N r : Nat) (s : BS) : Nat → Bool := fun w =>
  if w < B * N then boardBits B s.board w
  else if w < B * N + B then s.acc.testBit (w - B * N)
  else if w < sw B N r then s.idx.testBit (w - (B * N + B)) else false

/-- Token bits: 0 row flag, 1 separator flag, 2 reset flag, 3 + q row bit q. -/
def tokB : Tok → Nat → Bool
  | .row x, j => if j = 0 then true else if 3 ≤ j then x.testBit (j - 3) else false
  | .sep, j => decide (j = 1)
  | .reset, j => decide (j = 2)

def inB (B N r : Nat) (v : Nat → Bool) (t : Tok) : Nat → Bool := fun w =>
  if w < sw B N r then v w else tokB t (w - sw B N r)

def rowC (B N r : Nat) : Circ := input (sw B N r)
def sepC (B N r : Nat) : Circ := input (sw B N r + 1)
def rstC' (B N r : Nat) : Circ := input (sw B N r + 2)
def xC (B N r q : Nat) : Circ := input (sw B N r + 3 + q)

/-- Equality decoder for the LSB-first pointer. -/
def eqI (B N r i : Nat) : Circ := and ((List.range r).map (fun q => litEq (input (idxW B N q)) (i.testBit q)))

/-- Ripple increment: bit q of idx + 1. -/
def incF (B N q : Nat) : Circ := xor2 (input (idxW B N q)) (and ((List.range q).map (fun t => input (idxW B N t))))

def bBoard (B N r w : Nat) : Circ :=
  RolloutExec.mux (rstC' B N r) (const false)
    (RolloutExec.mux (and [rowC B N r, eqI B N r (w / B)]) (xC B N r (B - 1 - w % B)) (input w))

def bAcc (B N r q : Nat) : Circ :=
  RolloutExec.mux (rstC' B N r) (const false)
    (RolloutExec.mux (rowC B N r) (xor2 (input (accW B N q)) (xC B N r q)) (RolloutExec.mux (sepC B N r) (const false) (input (accW B N q))))

def bIdx (B N r q : Nat) : Circ :=
  RolloutExec.mux (rstC' B N r) (const false)
    (RolloutExec.mux (rowC B N r) (incF B N q) (RolloutExec.mux (sepC B N r) (const false) (input (idxW B N q))))

/-- The update formulas: board, accumulator, pointer. -/
def bsForms (B N r : Nat) : List Circ :=
  (List.range (B * N)).map (bBoard B N r) ++ (List.range B).map (bAcc B N r) ++ (List.range r).map (bIdx B N r)

theorem bsForms_length (B N r : Nat) : (bsForms B N r).length = sw B N r := by
  simp [bsForms, sw]; omega

/-- The output formulas: separator flag, summary bits, then the selector (valid, index,
    value) on the stored board and the accumulator. -/
def bsOuts (B N r r' : Nat) : List Circ :=
  [sepC B N r] ++ (List.range B).map (fun q => input (accW B N q)) ++ bForms (varBin B N r')

def bsBitStep (B N r : Nat) (v : Nat → Bool) (t : Tok) : Nat → Bool := fun w =>
  if w < sw B N r then eval (inB B N r v t) ((bsForms B N r).getD w (const false)) else false

/-! ### Evaluation lemmas -/

theorem bsForms_board {B N r w : Nat} (hw : w < B * N) : (bsForms B N r).getD w (const false) = bBoard B N r w := by
  unfold bsForms
  rw [List.getD_eq_getElem?_getD, List.append_assoc, List.getElem?_append_left (by simpa using hw), List.getElem?_map,
    List.getElem?_range hw]
  rfl

theorem bsForms_acc {B N r q : Nat} (hq : q < B) :
    (bsForms B N r).getD (B * N + q) (const false) = bAcc B N r q := by
  unfold bsForms
  rw [List.getD_eq_getElem?_getD, List.append_assoc, List.getElem?_append_right (by simp),
    List.getElem?_append_left (by simp; omega)]
  rw [show B * N + q - (List.map (bBoard B N r) (List.range (B * N))).length = q by simp]
  simp [hq]

theorem bsForms_idx {B N r q : Nat} (hq : q < r) :
    (bsForms B N r).getD (B * N + B + q) (const false) = bIdx B N r q := by
  unfold bsForms
  rw [List.getD_eq_getElem?_getD, List.append_assoc, List.getElem?_append_right (by simp; omega),
    List.getElem?_append_right (by simp; omega)]
  rw [show B * N + B + q - (List.map (bBoard B N r) (List.range (B * N))).length -
    (List.map (bAcc B N r) (List.range B)).length = q by simp; omega]
  simp [hq]

theorem eqI_eval (B N r i : Nat) (z : Nat → Bool) :
    eval z (eqI B N r i) = decide (∀ q < r, z (idxW B N q) = i.testBit q) := by
  apply Bool.eq_iff_iff.mpr
  simp only [eqI, eval_and, List.all_map, List.all_eq_true, List.mem_range, Function.comp_apply, decide_eq_true_iff]
  constructor
  · intro h q hq
    have := h q hq
    unfold litEq at this
    cases hb : i.testBit q <;> simp [hb] at this <;> simp [this]
  · intro h q hq
    unfold litEq
    rw [← h q hq]
    cases hz : z (idxW B N q) <;> simp [hz]

theorem eq_of_low_bits {a b r : Nat} (ha : a < 2 ^ r) (hb : b < 2 ^ r)
    (h : ∀ q < r, a.testBit q = b.testBit q) : a = b := by
  apply Nat.eq_of_testBit_eq
  intro q
  rcases Nat.lt_or_ge q r with hq | hq
  · exact h q hq
  · rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le ha (Nat.pow_le_pow_right (by decide) hq)),
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hb (Nat.pow_le_pow_right (by decide) hq))]

/-- Register fit invariant (N < 2^r so the pointer can count to N). -/
structure FitsB (B N r : Nat) (s : BS) : Prop where
  len : s.board.length = N
  width : Width B s.board
  acc : s.acc < 2 ^ B
  idx : s.idx ≤ N
  cnt : N < 2 ^ r

theorem boardBits_set' {B N : Nat} {P : List Nat} (hl : P.length = N) {i w : Nat} (v : Nat) (hw : w < B * N) :
    boardBits B (P.set i v) w = if w / B = i then v.testBit (B - 1 - w % B) else boardBits B P w := by
  by_cases hi : i < N
  · exact boardBits_set hl v hi hw
  · have hwi : w / B < N := by
      rcases Nat.eq_zero_or_pos B with hB | hB
      · subst hB; simp at hw
      · exact (Nat.div_lt_iff_lt_mul hB).2 (by rw [Nat.mul_comm]; exact hw)
    rw [List.set_eq_of_length_le (by omega), if_neg (by omega)]

/-- ONE-STEP REFINEMENT: on fitting states (and a row value of width B; for a row the
    pointer is below N), the update formulas compute the encoding of the semantic step. -/
theorem boardBits_zero (B N w : Nat) : boardBits B (List.replicate N 0) w = false := by
  unfold boardBits
  split
  · rw [List.getD_eq_getElem?_getD, List.getElem?_replicate]; split <;> simp
  · rfl

theorem bsBitStep_spec {B N r : Nat} (s : BS) (hf : FitsB B N r s) (t : Tok)
    (ht : ∀ x, t = Tok.row x → x < 2 ^ B ∧ s.idx < N) :
    bsBitStep B N r (bsBits B N r s) t = bsBits B N r (bsStep N s t).1 := by
  have hidx_lt : s.idx < 2 ^ r := Nat.lt_of_le_of_lt hf.idx hf.cnt
  let z := inB B N r (bsBits B N r s) t
  have zb : ∀ w, w < B * N → z w = boardBits B s.board w := by
    intro w hw; simp only [z, inB, bsBits, sw]; rw [if_pos (by omega), if_pos hw]
  have za : ∀ q, q < B → z (accW B N q) = s.acc.testBit q := by
    intro q hq; simp only [z, inB, bsBits, accW, sw]; rw [if_pos (by omega), if_neg (by omega), if_pos (by omega)]
    congr 1; omega
  have zi : ∀ q, q < r → z (idxW B N q) = s.idx.testBit q := by
    intro q hq; simp only [z, inB, bsBits, idxW, sw]
    rw [if_pos (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]
    congr 1; omega
  have zrow : z (sw B N r) = tokB t 0 := by simp only [z, inB]; rw [if_neg (by omega)]; simp
  have zsep : z (sw B N r + 1) = tokB t 1 := by simp only [z, inB]; rw [if_neg (by omega)]; congr 1; omega
  have zrst : z (sw B N r + 2) = tokB t 2 := by simp only [z, inB]; rw [if_neg (by omega)]; congr 1; omega
  have zx : ∀ q, z (sw B N r + 3 + q) = tokB t (3 + q) := by
    intro q; simp only [z, inB]; rw [if_neg (by omega)]; congr 1; omega
  have tok_row : ∀ x q, tokB (Tok.row x) (3 + q) = x.testBit q := by
    intro x q; simp only [tokB]; rw [if_neg (by omega), if_pos (by omega)]; congr 1; omega
  funext w
  unfold bsBitStep bsBits
  by_cases hw1 : w < B * N
  · rw [if_pos (by unfold sw; omega), bsForms_board hw1, if_pos hw1]
    show eval z (bBoard B N r w) = _
    simp only [bBoard, eval_mux, rstC', rowC, xC, eval_input, eval_const, eval_and, List.all_cons, List.all_nil,
      Bool.and_true, zrow, zrst, zx, zb w hw1]
    cases t with
    | reset => simp [tokB, bsStep, bsInit, boardBits_zero]
    | sep => simp [tokB, bsStep]
    | row x =>
      obtain ⟨hx, hlt⟩ := ht x rfl
      have hwi : w / B < N := by
        rcases Nat.eq_zero_or_pos B with hB | hB
        · subst hB; simp at hw1
        · exact (Nat.div_lt_iff_lt_mul hB).2 (by rw [Nat.mul_comm]; exact hw1)
      have h2 : tokB (Tok.row x) 2 = false := by simp [tokB]
      have h0 : tokB (Tok.row x) 0 = true := by simp [tokB]
      simp only [h2, h0, tok_row, Bool.false_eq_true, if_false, Bool.true_and, bsStep]
      rw [eqI_eval, boardBits_set' hf.len x hw1]
      have hdec : decide (∀ q < r, z (idxW B N q) = (w / B).testBit q) = decide (w / B = s.idx) := by
        apply Bool.eq_iff_iff.mpr
        simp only [decide_eq_true_iff]
        constructor
        · intro h
          exact (eq_of_low_bits hidx_lt (Nat.lt_of_lt_of_le hwi (Nat.le_of_lt hf.cnt))
            (fun q hq => by rw [← zi q hq, h q hq])).symm
        · intro h q hq; rw [zi q hq, h]
      rw [hdec]
      by_cases hc : w / B = s.idx
      · simp [hc]
      · simp [hc]
  · rw [if_neg hw1]
    by_cases hw2 : w < B * N + B
    · have hq : w - B * N < B := by omega
      have hw' : w = B * N + (w - B * N) := by omega
      rw [if_pos (by unfold sw; omega), if_pos hw2, hw', bsForms_acc hq]
      show eval z (bAcc B N r (w - B * N)) = _
      simp only [bAcc, eval_mux, rstC', rowC, sepC, xC, eval_input, eval_const, eval_xor2, zrow, zsep, zrst, zx,
        za _ hq]
      rw [show B * N + (w - B * N) - B * N = w - B * N by omega]
      cases t with
      | reset => simp [tokB, bsStep, bsInit]
      | sep => simp [tokB, bsStep]
      | row x => simp [tokB, bsStep, Nat.testBit_xor, tok_row]
    · rw [if_neg hw2]
      by_cases hw3 : w < sw B N r
      · have hq : w - (B * N + B) < r := by unfold sw at hw3; omega
        have hw' : w = B * N + B + (w - (B * N + B)) := by omega
        rw [if_pos hw3, if_pos hw3, hw', bsForms_idx hq]
        show eval z (bIdx B N r (w - (B * N + B))) = _
        simp only [bIdx, eval_mux, rstC', rowC, sepC, eval_input, eval_const, zrow, zsep, zrst, zi _ hq]
        rw [show B * N + B + (w - (B * N + B)) - (B * N + B) = w - (B * N + B) by omega]
        have hinc : eval z (incF B N (w - (B * N + B))) = (s.idx + 1).testBit (w - (B * N + B)) := by
          simp only [incF, eval_xor2, eval_input, zi _ hq, eval_and, List.all_map, Function.comp_def]
          rw [ControllerBits.testBit_succ]
          congr 1
          apply Bool.eq_iff_iff.mpr
          simp only [List.all_eq_true, List.mem_range, decide_eq_true_iff]
          constructor
          · intro h u hu; rw [← zi u (by omega)]; exact h u hu
          · intro h u hu; rw [zi u (by omega)]; exact h u hu
        rw [hinc]
        cases t with
        | reset => simp [tokB, bsStep, bsInit]
        | sep => simp [tokB, bsStep]
        | row x => simp [tokB, bsStep]
      · rw [if_neg hw3, if_neg hw3]

/-- Output decoding at a separator: flag, summary, selected move. -/
def bsDecode (B N r r' : Nat) (z : Nat → Bool) : Option BOut :=
  if z (sw B N r + 1) then
    some ⟨ofBits B (fun q => z (accW B N q)), binSem (varBin B N r') N z⟩
  else none

/-- OUTPUT REFINEMENT: at a separator from a fitting state, the decoded outputs are the
    summary acc and the move attainT acc board (the phase-5 selector's semantics). -/
theorem bsDecode_sep {B N r r' : Nat} (hr' : N ≤ 2 ^ r') (s : BS) (hf : FitsB B N r s) :
    bsDecode B N r r' (inB B N r (bsBits B N r s) Tok.sep) = (bsStep N s Tok.sep).2 := by
  have hsel : ∀ c ∈ bForms (varBin B N r'), eval (inB B N r (bsBits B N r s) Tok.sep) c =
      eval (selIn B N s.board s.acc) c := by
    intro c hc
    have hb := (varSel_bound (B := B) (N := N))
    have hm : maxInput c ≤ B * N + B := by
      have := encode_bound_sel hb hr'
      exact (this.all c hc).2.2
    apply eval_congr_below
    intro i hi
    simp only [inB, bsBits, selIn, sw]
    rw [if_pos (by omega)]
    by_cases h1 : i < B * N
    · rw [if_pos h1, if_pos h1]
    · rw [if_neg h1, if_neg h1, if_pos (by omega)]
  unfold bsDecode bsStep
  have hflag : inB B N r (bsBits B N r s) Tok.sep (sw B N r + 1) = true := by
    simp only [inB]; rw [if_neg (by omega)]; simp [tokB]
  rw [if_pos hflag]
  simp only [Option.some.injEq, BOut.mk.injEq]
  constructor
  · apply Nat.eq_of_testBit_eq
    intro q
    rw [testBit_ofBits]
    by_cases hq : q < B
    · simp only [hq, decide_true, Bool.true_and]
      simp only [inB, bsBits, accW, sw]
      rw [if_pos (by omega), if_neg (by omega), if_pos (by omega)]
      congr 1; omega
    · simp only [hq, decide_false, Bool.false_and]
      rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hf.acc (Nat.pow_le_pow_right (by decide) (by omega)))]
  · have hb := encode_bound_sel (varSel_bound (B := B) (N := N)) hr'
    have e : binSem (varBin B N r') N (inB B N r (bsBits B N r s) Tok.sep) =
        binSem (varBin B N r') N (selIn B N s.board s.acc) := by
      unfold binSem
      have hv : eval (inB B N r (bsBits B N r s) Tok.sep) (varBin B N r').valid =
          eval (selIn B N s.board s.acc) (varBin B N r').valid := hsel _ (by simp [bForms])
      have hi : (varBin B N r').idx.map (eval (inB B N r (bsBits B N r s) Tok.sep)) =
          (varBin B N r').idx.map (eval (selIn B N s.board s.acc)) :=
        List.map_congr_left (fun c hc => hsel c (by simp [bForms, hc]))
      have hva : (varBin B N r').val.map (eval (inB B N r (bsBits B N r s) Tok.sep)) =
          (varBin B N r').val.map (eval (selIn B N s.board s.acc)) :=
        List.map_congr_left (fun c hc => hsel c (by simp [bForms, hc]))
      rw [hv, hi, hva]
    rw [e]
    exact varBin_correct hr' hf.len hf.width hf.acc

/-! ### Runs over one decision -/

def bsBitRun (B N r : Nat) : (Nat → Bool) → List Tok → (Nat → Bool)
  | v, [] => v
  | v, t :: ts => bsBitRun B N r (bsBitStep B N r v t) ts

theorem bsBitRun_append (B N r : Nat) (v : Nat → Bool) (ts us : List Tok) :
    bsBitRun B N r v (ts ++ us) = bsBitRun B N r (bsBitRun B N r v ts) us := by
  induction ts generalizing v with
  | nil => rfl
  | cons t ts ih => exact ih _

theorem bits_rows {B N r : Nat} : ∀ (L : List Nat) (b : List Nat) (a k : Nat),
    FitsB B N r ⟨b, a, k⟩ → Width B L → k + L.length ≤ N →
    bsBitRun B N r (bsBits B N r ⟨b, a, k⟩) (L.map Tok.row) = bsBits B N r ⟨writes b k L, a ^^^ nimSum L, k + L.length⟩ ∧
      FitsB B N r ⟨writes b k L, a ^^^ nimSum L, k + L.length⟩
  | [], b, a, k, hf, _, _ => by simpa [bsBitRun, writes, nimSum] using hf
  | x :: L, b, a, k, hf, hw, hk => by
    have hx : x < 2 ^ B := hw x (by simp)
    simp only [List.map_cons, bsBitRun]
    rw [bsBitStep_spec _ hf (Tok.row x) (fun y hy => by cases hy; exact ⟨hx, show k < N by simp at hk; omega⟩)]
    have hf' : FitsB B N r ⟨b.set k x, a ^^^ x, k + 1⟩ := by
      refine ⟨by simp [hf.len], fun y hy => ?_, Nat.xor_lt_two_pow hf.acc hx, show k + 1 ≤ N by simp at hk; omega, hf.cnt⟩
      rcases List.mem_or_eq_of_mem_set hy with h | h
      · exact hf.width y h
      · rw [h]; exact hx
    obtain ⟨h1, h2⟩ := bits_rows L (b.set k x) (a ^^^ x) (k + 1) hf' (fun y hy => hw y (by simp [hy]))
      (by simp at hk; omega)
    simp only [bsStep]
    have e1 : a ^^^ x ^^^ nimSum L = a ^^^ nimSum (x :: L) := by simp [nimSum, Nat.xor_assoc]
    have e2 : k + 1 + L.length = k + (x :: L).length := by simp; omega
    rw [e1, e2] at h1 h2
    exact ⟨h1, h2⟩

/-- BIT-LEVEL DECISION THEOREM: from the encoding of any idle state with N slots, the
    N row updates and the separator update produce the encoding of the idle state storing
    P, and the outputs at the separator decode to (nim(P), decisionMove P). -/
theorem bits_decision {B N r r' : Nat} (hN : N < 2 ^ r) (hr' : N ≤ 2 ^ r') (b : List Nat) (hb : b.length = N)
    (hwb : Width B b) (P : List Nat) (hP : P.length = N) (hw : Width B P) :
    bsBitRun B N r (bsBits B N r ⟨b, 0, 0⟩) (btoks P) = bsBits B N r ⟨P, 0, 0⟩ ∧
    bsDecode B N r r' (inB B N r (bsBitRun B N r (bsBits B N r ⟨b, 0, 0⟩) (P.map Tok.row)) Tok.sep) =
      some ⟨nimSum P, decisionMove P⟩ := by
  have hf0 : FitsB B N r ⟨b, 0, 0⟩ := ⟨hb, hwb, Nat.two_pow_pos B, Nat.zero_le _, hN⟩
  obtain ⟨h1, h2⟩ := bits_rows P b 0 0 hf0 hw (by omega)
  rw [writes_eq P b 0 (by omega), Nat.zero_xor, Nat.zero_add] at h1 h2
  simp only [List.take_zero, List.nil_append] at h1 h2
  constructor
  · unfold btoks
    rw [bsBitRun_append, h1]
    simp only [bsBitRun]
    rw [bsBitStep_spec _ h2 Tok.sep (fun _ h => by cases h)]
    simp [bsStep]
  · rw [h1, bsDecode_sep hr' _ h2]
    simp [bsStep, attainT_eq_replayMove, decisionMove]

/-- Bit-level reset from ANY register vector. -/
theorem bits_reset (B N r : Nat) (v : Nat → Bool) : bsBitStep B N r v Tok.reset = bsBits B N r (bsInit N) := by
  funext w
  unfold bsBitStep bsBits
  have zr : ∀ j, inB B N r v Tok.reset (sw B N r + j) = decide (j = 2) := by
    intro j; simp only [inB]; rw [if_neg (by omega)]; simp [tokB]
  by_cases hw1 : w < B * N
  · rw [if_pos (by unfold sw; omega), bsForms_board hw1, if_pos hw1]
    simp only [bBoard, eval_mux, rstC', eval_input, zr, eval_const]
    simp [bsInit, boardBits_zero]
  · rw [if_neg hw1]
    by_cases hw2 : w < B * N + B
    · have hw' : w = B * N + (w - B * N) := by omega
      rw [if_pos (by unfold sw; omega), if_pos hw2, hw', bsForms_acc (by omega)]
      simp [bAcc, eval_mux, rstC', zr, bsInit]
    · rw [if_neg hw2]
      by_cases hw3 : w < sw B N r
      · have hw' : w = B * N + B + (w - (B * N + B)) := by omega
        rw [if_pos hw3, if_pos hw3, hw', bsForms_idx (by unfold sw at hw3; omega)]
        simp [bIdx, eval_mux, rstC', zr, bsInit]
      · rw [if_neg hw3, if_neg hw3]

/-- Memory and update counts: B·N + B + r state bits; N + 1 updates per decision. -/
theorem bs_counts (B N r : Nat) (P : List Nat) (hP : P.length = N) :
    sw B N r = B * N + B + r ∧ (btoks P).length = N + 1 ∧ (bsForms B N r).length = sw B N r :=
  ⟨rfl, by rw [btoks_length, hP], bsForms_length B N r⟩


/-! ## Bit-level whole game -/

/-- The move decoded from the outputs at the separator of one decision. -/
def bitMove (B N r r' : Nat) (v : Nat → Bool) (P : List Nat) : Option (Nat × Nat) :=
  (bsDecode B N r r' (inB B N r (bsBitRun B N r v (P.map Tok.row)) Tok.sep)).bind BOut.move

/-- Stateful interaction driven by the BIT-LEVEL machine (register vector v). -/
inductive BitStoreWins (B N r r' : Nat) : (Nat → Bool) → List Nat → Prop
  | intro (v : Nat → Bool) (P R : List Nat) :
      applyM P (bitMove B N r r' v P) = some R → Move P R →
      bsBitRun B N r v (btoks P) = bsBits B N r ⟨P, 0, 0⟩ →
      (∀ P', Move R P' → BitStoreWins B N r r' (bsBits B N r ⟨P, 0, 0⟩) P') → BitStoreWins B N r r' v P

theorem bitStoreWins_sound {B N r r' : Nat} {v : Nat → Bool} {P : List Nat} (h : BitStoreWins B N r r' v P) :
    Win P := by
  induction h with
  | intro v P R _ hm _ _ ih => exact Win.intro P R hm (Lose.intro R ih)

/-- BIT-LEVEL WHOLE-GAME THEOREM: with N < 2^r and N ≤ 2^r', from the encoding of any idle
    state storing a width-B board of N slots, the one-pass bit-level machine wins from every
    nonzero board of width B against every legal opponent. -/
theorem bits_store_wins {B N r r' : Nat} (hN : N < 2 ^ r) (hr' : N ≤ 2 ^ r') :
    ∀ (P : List Nat), P.length = N → Width B P → nimSum P ≠ 0 →
    ∀ b, b.length = N → Width B b → BitStoreWins B N r r' (bsBits B N r ⟨b, 0, 0⟩) P := by
  intro P
  induction P using (measure List.sum).wf.induction with
  | h P ih =>
    intro hP hw h0 b hb hwb
    obtain ⟨h1, h2⟩ := bits_decision (r' := r') hN hr' b hb hwb P hP hw
    obtain ⟨i, v, hd, hz⟩ := (decision_correct P).2.2 h0
    obtain ⟨x, _, _, hmv⟩ := (decision_correct P).2.1 i v hd
    refine BitStoreWins.intro _ P (P.set i v) ?_ hmv h1 ?_
    · unfold bitMove; rw [h2]; simp [hd, applyM]
    · intro P' hm'
      have hlt1 := move_sum_lt hmv
      have hlt2 := move_sum_lt hm'
      exact ih P' (by show P'.sum < P.sum; omega) (by rw [move_length hm', move_length hmv, hP])
        (width_move (width_move hw hmv) hm') (move_from_zero hm' hz) P hP hw

/-- GAME START: one reset update from an ARBITRARY register vector gives the encoding of
    the empty store, from which the bit-level machine wins. -/
theorem bits_store_game {B N r r' : Nat} (hN : N < 2 ^ r) (hr' : N ≤ 2 ^ r') (v : Nat → Bool)
    {P : List Nat} (hP : P.length = N) (hw : Width B P) (h0 : nimSum P ≠ 0) :
    bsBitStep B N r v Tok.reset = bsBits B N r (bsInit N) ∧
    BitStoreWins B N r r' (bsBitStep B N r v Tok.reset) P := by
  refine ⟨bits_reset B N r v, ?_⟩
  rw [bits_reset]
  exact bits_store_wins hN hr' P hP hw h0 _ (by simp [bsInit]) (fun x hx => by
    rw [List.eq_of_mem_replicate hx]; exact Nat.two_pow_pos B)

/-! ## Resources -/

theorem eqI_res (B N r i : Nat) : depth (eqI B N r i) ≤ 2 ∧ size (eqI B N r i) ≤ 2 * r + 1 ∧
    maxInput (eqI B N r i) ≤ sw B N r := by
  have hl : ∀ q, q < r → depth (litEq (input (idxW B N q)) (i.testBit q)) ≤ 1 ∧
      size (litEq (input (idxW B N q)) (i.testBit q)) ≤ 2 ∧ maxInput (litEq (input (idxW B N q)) (i.testBit q)) ≤ sw B N r := by
    intro q hq; unfold litEq idxW sw; split <;> simp <;> omega
  refine ⟨depth_and_le (fun c hc => ?_), ?_, ControllerBits.maxInput_and_le (fun c hc => ?_)⟩
  · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hc; exact (hl q (List.mem_range.mp hq)).1
  · unfold eqI; rw [size_and]
    have := sum_le_len_mul (cs := (List.range r).map (fun q => litEq (input (idxW B N q)) (i.testBit q))) (S := 2)
      (fun c hc => by obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hc; exact (hl q (List.mem_range.mp hq)).2.1)
    simp only [List.length_map, List.length_range] at this; omega
  · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hc; exact (hl q (List.mem_range.mp hq)).2.2

theorem mux_res {c a b : Circ} {dc sc mc da sa ma db sb mb : Nat}
    (hc : depth c ≤ dc ∧ size c ≤ sc ∧ maxInput c ≤ mc) (ha : depth a ≤ da ∧ size a ≤ sa ∧ maxInput a ≤ ma)
    (hb : depth b ≤ db ∧ size b ≤ sb ∧ maxInput b ≤ mb) :
    depth (RolloutExec.mux c a b) ≤ max (dc + 1) (max da db) + 2 ∧ size (RolloutExec.mux c a b) ≤ 2 * sc + sa + sb + 4 ∧
    maxInput (RolloutExec.mux c a b) ≤ max mc (max ma mb) := by
  have h1 := depth_mux_le c a b
  have h2 := size_mux c a b
  have h3 := maxInput_mux c a b
  refine ⟨by omega, by omega, by omega⟩

theorem xor2_res' {a b : Circ} {da sa ma db sb mb : Nat}
    (ha : depth a ≤ da ∧ size a ≤ sa ∧ maxInput a ≤ ma) (hb : depth b ≤ db ∧ size b ≤ sb ∧ maxInput b ≤ mb) :
    depth (xor2 a b) ≤ max da db + 3 ∧ size (xor2 a b) ≤ 2 * sa + 2 * sb + 5 ∧ maxInput (xor2 a b) ≤ max ma mb := by
  obtain ⟨h1, h2, h3⟩ := xor2_res a b
  refine ⟨by omega, by omega, by omega⟩

theorem inp_res {i m : Nat} (h : i + 1 ≤ m) : depth (input i) ≤ 0 ∧ size (input i) ≤ 1 ∧ maxInput (input i) ≤ m := by
  simp; omega

theorem cst_res (b : Bool) : depth (const b) ≤ 0 ∧ size (const b) ≤ 1 ∧ maxInput (const b) ≤ 0 := by simp

/-- UPDATE-FORMULA RESOURCES: depth ≤ 8, size ≤ 4r + 30, inputs below sw + 3 + B. -/
theorem bsForms_res (B N r : Nat) :
    ∀ c ∈ bsForms B N r, depth c ≤ 8 ∧ size c ≤ 4 * r + 30 ∧ maxInput c ≤ sw B N r + 3 + B := by
  have hrow : depth (rowC B N r) ≤ 0 ∧ size (rowC B N r) ≤ 1 ∧ maxInput (rowC B N r) ≤ sw B N r + 3 + B :=
    inp_res (by omega)
  have hsep : depth (sepC B N r) ≤ 0 ∧ size (sepC B N r) ≤ 1 ∧ maxInput (sepC B N r) ≤ sw B N r + 3 + B :=
    inp_res (by omega)
  have hrst : depth (rstC' B N r) ≤ 0 ∧ size (rstC' B N r) ≤ 1 ∧ maxInput (rstC' B N r) ≤ sw B N r + 3 + B :=
    inp_res (by omega)
  have hx : ∀ q, q < B → depth (xC B N r q) ≤ 0 ∧ size (xC B N r q) ≤ 1 ∧ maxInput (xC B N r q) ≤ sw B N r + 3 + B :=
    fun q hq => inp_res (by omega)
  intro c hc
  simp only [bsForms, List.mem_append, List.mem_map, List.mem_range] at hc
  rcases hc with (⟨w, hw, rfl⟩ | ⟨q, hq, rfl⟩) | ⟨q, hq, rfl⟩
  · obtain ⟨e1, e2, e3⟩ := eqI_res B N r (w / B)
    have hc1 : depth (and [rowC B N r, eqI B N r (w / B)]) ≤ 3 ∧ size (and [rowC B N r, eqI B N r (w / B)]) ≤ 2 * r + 3 ∧
        maxInput (and [rowC B N r, eqI B N r (w / B)]) ≤ sw B N r + 3 + B := by
      simp only [rowC, depth_and, size_and, maxInput_and, depth_input, size_input, maxInput_input, List.map_cons,
        List.map_nil, List.sum_cons, List.sum_nil, listMax, List.foldr]
      refine ⟨by omega, by omega, by omega⟩
    have hB : B - 1 - w % B < B := by
      rcases Nat.eq_zero_or_pos B with hB | hB
      · subst hB; simp at hw
      · omega
    have hin := mux_res hc1 (hx _ hB) (inp_res (i := w) (m := sw B N r + 3 + B) (by unfold sw; omega))
    have hout := mux_res hrst (cst_res false) hin
    unfold bBoard
    refine ⟨by omega, by omega, by omega⟩
  · have hxo := xor2_res' (inp_res (i := accW B N q) (m := sw B N r + 3 + B) (by unfold accW sw; omega)) (hx q hq)
    have hm := mux_res hsep (cst_res false) (inp_res (i := accW B N q) (m := sw B N r + 3 + B) (by unfold accW sw; omega))
    have hn := mux_res hrow hxo hm
    have hout := mux_res hrst (cst_res false) hn
    unfold bAcc
    refine ⟨by omega, by omega, by omega⟩
  · have ha : depth (and ((List.range q).map (fun t => input (idxW B N t)))) ≤ 1 ∧
        size (and ((List.range q).map (fun t => input (idxW B N t)))) ≤ r + 1 ∧
        maxInput (and ((List.range q).map (fun t => input (idxW B N t)))) ≤ sw B N r + 3 + B := by
      refine ⟨depth_and_le (fun c hc => by obtain ⟨t, _, rfl⟩ := List.mem_map.mp hc; simp), ?_,
        ControllerBits.maxInput_and_le (fun c hc => ?_)⟩
      · rw [size_and]
        have := sum_le_len_mul (cs := (List.range q).map (fun t => input (idxW B N t))) (S := 1)
          (fun c hc => by obtain ⟨t, _, rfl⟩ := List.mem_map.mp hc; simp)
        simp only [List.length_map, List.length_range] at this; omega
      · obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hc
        have := List.mem_range.mp ht; simp [idxW, sw]; omega
    have hinc := xor2_res' (inp_res (i := idxW B N q) (m := sw B N r + 3 + B) (by unfold idxW sw; omega)) ha
    have hm := mux_res hsep (cst_res false) (inp_res (i := idxW B N q) (m := sw B N r + 3 + B) (by unfold idxW sw; omega))
    have hn := mux_res hrow hinc hm
    have hout := mux_res hrst (cst_res false) hn
    unfold bIdx incF
    refine ⟨by omega, by omega, by omega⟩

def varSz (B N : Nat) : Nat :=
  4 * ((N + 2) * (12 * ((N + 2) * (B + 2) * (B * (2 * B + 3) + 9 + 2)) ^ 8 + 2)) ^ 3

/-- OUTPUT-FORMULA RESOURCES: depth ≤ 16; the selector part has the phase-5 bound. -/
theorem bsOuts_res {B N r r' : Nat} (hr' : N ≤ 2 ^ r') :
    ∀ c ∈ bsOuts B N r r', depth c ≤ 16 ∧ size c ≤ varSz B N + 1 ∧ maxInput c ≤ sw B N r + 3 + B := by
  have hb : BinBound (varBin B N r') N B r' (4 + 9 + 3) (varSz B N) (B * N + B) :=
    encode_bound_sel (varSel_bound (B := B) (N := N)) hr'
  intro c hc
  simp only [bsOuts, List.mem_append, List.mem_cons, List.mem_nil_iff, or_false, List.mem_map, List.mem_range] at hc
  rcases hc with (rfl | ⟨q, hq, rfl⟩) | hc
  · simp [sepC, sw]; omega
  · simp [accW, sw]; omega
  · obtain ⟨a, b, d⟩ := hb.all c hc
    refine ⟨by omega, by omega, by unfold sw; omega⟩

/-- Members (B, N), B, N ≥ 1, r = r' = log₂N + 1; input = registers + token. -/
def bsLen : Nat × Nat → Nat := fun i => sw i.1 i.2 (rIdx i.2) + 3 + i.1
def bsAll (i : Nat × Nat) : List Circ := bsForms i.1 i.2 (rIdx i.2) ++ bsOuts i.1 i.2 (rIdx i.2) (rIdx i.2)

theorem bsLen_pos (i : Nat × Nat) (_hi : restAdm i) : 1 ≤ bsLen i := by unfold bsLen; omega
theorem bs_leaves (k : Nat) (i : Nat × Nat) (hi : restAdm i) : leafBN k i ≤ bsLen i := by
  have hB := Nat.mul_le_mul_left i.1 hi.2
  have hN := Nat.mul_le_mul_right i.2 hi.1
  match k with
  | 0 => show i.1 ≤ bsLen i; unfold bsLen sw; omega
  | 1 => show i.2 ≤ bsLen i; unfold bsLen sw; simp at hN; omega
  | _ + 2 => show rIdx i.2 ≤ bsLen i; unfold bsLen sw; omega

def varSzE {ι : Type} : PE ι := 4 * ((vN + 2) * (12 * ((vN + 2) * (vB + 2) * (vB * (2 * vB + 3) + 9 + 2)) ^ 8 + 2)) ^ 3

def bsSizeE {ι : Type} : PE ι := (vB * vN + vB + vr) * (4 * vr + 30) + (1 + vB + (1 + vr + vB)) * (varSzE + 1)

theorem bsSizeE_eval (i : Nat × Nat) : PE.eval leafBN bsSizeE i =
    sw i.1 i.2 (rIdx i.2) * (4 * rIdx i.2 + 30) + (1 + i.1 + (1 + rIdx i.2 + i.1)) * (varSz i.1 i.2 + 1) := rfl

theorem bsAll_tsize (i : Nat × Nat) :
    tsize (bsAll i) ≤ sw i.1 i.2 (rIdx i.2) * (4 * rIdx i.2 + 30) + (1 + i.1 + (1 + rIdx i.2 + i.1)) * (varSz i.1 i.2 + 1) := by
  unfold bsAll tsize
  rw [List.map_append, List.sum_append_nat]
  have h1 := sum_le_len_mul (cs := bsForms i.1 i.2 (rIdx i.2)) (S := 4 * rIdx i.2 + 30) (fun c hc => (bsForms_res _ _ _ c hc).2.1)
  have h2 := sum_le_len_mul (cs := bsOuts i.1 i.2 (rIdx i.2) (rIdx i.2)) (S := varSz i.1 i.2 + 1)
    (fun c hc => (bsOuts_res (rIdx_width i.2) c hc).2.1)
  have hl : (bsOuts i.1 i.2 (rIdx i.2) (rIdx i.2)).length = 1 + i.1 + (1 + rIdx i.2 + i.1) := by
    have hb := encode_bound_sel (varSel_bound (B := i.1) (N := i.2)) (rIdx_width i.2)
    have e1 : (varBin i.1 i.2 (rIdx i.2)).idx.length = rIdx i.2 := hb.idx_len
    have e2 : (varBin i.1 i.2 (rIdx i.2)).val.length = i.1 := hb.val_len
    unfold bsOuts bForms
    simp only [List.length_append, List.length_cons, List.length_map, List.length_range, List.length_nil, e1, e2]
    omega
  rw [bsForms_length] at h1; rw [hl] at h2
  omega

/-- BOARD-STORAGE FAMILY CERTIFICATE: update and output formulas together have depth ≤ 16,
    read only the registers and one token, and have total size polynomial in that width. -/
theorem bs_ac0 : AC0Fam restAdm bsLen bsAll 16 := by
  refine ⟨bsLen_pos, fun i _ c hc => ?_, fun i _ c hc => ?_, ?_⟩
  · rcases List.mem_append.mp hc with h | h
    · have := (bsForms_res _ _ _ c h).1; omega
    · exact (bsOuts_res (rIdx_width i.2) c h).1
  · rcases List.mem_append.mp hc with h | h
    · exact (bsForms_res _ _ _ c h).2.2
    · exact (bsOuts_res (rIdx_width i.2) c h).2.2
  · exact polyIn_mono (fun i _ => bsAll_tsize i)
      (polyE bsLen_pos leafBN bs_leaves bsSizeE _ (fun i => (bsSizeE_eval i).symm))

def bsNet (i : Nat × Nat) : List Layer := compileF (bsAll i)

/-- The network computes exactly the formulas bsAll (outputs beyond them are 0). -/
theorem bsNet_eval (i : Nat × Nat) (x : Nat → Bool) {k : Nat} (hk : k < (bsAll i).length) :
    evalNet (bsNet i) x k = eval x (bsAll i)[k] := compileF_eval (bsAll i) x hk

theorem bsNet_evalD (i : Nat × Nat) (x : Nat → Bool) {k : Nat} (hk : k < (bsAll i).length) :
    evalNet (bsNet i) x k = eval x ((bsAll i).getD k (const false)) := by
  rw [bsNet_eval i x hk, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some]

/-- NETWORK STEP = BIT STEP: the first sw network outputs on (state, token) are the next
    register vector, so bsBitStep_spec applies to the network. -/
theorem bsNet_step (B N : Nat) (v : Nat → Bool) (t : Tok) (w : Nat) :
    (if w < sw B N (rIdx N) then evalNet (bsNet (B, N)) (inB B N (rIdx N) v t) w else false) =
      bsBitStep B N (rIdx N) v t w := by
  unfold bsBitStep
  split
  · rename_i hw
    have hl : (bsForms B N (rIdx N)).length = sw B N (rIdx N) := bsForms_length B N (rIdx N)
    have hk : w < (bsAll (B, N)).length := by
      show w < (bsForms B N (rIdx N) ++ bsOuts B N (rIdx N) (rIdx N)).length
      rw [List.length_append]; omega
    rw [bsNet_evalD (B, N) _ hk]
    show eval _ ((bsForms B N (rIdx N) ++ bsOuts B N (rIdx N) (rIdx N)).getD w (const false)) = _
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega)]
  · rfl

/-- NETWORK OUTPUTS: network output sw + k is output formula k of bsOuts (separator flag,
    accumulator bits, then the selector formulas read by bsDecode). -/
theorem bsNet_outputs (B N : Nat) (x : Nat → Bool) {k : Nat} (hk : k < (bsOuts B N (rIdx N) (rIdx N)).length) :
    evalNet (bsNet (B, N)) x (sw B N (rIdx N) + k) = eval x ((bsOuts B N (rIdx N) (rIdx N)).getD k (const false)) := by
  have hl : (bsForms B N (rIdx N)).length = sw B N (rIdx N) := bsForms_length B N (rIdx N)
  have hk' : sw B N (rIdx N) + k < (bsAll (B, N)).length := by
    show sw B N (rIdx N) + k < (bsForms B N (rIdx N) ++ bsOuts B N (rIdx N) (rIdx N)).length
    rw [List.length_append]; omega
  rw [bsNet_evalD (B, N) _ hk']
  show eval x ((bsForms B N (rIdx N) ++ bsOuts B N (rIdx N) (rIdx N)).getD (sw B N (rIdx N) + k) (const false)) = _
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hl,
    Nat.add_sub_cancel_left]

/-- BOARD-STORAGE NETWORK CERTIFICATE (W = 1, ≤ 34 layers). -/
theorem bs_net : NetFam restAdm bsLen bsNet 1 34 := by
  have spec := fun i => compileF_spec (bsAll i) (bsLen i) 16
    (fun c hc => by
      rcases List.mem_append.mp hc with h | h
      · exact (bsForms_res _ _ _ c h).2.2
      · exact (bsOuts_res (rIdx_width i.2) c h).2.2)
    (fun c hc => by
      rcases List.mem_append.mp hc with h | h
      · have := (bsForms_res _ _ _ c h).1; omega
      · exact (bsOuts_res (rIdx_width i.2) c h).1)
  have hT := polyE bsLen_pos leafBN bs_leaves bsSizeE _ (fun i => (bsSizeE_eval i).symm)
  refine ⟨bsLen_pos, fun i _ => (spec i).2.2.1, fun i _ => (spec i).2.2.2.1, fun i _ => (spec i).2.2.2.2.1, ?_, ?_⟩
  · obtain ⟨c, k, h⟩ := polyIn_add bsLen_pos hT (polyIn_leaf (fun i _ => Nat.le_refl (bsLen i)))
    refine ⟨c, k, fun i hi => netBounded_mono (spec i).2.2.2.2.2.1 ?_⟩
    have := bsAll_tsize i; have := h i hi; dsimp only at *; unfold tsize at *; omega
  · refine polyIn_mono (fun i _ => ?_) (polyIn_mul (polyIn_const _ _ 34) hT)
    have g := (spec i).2.2.2.2.2.2
    have h1 := bsAll_tsize i
    have h2 := length_le_tsize (bsAll i)
    unfold tsize at h1 h2
    show gateCount (compileF (bsAll i)) ≤ 34 * _
    omega

/-! ## Axiom audit -/

#print axioms btoks_length
#print axioms bsRun_append
#print axioms bsRun_rows
#print axioms take_set_succ
#print axioms writes_eq
#print axioms bs_decision
#print axioms bs_reset
#print axioms storeWins_sound
#print axioms store_wins
#print axioms bsForms_length
#print axioms bsForms_board
#print axioms bsForms_acc
#print axioms bsForms_idx
#print axioms eqI_eval
#print axioms eq_of_low_bits
#print axioms boardBits_set'
#print axioms boardBits_zero
#print axioms bsBitStep_spec
#print axioms bsDecode_sep
#print axioms bsBitRun_append
#print axioms bits_rows
#print axioms bits_decision
#print axioms bits_reset
#print axioms bs_counts
#print axioms bitStoreWins_sound
#print axioms bits_store_wins
#print axioms bits_store_game
#print axioms eqI_res
#print axioms mux_res
#print axioms xor2_res'
#print axioms inp_res
#print axioms cst_res
#print axioms bsForms_res
#print axioms bsOuts_res
#print axioms bsLen_pos
#print axioms bs_leaves
#print axioms bsSizeE_eval
#print axioms bsAll_tsize
#print axioms bs_ac0
#print axioms bsNet_eval
#print axioms bsNet_evalD
#print axioms bsNet_step
#print axioms bsNet_outputs
#print axioms bs_net


