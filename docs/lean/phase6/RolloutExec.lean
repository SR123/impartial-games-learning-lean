import Barrier

/- Phase 6, Priority 2: a finite-register rollout executor.  Written by Claude
   (10 October 2026).  Lean 4.26.0, core/Std only.

   The phase-5 loop `WholeGame.rollMoves` is an exact semantic specification, but it
   uses Nat fuel P.sum + 1 and reads the low bit of an unbounded move count.  Here the
   rollout is executed by a REGISTER MACHINE with B·N + 2 state bits:
     board (N heaps × B bits, the boardBits layout), par (one outcome bit), halt (one bit),
   and one SHALLOW STEP CIRCUIT whose extra inputs are a reset bit and an external board
   (loaded on reset).  On each clock step with halt = 0 the circuit evaluates the
   compiled policy selector polBin (the actual phase-5 formulas) on the board bits;
   if it returns a legal binary move (valid ∧ index < N), the addressed heap is replaced
   by the value bits (index comparison by the equality decoder, multiplexed write) and
   par toggles; otherwise halt is set.  With halt = 1 the registers are unchanged.  On
   reset the board is loaded and par, halt are cleared, from ANY register contents.

   The scheduler is the loop "while halt = 0, clock the step circuit": it reads one bit
   and keeps no counter.  The theorems show that it stops after exactly L + 1 policy
   evaluations (L simulated moves plus the terminal test), that the fixed bound
   N(2^B − 1) + 1 (a function of B and N only) never runs out, and that par is then the
   rollout outcome.  No P.sum oracle and no unbounded arithmetic gate is used: Lean's
   loop fuel is the fixed clock bound and is never exhausted.

   The step circuit is also compiled to a W = 1 threshold network.  B such executions
   feed the compiled multi-head readout network; the result equals decisionMove and wins
   against every legal opponent.  Per step the work is one evaluation of a depth-≤28
   formula list (≤ 58 network layers, step_net); the number of sequential steps is
   Σ_j (L_j + 1) ≤ B (N(2^B − 1) + 1), which is NOT constant: total sequential depth
   grows with the board (unbounded_steps). -/

namespace NimAudit
namespace RolloutExec

open Game Rollout Prob Attain Recurrent AC0 AC0.Circ CorrBridge AttainCircuit Bridge SelectCircuit
  BinReadout Controller ControllerBits PriorityEncoder ThresholdNet ThresholdInst FiniteNet WholeGame
  Family Barrier

/-! ## The semantic register machine -/

/-- Registers of the rollout machine. -/
structure RS where
  board : List Nat
  par : Bool
  halted : Bool

/-- One clock step, driven by a selector in index form (pol = policyIdx j for π_j). -/
def rsStep (pol : List Nat → Option (Nat × Nat)) (s : RS) : RS :=
  if s.halted then s else
    match pol s.board with
    | none => ⟨s.board, s.par, true⟩
    | some m => ⟨s.board.set m.1 m.2, !s.par, false⟩

/-- The scheduler: while halt = 0, clock the step; count the clocked steps (each step
    is one policy evaluation).  The Nat argument is Lean's termination fuel. -/
def untilHalt (pol : List Nat → Option (Nat × Nat)) : Nat → RS → RS × Nat
  | 0, s => (s, 0)
  | f + 1, s => if s.halted then (s, 0) else
      ((untilHalt pol f (rsStep pol s)).1, (untilHalt pol f (rsStep pol s)).2 + 1)

theorem untilHalt_halted (pol : List Nat → Option (Nat × Nat)) (s : RS) (hs : s.halted = true) :
    ∀ f, untilHalt pol f s = (s, 0)
  | 0 => rfl
  | f + 1 => by simp [untilHalt, hs]

theorem rolloutWinner_none' {j : Nat} {p : List Nat} (h : policyStep j p = none) : rolloutWinner j p = false := by
  rw [rolloutWinner]; split <;> simp_all

theorem rolloutWinner_some' {j : Nat} {p q : List Nat} (h : policyStep j p = some q) :
    rolloutWinner j p = !rolloutWinner j q := by
  rw [rolloutWinner]; split <;> simp_all

/-- SEMANTIC EXECUTION: from (P, b, halt = 0), with fuel at least L + 1 (L = number of
    simulated moves), the scheduler stops with halt = 1, par = b XOR outcome, after
    exactly L + 1 clocked steps. -/
theorem untilHalt_spec (j : Nat) : ∀ (f : Nat) (P : List Nat) (b : Bool), rolloutMoves j P + 1 ≤ f →
    (untilHalt (policyIdx j) f ⟨P, b, false⟩).1.par = xor b (rolloutWinner j P) ∧
    (untilHalt (policyIdx j) f ⟨P, b, false⟩).1.halted = true ∧
    (untilHalt (policyIdx j) f ⟨P, b, false⟩).2 = rolloutMoves j P + 1
  | 0, P, b, h => by omega
  | f + 1, P, b, h => by
    simp only [untilHalt, Bool.false_eq_true, if_false]
    cases hp : policyIdx j P with
    | none =>
      have hs : policyStep j P = none := by rw [← policyIdx_step, hp]; rfl
      have e : rsStep (policyIdx j) ⟨P, b, false⟩ = ⟨P, b, true⟩ := by simp [rsStep, hp]
      rw [e, untilHalt_halted _ _ rfl f]
      simp [rolloutWinner_none' hs, rolloutMoves_none hs]
    | some m =>
      have hs : policyStep j P = some (P.set m.1 m.2) := by rw [← policyIdx_step, hp]; rfl
      have e : rsStep (policyIdx j) ⟨P, b, false⟩ = ⟨P.set m.1 m.2, !b, false⟩ := by simp [rsStep, hp]
      rw [e]
      have hL := rolloutMoves_some hs
      obtain ⟨h1, h2, h3⟩ := untilHalt_spec j f (P.set m.1 m.2) (!b) (by omega)
      refine ⟨by rw [h1, rolloutWinner_some' hs]; cases b <;> simp, h2, by rw [h3, hL]⟩

/-- The fixed clock bound (a function of B and N only). -/
def clockBound (B N : Nat) : Nat := N * (2 ^ B - 1) + 1

theorem clock_ok {B j : Nat} {P : List Nat} (hw : Width B P) : rolloutMoves j P + 1 ≤ clockBound B P.length := by
  have := rolloutMoves_le (j := j) hw; unfold clockBound; omega

/-! ## The step circuit -/

def mux (c a b : Circ) : Circ := or [and [c, a], and [not c, b]]

theorem eval_mux (z : Nat → Bool) (c a b : Circ) :
    eval z (mux c a b) = if eval z c then eval z a else eval z b := by
  unfold mux; cases h : eval z c <;> simp [h]

/-- A legal binary move exists: valid ∧ (index < N), via the equality decoder. -/
def mvC (S : BCirc) (N : Nat) : Circ := and [S.valid, or ((List.range N).map (decodeC S.idx))]
/-- Active step: halt = 0 and a move exists. -/
def actC (B N : Nat) (S : BCirc) : Circ := and [not (input (B * N + 1)), mvC S N]
/-- The reset input wire. -/
def rstC (B N : Nat) : Circ := input (B * N + 2)
/-- New board bit w = B·i + p: on reset the external bit; if active and the index is i,
    the selector's value bit p; otherwise the old bit. -/
def boardC (B N : Nat) (S : BCirc) (w : Nat) : Circ :=
  mux (rstC B N) (input (B * N + 3 + w))
    (mux (and [actC B N S, decodeC S.idx (w / B)]) (getC S.val (w % B)) (input w))
/-- New outcome bit: toggled on an active step, cleared on reset. -/
def parC (B N : Nat) (S : BCirc) : Circ := and [not (rstC B N), xor2 (actC B N S) (input (B * N))]
/-- New halt bit: set exactly when the step is not active, cleared on reset. -/
def haltC (B N : Nat) (S : BCirc) : Circ := and [not (rstC B N), not (actC B N S)]

/-- THE STEP CIRCUIT: B·N board outputs, then par, then halt. -/
def stepForms (B N : Nat) (S : BCirc) : List Circ :=
  (List.range (B * N)).map (boardC B N S) ++ [parC B N S, haltC B N S]

theorem stepForms_length (B N : Nat) (S : BCirc) : (stepForms B N S).length = B * N + 2 := by
  simp [stepForms]

/-- Encoding of the registers: board bits, then par (wire B·N), then halt (wire B·N+1). -/
def rsBits (B N : Nat) (s : RS) : Nat → Bool := fun w =>
  if w < B * N then boardBits B s.board w else if w = B * N then s.par else if w = B * N + 1 then s.halted
  else false

/-- Step input: registers (wires < B·N+2), reset (wire B·N+2), external board (from B·N+3). -/
def stepIn (B N : Nat) (v : Nat → Bool) (rst : Bool) (ext : List Nat) : Nat → Bool := fun w =>
  if w < B * N + 2 then v w else if w = B * N + 2 then rst else boardBits B ext (w - (B * N + 3))

/-- One clocked update of the register vector (zero beyond the register wires). -/
def bitStep (B N : Nat) (S : BCirc) (v : Nat → Bool) (rst : Bool) (ext : List Nat) : Nat → Bool := fun w =>
  if w < B * N + 2 then eval (stepIn B N v rst ext) ((stepForms B N S).getD w (const false)) else false

/-- What the step circuit needs from a selector S in binary format. -/
structure PolSpec (S : BCirc) (B N : Nat) (pol : List Nat → Option (Nat × Nat)) : Prop where
  idx_w : N ≤ 2 ^ S.idx.length
  val_len : S.val.length = B
  reads : ∀ c ∈ bForms S, maxInput c ≤ B * N
  sem : ∀ P : List Nat, P.length = N → Width B P → binSem S N (boardBits B P) = pol P

theorem polSpec_polBin (B N j : Nat) : PolSpec (polBin B N j (rIdx N)) B N (policyIdx j) := by
  have hb := polBin_bound (B := B) (N := N) (j := j) (rIdx_width N)
  exact ⟨by rw [hb.idx_len]; exact rIdx_width N, hb.val_len, fun c hc => (hb.all c hc).2.2,
    fun P hP hw => (polBin_correct (rIdx_width N) hP hw).1⟩

/-! ### Evaluation lemmas -/

theorem stepForms_board {B N : Nat} {S : BCirc} {w : Nat} (hw : w < B * N) :
    (stepForms B N S).getD w (const false) = boardC B N S w := by
  unfold stepForms
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simpa using hw), List.getElem?_map,
    List.getElem?_range hw]
  rfl

theorem stepForms_par (B N : Nat) (S : BCirc) : (stepForms B N S).getD (B * N) (const false) = parC B N S := by
  unfold stepForms
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp)]
  simp

theorem stepForms_halt (B N : Nat) (S : BCirc) :
    (stepForms B N S).getD (B * N + 1) (const false) = haltC B N S := by
  unfold stepForms
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp)]
  simp

theorem any_decode (z : Nat → Bool) (idx : List Circ) {N : Nat} (hw : N ≤ 2 ^ idx.length) :
    ((List.range N).map (decodeC idx)).any (eval z) = decide (toNatBE (idx.map (eval z)) < N) := by
  apply Bool.eq_iff_iff.mpr
  rw [List.any_eq_true, decide_eq_true_iff]
  constructor
  · rintro ⟨c, hc, he⟩
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hc
    have hi' := List.mem_range.mp hi
    rw [decodeC_eval z idx (by omega), decide_eq_true_iff] at he
    omega
  · intro h
    refine ⟨decodeC idx (toNatBE (idx.map (eval z))), List.mem_map.mpr ⟨_, List.mem_range.mpr h, rfl⟩, ?_⟩
    rw [decodeC_eval z idx (by omega)]; simp

theorem eval_mvC (S : BCirc) {N : Nat} (hw : N ≤ 2 ^ S.idx.length) (z : Nat → Bool) :
    eval z (mvC S N) = (binSem S N z).isSome := by
  unfold mvC binSem
  simp only [eval_and, eval_or, List.all_cons, List.all_nil, Bool.and_true]
  rw [any_decode z S.idx hw]
  by_cases hv : eval z S.valid
  · simp only [hv, Bool.true_and, if_true]
    by_cases ht : toNatBE (S.idx.map (eval z)) < N <;> simp [ht]
  · simp [hv]

theorem maxInput_decodeC {idx : List Circ} {M : Nat} (h : ∀ c ∈ idx, maxInput c ≤ M) (i : Nat) :
    maxInput (decodeC idx i) ≤ M := by
  unfold decodeC
  apply ControllerBits.maxInput_and_le; intro c hc
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hc
  have hm : getC idx q ∈ idx := getC_mem (List.mem_range.mp hq)
  unfold litEq; split <;> simp [h _ hm]

theorem maxInput_getC_le {cs : List Circ} {M : Nat} (h : ∀ c ∈ cs, maxInput c ≤ M) (i : Nat) :
    maxInput (getC cs i) ≤ M := by
  unfold getC; rw [List.getD_eq_getElem?_getD]
  cases hc : cs[i]? with
  | none => simp
  | some c => exact h c (List.mem_of_getElem? hc)

theorem getD_set_nat (P : List Nat) (i v k : Nat) (hi : i < P.length) :
    (P.set i v).getD k 0 = if k = i then v else P.getD k 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_set]
  by_cases hk : k = i
  · subst hk; simp [hi]
  · simp [Ne.symm hk, hk]

theorem boardBits_set {B N : Nat} {P : List Nat} (hl : P.length = N) {i w : Nat} (v : Nat) (hi : i < N)
    (hw : w < B * N) :
    boardBits B (P.set i v) w = if w / B = i then v.testBit (B - 1 - w % B) else boardBits B P w := by
  unfold boardBits
  rw [List.length_set, hl, if_pos hw, if_pos hw, getD_set_nat _ _ _ _ (by rw [hl]; exact hi)]
  by_cases h : w / B = i <;> simp [h]

/-- ONE-STEP REFINEMENT (no reset): for every register state whose board has N heaps of
    width B, the step circuit computes the encoding of the semantic step. -/
theorem bitStep_run {S : BCirc} {B N : Nat} {pol : List Nat → Option (Nat × Nat)} (hS : PolSpec S B N pol)
    (s : RS) (hl : s.board.length = N) (hw : Width B s.board) (ext : List Nat) :
    bitStep B N S (rsBits B N s) false ext = rsBits B N (rsStep pol s) := by
  -- the input vector and its basic values
  let z := stepIn B N (rsBits B N s) false ext
  have zlow : ∀ i, i < B * N → z i = boardBits B s.board i := by
    intro i hi; simp only [z, stepIn, rsBits]; rw [if_pos (by omega), if_pos hi]
  have zpar : z (B * N) = s.par := by
    simp only [z, stepIn]; rw [if_pos (by omega)]; unfold rsBits
    rw [if_neg (by omega), if_pos rfl]
  have zhalt : z (B * N + 1) = s.halted := by
    simp only [z, stepIn]; rw [if_pos (by omega)]; unfold rsBits
    rw [if_neg (by omega), if_neg (by omega), if_pos rfl]
  have zrst : z (B * N + 2) = false := by simp [z, stepIn]
  have hcongr : ∀ c, maxInput c ≤ B * N → eval z c = eval (boardBits B s.board) c :=
    fun c hc => eval_congr_below _ _ c (fun i hi => zlow i (by omega))
  have hidx : ∀ c ∈ S.idx, maxInput c ≤ B * N := fun c hc => hS.reads c (by simp [bForms, hc])
  have hval : ∀ c ∈ S.val, maxInput c ≤ B * N := fun c hc => hS.reads c (by simp [bForms, hc])
  have hvalid : maxInput S.valid ≤ B * N := hS.reads _ (by simp [bForms])
  have hmv : eval z (mvC S N) = (pol s.board).isSome := by
    rw [hcongr _ (by
      unfold mvC; apply ControllerBits.maxInput_and_le; intro c hc
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc
      rcases hc with rfl | rfl
      · exact hvalid
      · apply ControllerBits.maxInput_or_le; intro c hc
        obtain ⟨i, _, rfl⟩ := List.mem_map.mp hc
        exact maxInput_decodeC hidx i), eval_mvC S hS.idx_w, hS.sem _ hl hw]
  have hact : eval z (actC B N S) = (!s.halted && (pol s.board).isSome) := by
    simp only [actC, eval_and, eval_not, eval_input, List.all_cons, List.all_nil, Bool.and_true, zhalt, hmv]
  have hdec : ∀ i', i' < N → eval z (decodeC S.idx i') =
      decide (toNatBE (S.idx.map (eval (boardBits B s.board))) = i') := by
    intro i' hi'
    rw [hcongr _ (maxInput_decodeC hidx i'), decodeC_eval _ _ (by have := hS.idx_w; omega)]
  have hvbit : ∀ p, eval z (getC S.val p) = (S.val.map (eval (boardBits B s.board))).getD p false := by
    intro p; rw [hcongr _ (maxInput_getC_le hval p), eval_getC]
  funext w
  unfold bitStep rsBits
  by_cases hw1 : w < B * N
  · -- a board wire
    rw [if_pos (by omega), stepForms_board hw1, if_pos hw1]
    show eval z (boardC B N S w) = _
    simp only [boardC, eval_mux, rstC, eval_input, zrst, Bool.false_eq_true, if_false, eval_and,
      List.all_cons, List.all_nil, Bool.and_true, hact]
    have hwi : w / B < N := by
      rcases Nat.eq_zero_or_pos B with hB | hB
      · subst hB; simp at hw1
      · exact (Nat.div_lt_iff_lt_mul hB).2 (by rw [Nat.mul_comm]; exact hw1)
    rw [zlow w hw1, hdec _ hwi]
    unfold rsStep
    by_cases hh : s.halted
    · simp [hh]
    · simp only [hh, Bool.not_false, Bool.true_and, Bool.false_eq_true, if_false]
      have hsem := hS.sem _ hl hw
      cases hp : pol s.board with
      | none => simp
      | some m =>
        obtain ⟨i, v⟩ := m
        simp only [Option.isSome_some, Bool.true_and, decide_eq_true_eq]
        -- decode the binary semantics
        rw [hp] at hsem
        unfold binSem at hsem
        split at hsem
        · split at hsem
          · next _ hlt =>
            simp only [Option.some.injEq, Prod.mk.injEq] at hsem
            obtain ⟨hi, hv⟩ := hsem
            have hiN : i < N := by rw [← hi]; exact hlt
            rw [boardBits_set hl v hiN hw1]
            by_cases hc : toNatBE (S.idx.map (eval (boardBits B s.board))) = w / B
            · rw [if_pos hc, hvbit]
              have hwi' : w / B = i := by rw [← hc, hi]
              rw [if_pos hwi', ← hv]
              have hpB : w % B < B := Nat.mod_lt _ (by
                rcases Nat.eq_zero_or_pos B with hB | hB
                · subst hB; simp at hw1
                · exact hB)
              have := testBit_toNatBE (S.val.map (eval (boardBits B s.board))) (w % B) (by simp [hS.val_len, hpB])
              simp only [List.length_map, hS.val_len] at this
              rw [this]
            · rw [if_neg hc]
              have hwi' : ¬ w / B = i := by rw [← hi]; exact fun h => hc h.symm
              rw [if_neg hwi']
          · cases hsem
        · cases hsem
  · rw [if_neg hw1]
    by_cases hw2 : w = B * N
    · subst hw2
      rw [if_pos (by omega), stepForms_par, if_pos rfl]
      show eval z (parC B N S) = _
      simp only [parC, rstC, eval_and, eval_not, eval_input, eval_xor2, List.all_cons, List.all_nil,
        Bool.and_true, zrst, Bool.not_false, Bool.true_and, hact, zpar]
      unfold rsStep
      by_cases hh : s.halted
      · simp [hh]
      · cases pol s.board <;> simp [hh]
    · rw [if_neg hw2]
      by_cases hw3 : w = B * N + 1
      · subst hw3
        rw [if_pos (by omega), stepForms_halt, if_pos rfl]
        show eval z (haltC B N S) = _
        simp only [haltC, rstC, eval_and, eval_not, eval_input, List.all_cons, List.all_nil,
          Bool.and_true, zrst, Bool.not_false, Bool.true_and, hact]
        unfold rsStep
        by_cases hh : s.halted
        · simp [hh]
        · cases pol s.board <;> simp [hh]
      · rw [if_neg hw3, if_neg (by omega)]

/-- RESET: from ANY register vector, a reset step loads the external board and clears par
    and halt. -/
theorem bitStep_reset (B N : Nat) (S : BCirc) (v : Nat → Bool) (ext : List Nat) :
    bitStep B N S v true ext = rsBits B N ⟨ext, false, false⟩ := by
  funext w
  unfold bitStep rsBits
  have zrst : stepIn B N v true ext (B * N + 2) = true := by simp [stepIn]
  by_cases hw1 : w < B * N
  · rw [if_pos (by omega), stepForms_board hw1, if_pos hw1]
    simp only [boardC, eval_mux, rstC, eval_input, zrst, if_true]
    simp only [stepIn]
    rw [if_neg (by omega), if_neg (by omega)]
    congr 1; omega
  · rw [if_neg hw1]
    by_cases hw2 : w = B * N
    · subst hw2
      rw [if_pos (by omega), stepForms_par, if_pos rfl]
      simp [parC, rstC, zrst]
    · rw [if_neg hw2]
      by_cases hw3 : w = B * N + 1
      · subst hw3
        rw [if_pos (by omega), stepForms_halt, if_pos rfl]
        simp [haltC, rstC, zrst]
      · rw [if_neg hw3, if_neg (by omega)]

/-! ## The scheduler at bit level -/

/-- Generic "while halt = 0, clock the step" loop on register vectors, reading only the
    halt wire; returns the final vector and the number of clocked steps. -/
def loopUntil (step : (Nat → Bool) → (Nat → Bool)) (hw : Nat) : Nat → (Nat → Bool) → (Nat → Bool) × Nat
  | 0, v => (v, 0)
  | f + 1, v => if v hw then (v, 0) else
      ((loopUntil step hw f (step v)).1, (loopUntil step hw f (step v)).2 + 1)

theorem loopUntil_congr {step step' : (Nat → Bool) → (Nat → Bool)} (h : ∀ v, step v = step' v) (hw : Nat) :
    ∀ f v, loopUntil step hw f v = loopUntil step' hw f v
  | 0, _ => rfl
  | f + 1, v => by simp only [loopUntil, h v, loopUntil_congr h hw f (step' v)]

theorem rsStep_inv {S : BCirc} {B N : Nat} {pol : List Nat → Option (Nat × Nat)} (hS : PolSpec S B N pol)
    (s : RS) (hl : s.board.length = N) (hw : Width B s.board) :
    (rsStep pol s).board.length = N ∧ Width B (rsStep pol s).board := by
  unfold rsStep
  by_cases hh : s.halted
  · simp [hh, hl, hw]
  · simp only [hh, Bool.false_eq_true, if_false]
    cases hp : pol s.board with
    | none => exact ⟨hl, hw⟩
    | some m =>
      obtain ⟨i, v⟩ := m
      have hsem := hS.sem _ hl hw
      rw [hp] at hsem
      have hv : v < 2 ^ B := by
        unfold binSem at hsem
        split at hsem
        · split at hsem
          · simp only [Option.some.injEq, Prod.mk.injEq] at hsem
            rw [← hsem.2]
            have := toNatBE_lt (S.val.map (eval (boardBits B s.board)))
            simpa [hS.val_len] using this
          · cases hsem
        · cases hsem
      refine ⟨by simp [hl], fun x hx => ?_⟩
      rcases List.mem_or_eq_of_mem_set hx with h | h
      · exact hw x h
      · rw [h]; exact hv

/-- RUN REFINEMENT: the bit-level scheduler with the step circuit computes the encoding
    of the semantic scheduler, step count included. -/
theorem loop_refines {S : BCirc} {B N : Nat} {pol : List Nat → Option (Nat × Nat)} (hS : PolSpec S B N pol) :
    ∀ (f : Nat) (s : RS), s.board.length = N → Width B s.board →
    loopUntil (fun v => bitStep B N S v false []) (B * N + 1) f (rsBits B N s) =
      (rsBits B N (untilHalt pol f s).1, (untilHalt pol f s).2)
  | 0, s, _, _ => rfl
  | f + 1, s, hl, hw => by
    have hh : rsBits B N s (B * N + 1) = s.halted := by
      unfold rsBits; rw [if_neg (by omega), if_neg (by omega), if_pos rfl]
    simp only [loopUntil, untilHalt, hh]
    by_cases hs : s.halted
    · simp [hs]
    · simp only [hs, Bool.false_eq_true, if_false]
      rw [bitStep_run hS s hl hw []]
      obtain ⟨hl', hw'⟩ := rsStep_inv hS s hl hw
      rw [loop_refines hS f (rsStep pol s) hl' hw']

/-! ## The executor (Boolean step circuit) -/

/-- Finite-register execution of rollout j on board P (N = |P|): one reset step loading P
    from an arbitrary register vector v0, then the halting loop with the fixed clock
    bound.  Returns the final register vector and the number of clocked policy steps. -/
def execRoll (B j : Nat) (v0 : Nat → Bool) (P : List Nat) : (Nat → Bool) × Nat :=
  loopUntil (fun v => bitStep B P.length (polBin B P.length j (rIdx P.length)) v false []) (B * P.length + 1)
    (clockBound B P.length) (bitStep B P.length (polBin B P.length j (rIdx P.length)) v0 true P)

/-- EXECUTOR THEOREM: from any initial register contents, the finite-register executor
    ends with halt = 1, its outcome bit equal to the rollout outcome RO_{π_j}(P), after
    exactly L + 1 policy evaluations (L simulated moves and the terminal test). -/
theorem execRoll_spec {B j : Nat} (v0 : Nat → Bool) {P : List Nat} (hw : Width B P) :
    (execRoll B j v0 P).1 (B * P.length) = rolloutWinner j P ∧
    (execRoll B j v0 P).1 (B * P.length + 1) = true ∧
    (execRoll B j v0 P).2 = rolloutMoves j P + 1 := by
  unfold execRoll
  rw [bitStep_reset, loop_refines (polSpec_polBin B P.length j) _ _ rfl hw]
  obtain ⟨h1, h2, h3⟩ := untilHalt_spec j (clockBound B P.length) P false (clock_ok hw)
  refine ⟨?_, ?_, h3⟩
  · show rsBits B P.length _ (B * P.length) = _
    unfold rsBits; rw [if_neg (by omega), if_pos rfl, h1]; simp
  · show rsBits B P.length _ (B * P.length + 1) = _
    unfold rsBits; rw [if_neg (by omega), if_neg (by omega), if_pos rfl, h2]

/-! ## The step circuit as a fixed-scale threshold network -/

def stepNet (B N j : Nat) : List Layer := compileF (stepForms B N (polBin B N j (rIdx N)))

def netStep (B N j : Nat) (v : Nat → Bool) (rst : Bool) (ext : List Nat) : Nat → Bool := fun w =>
  if w < B * N + 2 then evalNet (stepNet B N j) (stepIn B N v rst ext) w else false

theorem netStep_eq (B N j : Nat) (v : Nat → Bool) (rst : Bool) (ext : List Nat) :
    netStep B N j v rst ext = bitStep B N (polBin B N j (rIdx N)) v rst ext := by
  funext w
  unfold netStep bitStep stepNet
  by_cases hw : w < B * N + 2
  · rw [if_pos hw, if_pos hw, compileF_eval _ _ (by rw [stepForms_length]; exact hw),
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [stepForms_length]; exact hw)]
    rfl
  · rw [if_neg hw, if_neg hw]

/-- The executor driven by the THRESHOLD NETWORK step. -/
def execRollN (B j : Nat) (v0 : Nat → Bool) (P : List Nat) : (Nat → Bool) × Nat :=
  loopUntil (fun v => netStep B P.length j v false []) (B * P.length + 1)
    (clockBound B P.length) (netStep B P.length j v0 true P)

theorem execRollN_eq (B j : Nat) (v0 : Nat → Bool) (P : List Nat) : execRollN B j v0 P = execRoll B j v0 P := by
  unfold execRollN execRoll
  rw [netStep_eq]
  exact loopUntil_congr (fun v => netStep_eq _ _ _ v false []) _ _ _

theorem execRollN_spec {B j : Nat} (v0 : Nat → Bool) {P : List Nat} (hw : Width B P) :
    (execRollN B j v0 P).1 (B * P.length) = rolloutWinner j P ∧
    (execRollN B j v0 P).1 (B * P.length + 1) = true ∧
    (execRollN B j v0 P).2 = rolloutMoves j P + 1 := by
  rw [execRollN_eq]; exact execRoll_spec v0 hw

/-! ## Composition: B executed rollouts, then the compiled readout -/

/-- The outcome bit of rollout j produced by the network executor (registers start from
    the all-zero vector; any start works by `execRollN_spec`). -/
def outBit (B j : Nat) (P : List Nat) : Bool := (execRollN B j (fun _ => false) P).1 (B * P.length)

/-- Policy-network evaluations used by rollout j (clocked steps of the executor). -/
def polEvals (B j : Nat) (P : List Nat) : Nat := (execRollN B j (fun _ => false) P).2

/-- THE FULLY EXECUTED MULTI-HEAD DECISION: finite-register rollouts, then the readout
    network on the board and the B executed outcome bits. -/
def mhExec (B : Nat) (P : List Nat) : Option (Nat × Nat) :=
  netBinSem (mhNet B P.length (rIdx P.length)) P.length (rIdx P.length) B
    (obsIn B P.length P (fun j => outBit B j P))

def mhExecSel (B : Nat) (P : List Nat) : Option (List Nat) := applyM P (mhExec B P)

theorem outBit_eq {B j : Nat} {P : List Nat} (hw : Width B P) : outBit B j P = rolloutWinner j P :=
  (execRollN_spec _ hw).1

theorem mhExec_eq {B : Nat} {P : List Nat} (hw : Width B P) : mhExec B P = decisionMove P := by
  have ho : (fun j => outBit B j P) = outcomes P := by funext j; exact outBit_eq hw
  unfold mhExec; rw [ho]
  exact mhNet_correct (rIdx_width _) rfl hw

theorem mhExec_eq_mhMove {B : Nat} {P : List Nat} (hw : Width B P) : mhExec B P = mhMove B P := by
  rw [mhExec_eq hw, mhMove_eq hw]

theorem mhExecSel_eq {B : Nat} {P : List Nat} (hw : Width B P) : mhExecSel B P = ctrlSel P := by
  unfold mhExecSel ctrlSel; rw [mhExec_eq hw]; cases decisionMove P <;> rfl

/-- WHOLE-GAME THEOREM FOR THE FULLY EXECUTED MULTI-HEAD PLAYER: from every nonzero board
    of width B it wins against every legal opponent; no outcome bit is supplied for free. -/
theorem mhExec_wins {B : Nat} {P : List Nat} (hw : Width B P) (h : nimSum P ≠ 0) : Wins (mhExecSel B) P :=
  wins_congr (fun Q hQ => mhExecSel_eq hQ) hw (ctrl_wins P h)

/-- EVALUATION ACCOUNTING for one multi-head decision: rollout j makes L_j + 1 policy
    evaluations; together Σ_j (L_j + 1) = (total simulated moves) + B ≤ B·(N(2^B−1)+1);
    in addition there are B reset steps (one per rollout) and ONE readout evaluation. -/
theorem mhExec_evals {B : Nat} {P : List Nat} (hw : Width B P) :
    (∀ j, polEvals B j P = rolloutMoves j P + 1) ∧
    ((List.range B).map (fun j => polEvals B j P)).sum = totalRolloutMoves B P + B ∧
    totalRolloutMoves B P + B ≤ B * clockBound B P.length := by
  have he : ∀ j, polEvals B j P = rolloutMoves j P + 1 := fun j => (execRollN_spec _ hw).2.2
  refine ⟨he, ?_, ?_⟩
  · unfold totalRolloutMoves
    rw [List.map_congr_left (fun j _ => he j)]
    induction B with
    | zero => simp
    | succ k ih =>
      rw [List.range_succ, List.map_append, List.map_append, List.sum_append_nat, List.sum_append_nat]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      have : ((List.range k).map (fun j => rolloutMoves j P + 1)).sum = ((List.range k).map (fun j => rolloutMoves j P)).sum + k := by
        clear ih he hw
        induction k with
        | zero => simp
        | succ k ih2 =>
          rw [List.range_succ, List.map_append, List.map_append, List.sum_append_nat, List.sum_append_nat, ih2]
          simp; omega
      omega
  · have := totalRolloutMoves_le hw
    unfold clockBound; rw [Nat.mul_add, Nat.mul_one]; omega

/-- COST CORRECTION for the phase-5 loop: `WholeGame.rollMoves` calls the policy network
    once more than it moves (the terminal test).  rollCalls counts its polStepN calls. -/
def rollCalls (B j : Nat) : Nat → List Nat → Nat
  | 0, _ => 0
  | f + 1, P => match polStepN B j P with
    | none => 1
    | some Q => rollCalls B j f Q + 1

theorem rollCalls_eq {B j : Nat} : ∀ (f : Nat) (P : List Nat), Width B P → P.sum ≤ f →
    rollCalls B j (f + 1) P = rolloutMoves j P + 1 ∧ rollCalls B j (f + 1) P = rollMoves B j (f + 1) P + 1
  | f, P, hw, hf => by
    simp only [rollCalls, rollMoves, polStepN_eq hw]
    cases h : policyStep j P with
    | none => simp [rolloutMoves_none h]
    | some Q =>
      simp only
      have hm := policyStep_move h
      have hlt := move_sum_lt hm
      cases f with
      | zero => omega
      | succ f =>
        obtain ⟨h1, h2⟩ := rollCalls_eq (B := B) (j := j) f Q (width_move hw hm) (by omega)
        rw [rolloutMoves_some h]; omega

/-- The phase-5 multi-head player `mhSelect` performs Σ_j (L_j + 1) policy-network calls
    and one readout call: the simulated-move count of mhSelect_cost plus B + 1. -/
theorem mhSelect_calls {B : Nat} {P : List Nat} (hw : Width B P) :
    ((List.range B).map (fun j => rollCalls B j (P.sum + 1) P)).sum + 1 = totalRolloutMoves B P + B + 1 := by
  have e := fun j => (rollCalls_eq (B := B) (j := j) P.sum P hw (Nat.le_refl _)).1
  rw [List.map_congr_left (fun j _ => e j)]
  have h := (mhExec_evals (B := B) hw).2.1
  have he := (mhExec_evals (B := B) hw).1
  rw [List.map_congr_left (fun j _ => he j)] at h
  omega

/-- SEQUENTIAL TIME IS NOT CONSTANT: for every T there is a board (B = 1, all heaps 1)
    on which rollout 0 needs more than T clocked steps. -/
theorem unbounded_steps (T : Nat) : ∃ P : List Nat, Width 1 P ∧ T < polEvals 1 0 P := by
  refine ⟨List.replicate T 1, fun x hx => by rw [List.eq_of_mem_replicate hx]; decide, ?_⟩
  unfold polEvals
  rw [(execRollN_spec (B := 1) (j := 0) _ (fun x hx => by rw [List.eq_of_mem_replicate hx]; decide)).2.2,
    rolloutMoves_eq]
  have : rolloutCount 0 (List.replicate T 1) = T := by
    unfold rolloutCount heapCount
    induction T with
    | zero => rfl
    | succ T ih => simp [List.replicate_succ] at ih ⊢; omega
  omega


/-! ## Resources of the step circuit -/

theorem depth_mux_le (c a b : Circ) : depth (mux c a b) ≤ max (depth c + 1) (max (depth a) (depth b)) + 2 := by
  simp only [mux, depth_or, depth_and, depth_not, List.map_cons, List.map_nil, listMax, List.foldr]; omega

theorem size_mux (c a b : Circ) : size (mux c a b) = 2 * size c + size a + size b + 4 := by
  simp only [mux, size_or, size_and, size_not, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; omega

theorem maxInput_mux (c a b : Circ) : maxInput (mux c a b) ≤ max (maxInput c) (max (maxInput a) (maxInput b)) := by
  simp only [mux, maxInput_or, maxInput_and, maxInput_not, List.map_cons, List.map_nil, listMax, List.foldr]; omega

theorem xor2_res (a b : Circ) : depth (xor2 a b) ≤ max (depth a) (depth b) + 3 ∧
    size (xor2 a b) = 2 * size a + 2 * size b + 5 ∧ maxInput (xor2 a b) ≤ max (maxInput a) (maxInput b) := by
  simp only [xor2, depth_or, depth_and, depth_not, size_or, size_and, size_not, maxInput_or, maxInput_and,
    maxInput_not, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, listMax, List.foldr]
  refine ⟨by omega, by omega, by omega⟩

/-- Per-formula size bound of the step circuit (r index bits, N heaps, selector size Sz). -/
def stepZ (r N Sz : Nat) : Nat :=
  2 * ((Sz + N * (r * (Sz + 1) + 1) + 2 + 3) + (r * (Sz + 1) + 1) + 1) + Sz + 13 +
    2 * (Sz + N * (r * (Sz + 1) + 1) + 2 + 3) + 10

/-- STEP-CIRCUIT RESOURCES: from a selector with BinBound (depth ≤ D, size ≤ Sz, reading
    the board), every step formula has depth ≤ D + 11, size ≤ stepZ and reads only the
    2·B·N + 3 step inputs. -/
theorem stepForms_res {S : BCirc} {N B r D Sz : Nat} (hb : BinBound S N B r D Sz (B * N)) :
    ∀ c ∈ stepForms B N S, depth c ≤ D + 11 ∧ size c ≤ stepZ r N Sz ∧ maxInput c ≤ 2 * (B * N) + 3 := by
  have hbb := bbound_of_bin hb
  have hdec := fun i => decodeC_resources hbb i
  have hval : ∀ p, depth (getC S.val p) ≤ D ∧ size (getC S.val p) ≤ Sz + 1 ∧ maxInput (getC S.val p) ≤ B * N := by
    intro p; unfold getC; rw [List.getD_eq_getElem?_getD]
    cases h : S.val[p]? with
    | none => simp
    | some c =>
      have hm := List.mem_of_getElem? h
      exact ⟨hbb.depth_val c hm, Nat.le_succ_of_le (hbb.size_val c hm), hbb.max_val c hm⟩
  have hmv : depth (mvC S N) ≤ D + 4 ∧ size (mvC S N) ≤ Sz + N * (r * (Sz + 1) + 1) + 2 ∧
      maxInput (mvC S N) ≤ B * N := by
    have hor : depth (or ((List.range N).map (decodeC S.idx))) ≤ D + 3 ∧
        size (or ((List.range N).map (decodeC S.idx))) ≤ N * (r * (Sz + 1) + 1) + 1 ∧
        maxInput (or ((List.range N).map (decodeC S.idx))) ≤ B * N := by
      refine ⟨depth_or_le (fun c hc => ?_), ?_, ControllerBits.maxInput_or_le (fun c hc => ?_)⟩
      · obtain ⟨i, _, rfl⟩ := List.mem_map.mp hc; exact (hdec i).1
      · rw [size_or]
        have := sum_le_len_mul (cs := (List.range N).map (decodeC S.idx)) (S := r * (Sz + 1) + 1)
          (fun c hc => by obtain ⟨i, _, rfl⟩ := List.mem_map.mp hc; exact (hdec i).2.1)
        simp only [List.length_map, List.length_range] at this; omega
      · obtain ⟨i, _, rfl⟩ := List.mem_map.mp hc; exact (hdec i).2.2
    unfold mvC
    simp only [depth_and, size_and, maxInput_and, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      listMax, List.foldr]
    have := hbb.depth_valid; have := hbb.size_valid; have := hbb.max_valid
    refine ⟨by omega, by omega, by omega⟩
  have hact : depth (actC B N S) ≤ D + 5 ∧ size (actC B N S) ≤ Sz + N * (r * (Sz + 1) + 1) + 2 + 3 ∧
      maxInput (actC B N S) ≤ B * N + 2 := by
    unfold actC
    simp only [depth_and, size_and, maxInput_and, depth_not, size_not, maxInput_not, depth_input, size_input,
      maxInput_input, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, listMax, List.foldr]
    refine ⟨by omega, by omega, by omega⟩
  intro c hc
  simp only [stepForms, List.mem_append, List.mem_map, List.mem_range, List.mem_cons, List.mem_nil_iff,
    or_false] at hc
  rcases hc with ⟨w, hw, rfl⟩ | rfl | rfl
  · -- board formula
    obtain ⟨d1, s1, m1⟩ := hdec (w / B)
    obtain ⟨d2, s2, m2⟩ := hval (w % B)
    have hc1 : depth (and [actC B N S, decodeC S.idx (w / B)]) ≤ D + 6 ∧
        size (and [actC B N S, decodeC S.idx (w / B)]) ≤ (Sz + N * (r * (Sz + 1) + 1) + 2 + 3) + (r * (Sz + 1) + 1) + 1 ∧
        maxInput (and [actC B N S, decodeC S.idx (w / B)]) ≤ B * N + 2 := by
      simp only [depth_and, size_and, maxInput_and, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        listMax, List.foldr]
      refine ⟨by omega, by omega, by omega⟩
    have hin := depth_mux_le (and [actC B N S, decodeC S.idx (w / B)]) (getC S.val (w % B)) (input w)
    have hins := size_mux (and [actC B N S, decodeC S.idx (w / B)]) (getC S.val (w % B)) (input w)
    have hinm := maxInput_mux (and [actC B N S, decodeC S.idx (w / B)]) (getC S.val (w % B)) (input w)
    unfold boardC rstC
    have ho := depth_mux_le (input (B * N + 2)) (input (B * N + 3 + w))
      (mux (and [actC B N S, decodeC S.idx (w / B)]) (getC S.val (w % B)) (input w))
    have hos := size_mux (input (B * N + 2)) (input (B * N + 3 + w))
      (mux (and [actC B N S, decodeC S.idx (w / B)]) (getC S.val (w % B)) (input w))
    have hom := maxInput_mux (input (B * N + 2)) (input (B * N + 3 + w))
      (mux (and [actC B N S, decodeC S.idx (w / B)]) (getC S.val (w % B)) (input w))
    simp only [depth_input, size_input, maxInput_input] at ho hos hom hin hins hinm
    unfold stepZ
    refine ⟨by omega, by omega, by omega⟩
  · -- par
    obtain ⟨x1, x2, x3⟩ := xor2_res (actC B N S) (input (B * N))
    unfold parC rstC
    simp only [depth_and, size_and, maxInput_and, depth_not, size_not, maxInput_not, depth_input, size_input,
      maxInput_input, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, listMax, List.foldr] at x1 x2 x3 ⊢
    unfold stepZ
    refine ⟨by omega, by omega, by omega⟩
  · -- halt
    unfold haltC rstC
    simp only [depth_and, size_and, maxInput_and, depth_not, size_not, maxInput_not, depth_input, size_input,
      maxInput_input, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, listMax, List.foldr]
    unfold stepZ
    refine ⟨by omega, by omega, by omega⟩

/-- Step-circuit members: index (B, (N, j)), input = registers + reset + external board. -/
def stepLen : Nat × (Nat × Nat) → Nat := fun i => 2 * (i.1 * i.2.1) + 3
def stepF (i : Nat × (Nat × Nat)) : List Circ := stepForms i.1 i.2.1 (polS i)

def stepZE {ι : Type} : PE ι :=
  2 * ((polSzE + vN * (vr * (polSzE + 1) + 1) + 2 + 3) + (vr * (polSzE + 1) + 1) + 1) + polSzE + 13 +
    2 * (polSzE + vN * (vr * (polSzE + 1) + 1) + 2 + 3) + 10

theorem stepLen_pos (i : Nat × (Nat × Nat)) (_hi : polAdm i) : 1 ≤ stepLen i := by unfold stepLen; omega
theorem step_leaves (k : Nat) (i : Nat × (Nat × Nat)) (hi : polAdm i) : leafBNj k i ≤ stepLen i := by
  have h := pol_leaves k i hi; unfold polLen at h; unfold stepLen; omega

theorem stepF_tsize (i : Nat × (Nat × Nat)) :
    tsize (stepF i) ≤ (i.1 * i.2.1 + 2) * stepZ (rIdx i.2.1) i.2.1 (polSz i.1 i.2.1) := by
  have h := sum_le_len_mul (cs := stepF i) (S := stepZ (rIdx i.2.1) i.2.1 (polSz i.1 i.2.1))
    (fun c hc => (stepForms_res (pol_bound i) c hc).2.1)
  unfold stepF at h ⊢; rw [stepForms_length] at h; exact h

/-- STEP-CIRCUIT FAMILY CERTIFICATE: depth ≤ 28, input width 2·B·N + 3, total size
    polynomial in that width (one clock step of one rollout). -/
theorem step_ac0 : AC0Fam polAdm stepLen stepF 28 := by
  refine ⟨stepLen_pos, fun i _ c hc => (stepForms_res (pol_bound i) c hc).1,
    fun i _ c hc => (stepForms_res (pol_bound i) c hc).2.2, ?_⟩
  exact polyIn_mono (fun i _ => stepF_tsize i)
    (polyE stepLen_pos leafBNj step_leaves ((vB * vN + 2) * stepZE) _ (fun _ => rfl))

def stepN (i : Nat × (Nat × Nat)) : List Layer := stepNet i.1 i.2.1 i.2.2

/-- STEP-NETWORK FAMILY CERTIFICATE (W = 1, ≤ 58 layers). -/
theorem step_net : NetFam polAdm stepLen stepN 1 58 := by
  have spec := fun i => compileF_spec (stepF i) (stepLen i) 28 (fun c hc => (stepForms_res (pol_bound i) c hc).2.2)
    (fun c hc => (stepForms_res (pol_bound i) c hc).1)
  have hT := polyE stepLen_pos leafBNj step_leaves ((vB * vN + 2) * stepZE)
    (fun i => (i.1 * i.2.1 + 2) * stepZ (rIdx i.2.1) i.2.1 (polSz i.1 i.2.1)) (fun _ => rfl)
  refine ⟨stepLen_pos, fun i _ => (spec i).2.2.1, fun i _ => (spec i).2.2.2.1, fun i _ => (spec i).2.2.2.2.1, ?_, ?_⟩
  · obtain ⟨c, k, h⟩ := polyIn_add stepLen_pos hT (polyIn_leaf (fun i _ => Nat.le_refl (stepLen i)))
    refine ⟨c, k, fun i hi => netBounded_mono (spec i).2.2.2.2.2.1 ?_⟩
    have := stepF_tsize i; have := h i hi; dsimp only at *; unfold tsize at *; omega
  · have h2 := polyIn_add stepLen_pos (polyIn_mul (polyIn_const _ _ (2 * 28 + 1)) hT)
      (polyE stepLen_pos leafBNj step_leaves (vB * vN + 2) (fun i => i.1 * i.2.1 + 2) (fun _ => rfl))
    refine polyIn_mono (fun i _ => ?_) h2
    have g := (spec i).2.2.2.2.2.2
    have := Nat.mul_le_mul_left (2 * 28 + 1) (stepF_tsize i)
    have hl : (stepF i).length = i.1 * i.2.1 + 2 := by unfold stepF; rw [stepForms_length]
    unfold tsize at this; rw [hl] at g
    show gateCount (stepNet i.1 i.2.1 i.2.2) ≤ _
    exact Nat.le_trans g (by omega)

/-! ## Bit work of one fully executed multi-head decision -/

def stepSize (B N j : Nat) : Nat := tsize (stepForms B N (polBin B N j (rIdx N)))

/-- Formula nodes evaluated: each rollout evaluates the step formulas once per clocked
    step and once for its reset; the readout formulas are evaluated once. -/
def mhWork (B : Nat) (P : List Nat) : Nat :=
  ((List.range B).map (fun j => (polEvals B j P + 1) * stepSize B P.length j)).sum +
    tsize (bForms (mhS (B, P.length)))

theorem mhWork_le {B : Nat} {P : List Nat} (hw : Width B P) :
    mhWork B P ≤ B * ((P.length * 2 ^ B + 2) * ((B * P.length + 2) * stepZ (rIdx P.length) P.length (polSz B P.length))) +
      (1 + rIdx P.length + B) * mhSz B P.length := by
  unfold mhWork
  have h1 : ∀ j ∈ List.range B, (polEvals B j P + 1) * stepSize B P.length j ≤
      (P.length * 2 ^ B + 2) * ((B * P.length + 2) * stepZ (rIdx P.length) P.length (polSz B P.length)) := by
    intro j _
    have he := (execRollN_spec (j := j) (fun _ => false) hw).2.2
    have hc := clock_ok (j := j) hw
    have hs := stepF_tsize (B, P.length, j)
    unfold stepF at hs
    have hpe : polEvals B j P + 1 ≤ P.length * 2 ^ B + 2 := by
      unfold polEvals; rw [he]; unfold clockBound at hc
      have : P.length * (2 ^ B - 1) ≤ P.length * 2 ^ B := Nat.mul_le_mul_left P.length (Nat.sub_le (2 ^ B) 1)
      omega
    exact Nat.mul_le_mul hpe hs
  have h2 := sum_map_le_mem (l := List.range B) (f := fun j => (polEvals B j P + 1) * stepSize B P.length j)
    (g := fun _ => (P.length * 2 ^ B + 2) * ((B * P.length + 2) * stepZ (rIdx P.length) P.length (polSz B P.length))) h1
  rw [List.map_const', List.sum_replicate_nat, List.length_range] at h2
  have h3 := PriorityEncoder.totalSize_le (mh_bound (B, P.length))
  rw [← tsize_bForms] at h3
  exact Nat.add_le_add h2 h3

theorem polyIn_comp {ι : Type} {adm : ι → Prop} {len1 len2 : ι → Nat} {f : ι → Nat}
    (h : PolyIn adm len1 f) {c' k' : Nat} (hl : ∀ i, adm i → len1 i ≤ c' * len2 i ^ k') : PolyIn adm len2 f := by
  obtain ⟨c, k, hf⟩ := h
  refine ⟨c * c' ^ k, k' * k, fun i hi => ?_⟩
  calc f i ≤ c * len1 i ^ k := hf i hi
    _ ≤ c * (c' * len2 i ^ k') ^ k := Nat.mul_le_mul_left c (Nat.pow_le_pow_left (hl i hi) k)
    _ = c * c' ^ k * len2 i ^ (k' * k) := by rw [Nat.mul_pow, ← Nat.pow_mul, Nat.mul_assoc]

/-- Leaves for the work bound: 0 ↦ B, 1 ↦ N, 2 ↦ r, otherwise ↦ 2^B. -/
def leafW : Nat → Nat × Nat → Nat
  | 0, i => i.1
  | 1, i => i.2
  | 2, i => rIdx i.2
  | _, i => 2 ^ i.1

def workLen : Nat × Nat → Nat := fun i => i.1 * i.2 + 2 ^ i.1

theorem work_leaves (k : Nat) (i : Nat × Nat) (hi : restAdm i) : leafW k i ≤ workLen i := by
  have hB := Nat.mul_le_mul_left i.1 hi.2
  have hN := Nat.mul_le_mul_right i.2 hi.1
  have hr := rIdx_le hi.2
  have h2 := Nat.two_pow_pos i.1
  match k with
  | 0 => show i.1 ≤ workLen i; unfold workLen; simp at hB; omega
  | 1 => show i.2 ≤ workLen i; unfold workLen; simp at hN; omega
  | 2 => show rIdx i.2 ≤ workLen i; unfold workLen; simp at hN; omega
  | _ + 3 => show 2 ^ i.1 ≤ workLen i; unfold workLen; omega

/-- BIT WORK IS POLYNOMIAL IN B·N + 2^B (exponential in B in general). -/
theorem mhWork_poly : ∃ c k, ∀ B : Nat, ∀ P : List Nat, 1 ≤ B → 1 ≤ P.length → Width B P →
    mhWork B P ≤ c * (B * P.length + 2 ^ B) ^ k := by
  have hp : ∀ i, restAdm i → 1 ≤ workLen i := fun i hi => by
    show 1 ≤ i.1 * i.2 + 2 ^ i.1; have := Nat.two_pow_pos i.1; omega
  obtain ⟨c, k, h⟩ := polyE hp leafW work_leaves
    (vB * ((vN * PE.v 3 + 2) * ((vB * vN + 2) * stepZE)) + (1 + vr + vB) * mhSzE)
    (fun i => i.1 * ((i.2 * 2 ^ i.1 + 2) * ((i.1 * i.2 + 2) * stepZ (rIdx i.2) i.2 (polSz i.1 i.2))) +
      (1 + rIdx i.2 + i.1) * mhSz i.1 i.2) (fun _ => rfl)
  exact ⟨c, k, fun B P hB hN hw => Nat.le_trans (mhWork_le hw) (h (B, P.length) ⟨hB, hN⟩)⟩

/-- For B = O(log N), i.e. 2^B ≤ (N+1)^a with a fixed, the bit work of one fully
    executed multi-head decision is polynomial in N. -/
theorem mhWork_poly_logB (a : Nat) : ∃ c k, ∀ B : Nat, ∀ P : List Nat, 1 ≤ B → 1 ≤ P.length → Width B P →
    2 ^ B ≤ (P.length + 1) ^ a → mhWork B P ≤ c * P.length ^ k := by
  have hp : ∀ i, (restAdm i ∧ 2 ^ i.1 ≤ (i.2 + 1) ^ a) → 1 ≤ workLen i :=
    fun i hi => by show 1 ≤ i.1 * i.2 + 2 ^ i.1; have := Nat.two_pow_pos i.1; omega
  have hW := polyE hp leafW (fun k i hi => work_leaves k i hi.1)
    (vB * ((vN * PE.v 3 + 2) * ((vB * vN + 2) * stepZE)) + (1 + vr + vB) * mhSzE)
    (fun i => i.1 * ((i.2 * 2 ^ i.1 + 2) * ((i.1 * i.2 + 2) * stepZ (rIdx i.2) i.2 (polSz i.1 i.2))) +
      (1 + rIdx i.2 + i.1) * mhSz i.1 i.2) (fun _ => rfl)
  have hl : ∀ i, (restAdm i ∧ 2 ^ i.1 ≤ (i.2 + 1) ^ a) → workLen i ≤ (2 * 2 ^ a + 1) * i.2 ^ (a + 1) := by
    intro i ⟨⟨hB, hN⟩, h2⟩
    have hBlt : i.1 < 2 ^ i.1 := Nat.lt_two_pow_self
    have e1 : (i.2 + 1) ^ a ≤ 2 ^ a * i.2 ^ a := by
      rw [← Nat.mul_pow]; exact Nat.pow_le_pow_left (by omega) a
    have e2 : i.2 ^ a ≤ i.2 ^ (a + 1) := Nat.pow_le_pow_right (by omega) (by omega)
    have e3 : i.1 * i.2 ≤ 2 ^ a * i.2 ^ a * i.2 := Nat.mul_le_mul_right _ (by omega)
    have e4 : 2 ^ a * i.2 ^ a * i.2 = 2 ^ a * i.2 ^ (a + 1) := by rw [Nat.mul_assoc, ← Nat.pow_succ]
    have e5 : 2 ^ a * i.2 ^ a ≤ 2 ^ a * i.2 ^ (a + 1) := Nat.mul_le_mul_left _ e2
    have e6 : (2 * 2 ^ a + 1) * i.2 ^ (a + 1) = 2 * (2 ^ a * i.2 ^ (a + 1)) + i.2 ^ (a + 1) := by
      rw [Nat.add_mul, Nat.one_mul, Nat.mul_assoc]
    unfold workLen; omega
  obtain ⟨c, k, h⟩ := polyIn_comp hW hl
  exact ⟨c, k, fun B P hB hN hw h2 => Nat.le_trans (mhWork_le hw) (h (B, P.length) ⟨⟨hB, hN⟩, h2⟩)⟩

/-! ## Axiom audit -/

#print axioms untilHalt_halted
#print axioms rolloutWinner_none'
#print axioms rolloutWinner_some'
#print axioms untilHalt_spec
#print axioms clock_ok
#print axioms eval_mux
#print axioms stepForms_length
#print axioms polSpec_polBin
#print axioms stepForms_board
#print axioms stepForms_par
#print axioms stepForms_halt
#print axioms any_decode
#print axioms eval_mvC
#print axioms maxInput_decodeC
#print axioms maxInput_getC_le
#print axioms getD_set_nat
#print axioms boardBits_set
#print axioms bitStep_run
#print axioms bitStep_reset
#print axioms loopUntil_congr
#print axioms rsStep_inv
#print axioms loop_refines
#print axioms execRoll_spec
#print axioms netStep_eq
#print axioms execRollN_eq
#print axioms execRollN_spec
#print axioms outBit_eq
#print axioms mhExec_eq
#print axioms mhExec_eq_mhMove
#print axioms mhExecSel_eq
#print axioms mhExec_wins
#print axioms mhExec_evals
#print axioms rollCalls_eq
#print axioms mhSelect_calls
#print axioms unbounded_steps
#print axioms depth_mux_le
#print axioms size_mux
#print axioms maxInput_mux
#print axioms xor2_res
#print axioms stepForms_res
#print axioms stepLen_pos
#print axioms step_leaves
#print axioms stepF_tsize
#print axioms step_ac0
#print axioms step_net
#print axioms mhWork_le
#print axioms polyIn_comp
#print axioms work_leaves
#print axioms mhWork_poly
#print axioms mhWork_poly_logB


