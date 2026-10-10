import ControllerBits

/- Phase 4, Priority 4: constructive selection circuits.  Written by Claude
   (10 October 2026).  Lean 4.26.0, core/Std only.

   * A GENERIC first-index move selector `genSel` (primary test with its new value,
     fallback "subtract 1 from the first nonzero heap"), with one exactness theorem
     `genSel_correct` reused by every instance below.
   * VARIABLE-TARGET selector `varSel`: the target σ arrives on B input wires (it is
     not a constant baked into the circuit, unlike phase-3 `attRC`); it computes
     `attainT σ P` = `replayMove σ P` (cancel σ at the first qualifying heap, else
     the fallback, else halt).
   * MULTI-HEAD selector `mhSel`: σ is reconstructed inside the circuit from the B
     rollout-outcome wires (σ₀ = o₀, σⱼ = oⱼ ⊕ o₀); on the true outcomes it outputs
     `decisionMove P`, the same verified move as the recurrent controller.
   * POLICY-STEP circuits `polSel j` for π_j (threshold eligibility 2^j ≤ x, first
     eligible heap, subtraction of 2^j, fallback subtract-1): exact for `policyStep`.
   Input layout: board bits as in `CorrBridge.boardBits` (heap i, big-endian position
   p at wire B·i + p) on wires below B·N; extra wires (σ or outcomes) from B·N on. -/

namespace NimAudit
namespace SelectCircuit

open Game Rollout Prob Attain Recurrent AC0 AC0.Circ CorrBridge AttainCircuit Bridge

/-- Evaluation of a move readout on an arbitrary input vector. -/
def selReadout (R : RCirc) (z : Nat → Bool) : Option (Nat × Nat) :=
  if eval z R.valid then
    match firstTrue (R.sel.map (eval z)) with
    | some i => some (i, toNatBE (R.val.map (eval z)))
    | none => none
  else none

theorem readoutOf_eq (B : Nat) (R : Bool → RCirc) (P : List Nat) (b : Bool) :
    readoutOf B R P b = selReadout (R b) (boardBits B P) := rfl

/-- Substitution into all formulas of a readout. -/
def substR (τ : Nat → Circ) (R : RCirc) : RCirc := ⟨subst τ R.valid, R.sel.map (subst τ), R.val.map (subst τ)⟩

theorem selReadout_subst (τ : Nat → Circ) (R : RCirc) (z : Nat → Bool) :
    selReadout (substR τ R) z = selReadout R (fun w => eval z (τ w)) := by
  have h : (eval z ∘ subst τ) = eval (fun w => eval z (τ w)) := funext (fun c => eval_subst τ z c)
  simp only [selReadout, substR, List.map_map, h, eval_subst]

def orFirst (N : Nat) (cs bs : Nat → Circ) : Circ :=
  or ((List.range N).map (fun i => and [firstC cs i, bs i]))

theorem orFirst_eval {N : Nat} (z : Nat → Bool) (cs bs : Nat → Circ) :
    eval z (orFirst N cs bs) =
      match firstTrue ((List.range N).map (fun i => eval z (cs i))) with
      | some i => eval z (bs i)
      | none => false := by
  apply Bool.eq_iff_iff.mpr
  simp only [orFirst, eval_or, List.any_map, List.any_eq_true, List.mem_range, Function.comp_apply,
    eval_and, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
  constructor
  · rintro ⟨i, hi, hf, hb⟩
    rw [firstC_eval (N := N) z cs hi, decide_eq_true_iff] at hf
    rw [hf]; exact hb
  · intro h
    cases hft : firstTrue ((List.range N).map (fun i => eval z (cs i))) with
    | none => rw [hft] at h; cases h
    | some i =>
      rw [hft] at h
      have hi : i < N := by have := firstTrue_lt hft; simpa using this
      exact ⟨i, hi, by rw [firstC_eval (N := N) z cs hi, decide_eq_true_iff]; exact hft, h⟩

theorem firstTrue_isSome (l : List Bool) : (firstTrue l).isSome = l.any id := by
  induction l with
  | nil => rfl
  | cons b l ih => cases b <;> simp [firstTrue, ih]

/-! ## The generic selector -/

/-- First heap passing a primary test, with its new value. -/
def firstIdx (pr : Nat → Bool) (f : Nat → Nat) (P : List Nat) : Option (Nat × Nat) :=
  (firstTrue (P.map pr)).map (fun i => (i, f (P.getD i 0)))

/-- Primary choice, else fallback (first nonzero heap minus one), else halt. -/
def primOr (pr : Nat → Bool) (f : Nat → Nat) (P : List Nat) : Option (Nat × Nat) :=
  match firstIdx pr f P with
  | some m => some m
  | none => decIdx P

def anyC' (N : Nat) (prim : Nat → Circ) : Circ := or ((List.range N).map prim)

def genSel (B N : Nat) (prim : Nat → Circ) (pv : Nat → Nat → Circ) : RCirc :=
  ⟨validA B N,
   (List.range N).map (fun i => or [prim i, and [not (anyC' N prim), AttainCircuit.nzC B i]]),
   (List.range B).map (fun p => or [and [anyC' N prim, orFirst N prim (fun i => pv i p)],
     and [not (anyC' N prim), orFirst N (AttainCircuit.nzC B) (fun i => decbitC B i p)]])⟩

section GenSel
variable {B N : Nat} {P : List Nat}

theorem max_nzC {i : Nat} (hi : i < N) : maxInput (AttainCircuit.nzC B i) ≤ B * N := by
  unfold AttainCircuit.nzC
  apply ControllerBits.maxInput_or_le; intro c hc
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hc
  have := List.mem_range.mp hp
  have : B * i + B ≤ B * N := by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hi
  simp; omega

theorem max_decbitC {i p : Nat} (hi : i < N) (hp : p < B) : maxInput (decbitC B i p) ≤ B * N := by
  have hb : B * i + B ≤ B * N := by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hi
  have h1 : maxInput (lowZeroC B i p) ≤ B * N := by
    unfold lowZeroC
    apply ControllerBits.maxInput_and_le; intro c hc
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hc
    have := List.mem_range.mp hr
    simp; omega
  unfold decbitC xor2
  generalize lowZeroC B i p = L at h1
  simp only [maxInput_or, maxInput_and, maxInput_not, maxInput_input, List.map_cons, List.map_nil,
    listMax, List.foldr_cons, List.foldr_nil]
  omega

theorem decbit_eval (hP : P.length = N) {i p : Nat} (hi : i < N) (hp : p < B) (hpos : 0 < P.getD i 0) :
    eval (boardBits B P) (decbitC B i p) = (P.getD i 0 - 1).testBit (B - 1 - p) := by
  rw [testBit_pred _ hpos]
  unfold decbitC
  rw [eval_xor2, eval_input, boardBits_heap hP hi hp]
  congr 1
  unfold lowZeroC
  apply Bool.eq_iff_iff.mpr
  simp only [eval_and, List.all_map, List.all_eq_true, List.mem_range, Function.comp_apply,
    eval_not, eval_input, Bool.not_eq_true', decide_eq_true_iff]
  constructor
  · intro h j hj
    have := h (B - 1 - p - 1 - j) (by omega)
    rw [boardBits_heap hP hi (by omega)] at this
    rwa [show B - 1 - (p + 1 + (B - 1 - p - 1 - j)) = j by omega] at this
  · intro h r hr
    rw [boardBits_heap hP hi (by omega)]
    exact h _ (by omega)

theorem getD_lt_of_width (hP : P.length = N) (hw : Width B P) {i : Nat} (hi : i < N) :
    P.getD i 0 < 2 ^ B := by
  apply hw; simp only [List.getD_eq_getElem?_getD]; rw [List.getElem?_eq_getElem (by omega)]; simp

theorem map_getD_eq (hP : P.length = N) {f : Nat → Bool} {g : Nat → Bool}
    (h : ∀ i < N, g i = f (P.getD i 0)) : (List.range N).map g = P.map f := by
  rw [← range_map_getD f P, hP]
  apply List.map_congr_left; intro i hi; exact h i (List.mem_range.mp hi)

theorem firstTrue_map_getD {l : List Bool} {i : Nat} (pr : Nat → Bool) (hl : l = P.map pr)
    (h : firstTrue l = some i) : i < P.length ∧ pr (P.getD i 0) = true := by
  obtain ⟨hlen, hb, _⟩ := (firstTrue_some_iff _ i).1 h
  subst hl
  rw [List.length_map] at hlen
  refine ⟨hlen, ?_⟩
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hlen] at hb ⊢
  simpa using hb

/-- GENERIC SELECTOR EXACTNESS. -/
theorem genSel_correct (hP : P.length = N) (hw : Width B P) (z : Nat → Bool)
    (hz : ∀ j < B * N, z j = boardBits B P j) (prim : Nat → Circ) (pv : Nat → Nat → Circ)
    (pr : Nat → Bool) (f : Nat → Nat)
    (hpr : ∀ i < N, eval z (prim i) = pr (P.getD i 0))
    (hpos : ∀ x, pr x = true → 0 < x)
    (hf : ∀ x, pr x = true → x < 2 ^ B → f x < 2 ^ B)
    (hpv : ∀ i < N, ∀ p < B, pr (P.getD i 0) = true →
      eval z (pv i p) = (f (P.getD i 0)).testBit (B - 1 - p)) :
    selReadout (genSel B N prim pv) z = primOr pr f P := by
  have hnzz : ∀ i < N, eval z (AttainCircuit.nzC B i) = decide (0 < P.getD i 0) := by
    intro i hi
    rw [eval_congr_below z (boardBits B P) _ (fun j hj => hz j (Nat.lt_of_lt_of_le hj (max_nzC hi))),
      nz_eval hP hw hi]
  have hdbz : ∀ i < N, ∀ p < B, 0 < P.getD i 0 →
      eval z (decbitC B i p) = (P.getD i 0 - 1).testBit (B - 1 - p) := by
    intro i hi p hp hpos'
    rw [eval_congr_below z (boardBits B P) _
      (fun j hj => hz j (Nat.lt_of_lt_of_le hj (max_decbitC hi hp))), decbit_eval hP hi hp hpos']
  have hcan : (List.range N).map (fun i => eval z (prim i)) = P.map pr := map_getD_eq hP hpr
  have hnz : (List.range N).map (fun i => eval z (AttainCircuit.nzC B i)) = P.map (fun x => decide (0 < x)) :=
    map_getD_eq hP hnzz
  have hany : eval z (anyC' N prim) = (P.map pr).any id := by
    unfold anyC'; rw [eval_or, ← hcan, List.any_map, List.any_map]; rfl
  have hsel : (genSel B N prim pv).sel.map (eval z) =
      (List.range N).map (fun i => eval z (prim i) ||
        (!((List.range N).any (fun i => eval z (prim i))) && eval z (AttainCircuit.nzC B i))) := by
    unfold genSel
    rw [List.map_map]
    apply List.map_congr_left; intro i _
    simp only [Function.comp_apply, eval_or, eval_and, eval_not, List.any_cons, List.any_nil,
      List.all_cons, List.all_nil, Bool.or_false, Bool.and_true, anyC', List.any_map]
    rfl
  have hvalid : eval z (genSel B N prim pv).valid = (P.map (fun x => decide (0 < x))).any id := by
    unfold genSel validA; rw [eval_or, ← hnz, List.any_map, List.any_map]; rfl
  have hanyR : (List.range N).any (fun i => eval z (prim i)) = (P.map pr).any id := by
    rw [← hcan, List.any_map]; rfl
  unfold selReadout primOr firstIdx
  rw [hsel, firstTrue_or, hvalid, hanyR, hcan, hnz, decIdx_firstTrue]
  by_cases hA : (P.map pr).any id = true
  · rw [← firstTrue_isSome] at hA
    obtain ⟨i, hi⟩ := Option.isSome_iff_exists.mp hA
    obtain ⟨hiN, hpri⟩ := firstTrue_map_getD pr rfl hi
    rw [hP] at hiN
    have hvalidT : (P.map (fun x => decide (0 < x))).any id = true := by
      rw [List.any_map]; apply List.any_eq_true.mpr
      exact ⟨P.getD i 0, by
        simp only [List.getD_eq_getElem?_getD]; rw [List.getElem?_eq_getElem (by omega)]; simp,
        by simpa using hpos _ hpri⟩
    rw [firstTrue_isSome] at hA
    simp only [hvalidT, if_true, hA, hi, Option.map_some]
    congr 2
    have hxlt := getD_lt_of_width hP hw hiN
    simp only [genSel, List.map_map]
    apply toNatBE_of_bits (hf _ hpri hxlt)
    intro p hp
    simp only [Function.comp_apply, eval_or, eval_and, eval_not, List.any_cons, List.any_nil, List.all_cons,
      List.all_nil, Bool.and_true, Bool.or_false, hany, hA, Bool.not_true, Bool.false_and,
      Bool.true_and]
    rw [orFirst_eval, hcan, hi]
    exact hpv i hiN p hp hpri
  · have hnone : firstTrue (P.map pr) = none := by
      cases h : firstTrue (P.map pr) with
      | none => rfl
      | some i =>
        exfalso; apply hA; rw [← firstTrue_isSome, h]; rfl
    have hA' : (P.map pr).any id = false := by simpa using hA
    simp only [hA', Bool.false_eq_true, if_false, hnone, Option.map_none]
    by_cases hV : (P.map (fun x => decide (0 < x))).any id = true
    · simp only [hV, if_true]
      rw [← firstTrue_isSome] at hV
      obtain ⟨i, hi⟩ := Option.isSome_iff_exists.mp hV
      obtain ⟨hiN, hposi⟩ := firstTrue_map_getD (fun x => decide (0 < x)) rfl hi
      rw [hP] at hiN
      simp only [hi, Option.map_some]
      congr 2
      have hxlt := getD_lt_of_width hP hw hiN
      have hpos' : 0 < P.getD i 0 := by simpa using hposi
      simp only [genSel, List.map_map]
      apply toNatBE_of_bits (Nat.lt_of_le_of_lt (Nat.sub_le _ _) hxlt)
      intro p hp
      simp only [Function.comp_apply, eval_or, eval_and, eval_not, List.any_cons, List.any_nil, List.all_cons,
        List.all_nil, Bool.and_true, Bool.or_false, hany, hA', Bool.not_false, Bool.false_and,
        Bool.true_and, Bool.false_or]
      rw [orFirst_eval, hnz, hi]
      exact hdbz i hiN p hp hpos'
    · have hV' : (P.map (fun x => decide (0 < x))).any id = false := by simpa using hV
      have hnone' : firstTrue (P.map (fun x => decide (0 < x))) = none := by
        cases h : firstTrue (P.map (fun x => decide (0 < x))) with
        | none => rfl
        | some i => exfalso; apply hV; rw [← firstTrue_isSome, h]; rfl
      simp [hV', hnone']

end GenSel

/-! ## Index form versus list form of moves -/

theorem firstIdx_cons (pr : Nat → Bool) (f : Nat → Nat) (x : Nat) (rest : List Nat) :
    firstIdx pr f (x :: rest) =
      if pr x then some (0, f x) else (firstIdx pr f rest).map (fun m => (m.1 + 1, m.2)) := by
  unfold firstIdx
  cases h : pr x
  · simp only [List.map_cons, h, firstTrue, Bool.false_eq_true, if_false]
    cases firstTrue (rest.map pr) <;> simp
  · simp [h, firstTrue]

theorem cancelIdx_eq_firstIdx (t : Nat) (P : List Nat) :
    cancelIdx t P = firstIdx (fun x => decide (x ^^^ t < x)) (fun x => x ^^^ t) P := by
  rw [cancelIdx_firstTrue]; rfl

theorem attainT_eq_primOr (t : Nat) (P : List Nat) :
    attainT t P = primOr (fun x => decide (x ^^^ t < x)) (fun x => x ^^^ t) P := by
  unfold attainT primOr; rw [cancelIdx_eq_firstIdx]
  cases firstIdx (fun x => decide (x ^^^ t < x)) (fun x => x ^^^ t) P <;> rfl

theorem cancelIdx_zero (P : List Nat) : cancelIdx 0 P = none := by
  induction P with
  | nil => rfl
  | cons x P ih => simp [cancelIdx, ih]

/-- The variable-target selection is the replay move of the recurrent controller. -/
theorem attainT_eq_replayMove (σ : Nat) (P : List Nat) : attainT σ P = replayMove σ P := by
  rw [replayMove_eq]
  unfold attainT selFor
  by_cases h : σ = 0
  · subst h; simp [cancelIdx_zero, firstSome]
  · simp only [h, if_false]
    cases cancelIdx σ P <;> rfl

/-- Applying an index-form move. -/
def applyM (P : List Nat) : Option (Nat × Nat) → Option (List Nat)
  | some m => some (P.set m.1 m.2)
  | none => none

theorem applyM_shift (x : Nat) (rest : List Nat) (o : Option (Nat × Nat)) :
    applyM (x :: rest) (o.map (fun m => (m.1 + 1, m.2))) = (applyM rest o).map (x :: ·) := by
  cases o <;> rfl

theorem subFirstGe_eq (u : Nat) : ∀ P : List Nat,
    subFirstGe u P = applyM P (firstIdx (fun x => decide (u ≤ x)) (fun x => x - u) P)
  | [] => rfl
  | x :: rest => by
    rw [firstIdx_cons]
    by_cases h : u ≤ x
    · simp [subFirstGe, h, applyM]
    · simp only [subFirstGe, h, if_false, decide_false, Bool.false_eq_true]
      rw [applyM_shift, subFirstGe_eq u rest]

theorem subFirstPos_eq : ∀ P : List Nat, subFirstPos P = applyM P (decIdx P)
  | [] => rfl
  | x :: rest => by
    by_cases h : 0 < x
    · simp [subFirstPos, decIdx, h, applyM]
    · simp only [subFirstPos, decIdx, h, if_false]
      rw [applyM_shift, subFirstPos_eq rest]

/-- The policy step of π_j in index form. -/
def policyIdx (j : Nat) (P : List Nat) : Option (Nat × Nat) :=
  primOr (fun x => decide (2 ^ j ≤ x)) (fun x => x - 2 ^ j) P

theorem policyIdx_step (j : Nat) (P : List Nat) : applyM P (policyIdx j P) = policyStep j P := by
  unfold policyIdx primOr policyStep
  rw [subFirstGe_eq]
  cases firstIdx (fun x => decide (2 ^ j ≤ x)) (fun x => x - 2 ^ j) P with
  | some m => rfl
  | none => rw [subFirstPos_eq]; rfl

/-! ## Variable-target selector -/

/-- Input vector: board on wires below B·N, then the bits of σ (little-endian). -/
def selIn (B N : Nat) (P : List Nat) (σ : Nat) : Nat → Bool := fun j =>
  if j < B * N then boardBits B P j else σ.testBit (j - B * N)

def sigW (B N q : Nat) : Circ := input (B * N + q)

/-- σ has its top bit at position k. -/
def topC (B N k : Nat) : Circ :=
  and (sigW B N k :: (List.range (B - 1 - k)).map (fun u => not (sigW B N (k + 1 + u))))

/-- Heap i cancels σ (σ ≠ 0 and x_i XOR σ < x_i). -/
def cancV (B N i : Nat) : Circ :=
  or ((List.range B).map (fun k => and [topC B N k, input (B * i + (B - 1 - k))]))

/-- Big-endian bit p of x_i XOR σ. -/
def xbV (B N i p : Nat) : Circ := xor2 (input (B * i + p)) (sigW B N (B - 1 - p))

def varSel (B N : Nat) : RCirc := genSel B N (cancV B N) (xbV B N)

section VarSel
variable {B N : Nat} {P : List Nat}

theorem selIn_board (σ : Nat) {j : Nat} (hj : j < B * N) : selIn B N P σ j = boardBits B P j := by
  simp [selIn, hj]

theorem selIn_sig (σ q : Nat) : selIn B N P σ (B * N + q) = σ.testBit q := by
  simp only [selIn, if_neg (show ¬ (B * N + q < B * N) by omega), Nat.add_sub_cancel_left]

theorem heap_lt {i p : Nat} (hi : i < N) (hp : p < B) : B * i + p < B * N := by
  have : B * i + B ≤ B * N := by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hi
  omega

theorem cancV_eval (hP : P.length = N) {σ : Nat} (hσ : σ < 2 ^ B) {i : Nat} (hi : i < N) :
    eval (selIn B N P σ) (cancV B N i) = decide (P.getD i 0 ^^^ σ < P.getD i 0) := by
  have e : decide (P.getD i 0 ^^^ σ < P.getD i 0) = decide (σ ≠ 0 ∧ P.getD i 0 ^^^ σ < P.getD i 0) := by
    by_cases h : σ = 0
    · subst h; simp
    · simp [h]
  rw [e]
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_iff, ControllerBits.canc_iff hσ]
  simp only [cancV, topC, sigW, eval_or, eval_and, eval_not, eval_input, List.any_map, List.all_cons,
    List.all_map, List.all_nil, List.any_eq_true, List.all_eq_true, List.mem_range, Function.comp_apply,
    Bool.and_eq_true, Bool.and_true, Bool.not_eq_true', selIn_sig]
  constructor
  · rintro ⟨k, hk, ⟨h1, h2⟩, h3⟩
    refine ⟨k, hk, h1, ?_, h2⟩
    rw [selIn_board σ (heap_lt hi (by omega)), boardBits_heap hP hi (by omega),
      show B - 1 - (B - 1 - k) = k by omega] at h3
    exact h3
  · rintro ⟨k, hk, h1, h2, h3⟩
    refine ⟨k, hk, ⟨h1, h3⟩, ?_⟩
    rw [selIn_board σ (heap_lt hi (by omega)), boardBits_heap hP hi (by omega),
      show B - 1 - (B - 1 - k) = k by omega]
    exact h2

theorem xbV_eval (hP : P.length = N) (σ : Nat) {i p : Nat} (hi : i < N) (hp : p < B) :
    eval (selIn B N P σ) (xbV B N i p) = (P.getD i 0 ^^^ σ).testBit (B - 1 - p) := by
  simp only [xbV, sigW, eval_xor2, eval_input, selIn_sig, selIn_board σ (heap_lt hi hp),
    boardBits_heap hP hi hp, Nat.testBit_xor]

/-- VARIABLE-TARGET SELECTOR EXACTNESS: for every σ < 2^B supplied on the σ wires, the
    circuit outputs `attainT σ P` (= `replayMove σ P`). -/
theorem varSel_correct (hP : P.length = N) (hw : Width B P) {σ : Nat} (hσ : σ < 2 ^ B) :
    selReadout (varSel B N) (selIn B N P σ) = attainT σ P := by
  rw [attainT_eq_primOr]
  apply genSel_correct hP hw _ (fun j hj => selIn_board σ hj)
  · intro i hi; exact cancV_eval hP hσ hi
  · intro x hx
    rcases Nat.eq_zero_or_pos x with h | h
    · subst h; simp at hx
    · exact h
  · intro x _ hx; exact Nat.xor_lt_two_pow hx hσ
  · intro i hi p hp _; exact xbV_eval hP σ hi hp

end VarSel

/-! ## Multi-head reconstruction and move selection -/

/-- Input vector: board, then the B rollout outcome bits o 0, …, o (B-1). -/
def obsIn (B N : Nat) (P : List Nat) (o : Nat → Bool) : Nat → Bool := fun j =>
  if j < B * N then boardBits B P j else o (j - B * N)

/-- σ_j from the outcome wires: σ₀ = o₀, σⱼ = oⱼ ⊕ o₀ (j < B). -/
def recC (B N j : Nat) : Circ :=
  if j < B then (if j = 0 then input (B * N) else xor2 (input (B * N + j)) (input (B * N))) else const false

def mhSubst (B N : Nat) : Nat → Circ := fun w => if w < B * N then input w else recC B N (w - B * N)

/-- The multi-head selector: the variable-target selector with σ reconstructed. -/
def mhSel (B N : Nat) : RCirc := substR (mhSubst B N) (varSel B N)

theorem mh_inputs (B N : Nat) (P : List Nat) (o : Nat → Bool) :
    (fun w => eval (obsIn B N P o) (mhSubst B N w)) = selIn B N P (reconstruct B o) := by
  funext w
  unfold mhSubst selIn
  by_cases hw : w < B * N
  · simp [hw, obsIn]
  · simp only [hw, if_false]
    unfold reconstruct
    rw [testBit_ofBits]
    unfold recC recoverBit
    by_cases hj : w - B * N < B
    · by_cases h0 : w - B * N = 0
      · have hB : 0 < B := by omega
        rw [h0]
        simp [hB, obsIn]
      · simp only [hj, h0, if_true, if_false, eval_xor2, eval_input, decide_true, Bool.true_and]
        simp [obsIn, show ¬ (B * N + (w - B * N) < B * N) by omega, show ¬ (B * N < B * N) by omega]
    · simp [hj]

/-- MULTI-HEAD SELECTOR: for any outcome vector o the circuit outputs
    `attainT (reconstruct B o) P`; on the true rollout outcomes of a B-bit board it
    outputs `decisionMove P` (legal, zero successor from nonzero positions, halting
    exactly on terminal boards: `Controller.decision_correct`). -/
theorem mhSel_correct {B N : Nat} {P : List Nat} (hP : P.length = N) (hw : Width B P) (o : Nat → Bool) :
    selReadout (mhSel B N) (obsIn B N P o) = attainT (reconstruct B o) P := by
  unfold mhSel
  rw [selReadout_subst, mh_inputs]
  exact varSel_correct hP hw (ofBits_lt B _)

theorem mhSel_outcomes {B N : Nat} {P : List Nat} (hP : P.length = N) (hw : Width B P) :
    selReadout (mhSel B N) (obsIn B N P (outcomes P)) = Controller.decisionMove P := by
  rw [mhSel_correct hP hw, reconstruct_eq hw, attainT_eq_replayMove]
  rfl

/-! ## Policy-step circuits for π_j -/

/-- Heap i is eligible for π_j: 2^j ≤ x_i (some bit at position ≥ j is set). -/
def eligC (B j i : Nat) : Circ :=
  or ((List.range (B - j)).map (fun u => input (B * i + (B - 1 - (j + u)))))

/-- Big-endian bit p of x_i − 2^j (valid when 2^j ≤ x_i). -/
def subbitC (B j i p : Nat) : Circ :=
  if B - 1 - p < j then input (B * i + p)
  else xor2 (input (B * i + p))
    (and ((List.range (B - 1 - p - j)).map (fun m => not (input (B * i + (B - 1 - (j + m)))))))

def polSel (B N j : Nat) : RCirc := genSel B N (eligC B j) (subbitC B j)

theorem pow_le_iff_bit {x j B : Nat} (hx : x < 2 ^ B) :
    2 ^ j ≤ x ↔ ∃ u < B - j, x.testBit (j + u) = true := by
  constructor
  · intro h
    have hx0 : x ≠ 0 := by have := Nat.two_pow_pos j; omega
    have h1 : j ≤ x.log2 := by
      rcases Nat.lt_or_ge x.log2 j with h' | h'
      · exfalso
        have := Nat.lt_log2_self (n := x)
        have : x < 2 ^ j := Nat.lt_of_lt_of_le this (Nat.pow_le_pow_right (by decide) (by omega))
        omega
      · exact h'
    have h2 : x.log2 < B := by
      rcases Nat.lt_or_ge x.log2 B with h' | h'
      · exact h'
      · exfalso
        have := Nat.log2_self_le hx0
        have : 2 ^ B ≤ x := Nat.le_trans (Nat.pow_le_pow_right (by decide) h') this
        omega
    refine ⟨x.log2 - j, by omega, ?_⟩
    rw [show j + (x.log2 - j) = x.log2 by omega]
    cases hb : x.testBit x.log2 with
    | true => rfl
    | false =>
      exfalso
      have : x < 2 ^ x.log2 := by
        apply Nat.lt_pow_two_of_testBit
        intro i hi
        by_cases hik : i = x.log2
        · subst hik; exact hb
        · exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le Nat.lt_log2_self
            (Nat.pow_le_pow_right (by decide) (by omega)))
      exact absurd (Nat.log2_self_le hx0) (Nat.not_le.mpr this)
  · rintro ⟨u, _, hu⟩
    exact Nat.le_trans (Nat.pow_le_pow_right (by decide) (by omega)) (Nat.ge_two_pow_of_testBit hu)

theorem sub_pow_testBit {x j : Nat} (hx : 2 ^ j ≤ x) (k : Nat) :
    (x - 2 ^ j).testBit k =
      if k < j then x.testBit k else xor (x.testBit k) (decide (∀ m < k - j, x.testBit (j + m) = false)) := by
  have hq : 0 < x / 2 ^ j := Nat.div_pos hx (Nat.two_pow_pos j)
  have hdecomp : x - 2 ^ j = 2 ^ j * (x / 2 ^ j - 1) + x % 2 ^ j := by
    have h1 := Nat.div_add_mod x (2 ^ j)
    have h2 : 2 ^ j * (x / 2 ^ j - 1) + 2 ^ j = 2 ^ j * (x / 2 ^ j) := by
      rw [Nat.mul_sub_one]; have := Nat.le_mul_of_pos_right (2 ^ j) hq; omega
    omega
  rw [hdecomp, Nat.testBit_two_pow_mul_add _ (Nat.mod_lt _ (Nat.two_pow_pos j))]
  by_cases hk : k < j
  · simp only [hk, if_true]
    rw [Nat.testBit_mod_two_pow]; simp [hk]
  · simp only [hk, if_false]
    rw [testBit_pred _ hq]
    simp only [Nat.testBit_div_two_pow]
    rw [show k - j + j = k by omega]
    congr 1
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_iff]
    constructor
    · intro h m hm; rw [Nat.add_comm]; exact h m hm
    · intro h m hm; rw [Nat.add_comm]; exact h m hm

theorem eligC_eval {B N j : Nat} {P : List Nat} (hP : P.length = N) (hw : Width B P) {i : Nat} (hi : i < N) :
    eval (boardBits B P) (eligC B j i) = decide (2 ^ j ≤ P.getD i 0) := by
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_iff, pow_le_iff_bit (getD_lt_of_width hP hw hi)]
  simp only [eligC, eval_or, List.any_map, List.any_eq_true, List.mem_range, Function.comp_apply,
    eval_input]
  constructor
  · rintro ⟨u, hu, h⟩
    rw [boardBits_heap hP hi (by omega), show B - 1 - (B - 1 - (j + u)) = j + u by omega] at h
    exact ⟨u, hu, h⟩
  · rintro ⟨u, hu, h⟩
    refine ⟨u, hu, ?_⟩
    rw [boardBits_heap hP hi (by omega), show B - 1 - (B - 1 - (j + u)) = j + u by omega]
    exact h

theorem subbitC_eval {B N j : Nat} {P : List Nat} (hP : P.length = N) {i p : Nat} (hi : i < N) (hp : p < B)
    (hx : 2 ^ j ≤ P.getD i 0) :
    eval (boardBits B P) (subbitC B j i p) = (P.getD i 0 - 2 ^ j).testBit (B - 1 - p) := by
  rw [sub_pow_testBit hx]
  unfold subbitC
  by_cases hk : B - 1 - p < j
  · simp only [hk, if_true, eval_input, boardBits_heap hP hi hp]
  · simp only [hk, if_false, eval_xor2, eval_input, boardBits_heap hP hi hp]
    congr 1
    apply Bool.eq_iff_iff.mpr
    simp only [eval_and, List.all_map, List.all_eq_true, List.mem_range, Function.comp_apply, eval_not,
      eval_input, Bool.not_eq_true', decide_eq_true_iff]
    constructor
    · intro h m hm
      have := h m hm
      rwa [boardBits_heap hP hi (by omega), show B - 1 - (B - 1 - (j + m)) = j + m by omega] at this
    · intro h m hm
      rw [boardBits_heap hP hi (by omega), show B - 1 - (B - 1 - (j + m)) = j + m by omega]
      exact h m hm

/-- POLICY-STEP CIRCUIT EXACTNESS: the circuit outputs the π_j move (index form), and
    applying it gives exactly `policyStep j P`. -/
theorem polSel_correct {B N j : Nat} {P : List Nat} (hP : P.length = N) (hw : Width B P) :
    selReadout (polSel B N j) (boardBits B P) = policyIdx j P ∧
      applyM P (selReadout (polSel B N j) (boardBits B P)) = policyStep j P := by
  have h : selReadout (polSel B N j) (boardBits B P) = policyIdx j P := by
    apply genSel_correct hP hw _ (fun _ _ => rfl)
    · intro i hi; exact eligC_eval hP hw hi
    · intro x hx; have := Nat.two_pow_pos j; simp at hx; omega
    · intro x _ hx; exact Nat.lt_of_le_of_lt (Nat.sub_le _ _) hx
    · intro i hi p hp hx; exact subbitC_eval hP hi hp (by simpa using hx)
  exact ⟨h, by rw [h, policyIdx_step]⟩

/-! ## Resources: constant depth, polynomial size -/

/-- All formulas of a readout: depth ≤ D, size ≤ S, inputs below M. -/
def SelBound (R : RCirc) (N B D S M : Nat) : Prop :=
  R.sel.length = N ∧ R.val.length = B ∧
    ∀ c ∈ R.valid :: (R.sel ++ R.val), depth c ≤ D ∧ size c ≤ S ∧ maxInput c ≤ M

section Res
variable {U : Nat}

theorem lift1 (hU : 1 ≤ U) {x a k a' k' : Nat} (h : x ≤ a * U ^ k) (ha : a ≤ a') (hk : k ≤ k') :
    x ≤ a' * U ^ k' :=
  Nat.le_trans h (Nat.mul_le_mul ha (Nat.pow_le_pow_right hU hk))

theorem sz_firstC (hU : 1 ≤ U) {cs : Nat → Circ} {i a k : Nat} (hi : i + 1 ≤ U)
    (h : ∀ i' ≤ i, size (cs i') ≤ a * U ^ k) : size (firstC cs i) ≤ (a + 2) * U ^ (k + 1) := by
  unfold firstC
  apply size_and_le hU (by simp; omega)
  intro c hc
  simp only [List.mem_cons, List.mem_map, List.mem_range] at hc
  rcases hc with rfl | ⟨i', hi', rfl⟩
  · exact lift1 hU (h i (Nat.le_refl _)) (by omega) (Nat.le_refl _)
  · exact size_not_le hU (h i' (by omega))

theorem dp_firstC {cs : Nat → Circ} {i d : Nat} (h : ∀ i' ≤ i, depth (cs i') ≤ d) :
    depth (firstC cs i) ≤ d + 2 := by
  unfold firstC
  apply depth_and_le
  intro c hc
  simp only [List.mem_cons, List.mem_map, List.mem_range] at hc
  rcases hc with rfl | ⟨i', hi', rfl⟩
  · have := h i (Nat.le_refl _); omega
  · simp only [depth_not]; have := h i' (by omega); omega

theorem mx_firstC {cs : Nat → Circ} {i M : Nat} (h : ∀ i' ≤ i, maxInput (cs i') ≤ M) :
    maxInput (firstC cs i) ≤ M := by
  unfold firstC
  apply ControllerBits.maxInput_and_le
  intro c hc
  simp only [List.mem_cons, List.mem_map, List.mem_range] at hc
  rcases hc with rfl | ⟨i', hi', rfl⟩
  · exact h i (Nat.le_refl _)
  · simp only [maxInput_not]; exact h i' (by omega)

theorem sz_orFirst (hU : 2 ≤ U) {N : Nat} {cs bs : Nat → Circ} {a k : Nat} (hN : N ≤ U)
    (hcs : ∀ i < N, size (cs i) ≤ a * U ^ k) (hbs : ∀ i < N, size (bs i) ≤ a * U ^ k) :
    size (orFirst N cs bs) ≤ (a + 4) * U ^ (k + 3) := by
  have hU1 : 1 ≤ U := by omega
  unfold orFirst
  apply size_or_le hU1 (by simp; omega)
  intro c hc
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hc
  have hi' := List.mem_range.mp hi
  apply size_and_le hU1 (by simp; omega)
  intro c hc
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl
  · exact sz_firstC hU1 (by omega) (fun i' hi'' => hcs i' (by omega))
  · exact lift1 hU1 (hbs i hi') (by omega) (by omega)

theorem dp_orFirst {N : Nat} {cs bs : Nat → Circ} {d : Nat} (hcs : ∀ i < N, depth (cs i) ≤ d)
    (hbs : ∀ i < N, depth (bs i) ≤ d + 2) : depth (orFirst N cs bs) ≤ d + 4 := by
  unfold orFirst
  apply depth_or_le
  intro c hc
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hc
  have hi' := List.mem_range.mp hi
  apply depth_and_le
  intro c hc
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl
  · have := dp_firstC (cs := cs) (i := i) (d := d) (fun i' hi'' => hcs i' (by omega)); omega
  · have := hbs i hi'; omega

theorem mx_orFirst {N M : Nat} {cs bs : Nat → Circ} (hcs : ∀ i < N, maxInput (cs i) ≤ M)
    (hbs : ∀ i < N, maxInput (bs i) ≤ M) : maxInput (orFirst N cs bs) ≤ M := by
  unfold orFirst
  apply ControllerBits.maxInput_or_le
  intro c hc
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hc
  have hi' := List.mem_range.mp hi
  apply ControllerBits.maxInput_and_le
  intro c hc
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl
  · exact mx_firstC (fun i' hi'' => hcs i' (by omega))
  · exact hbs i hi'

end Res

section GenRes
variable {B N : Nat}

theorem nzC_res (hU : 2 ≤ U) (hB : B ≤ U) (i : Nat) :
    size (AttainCircuit.nzC B i) ≤ 2 * U ^ 1 ∧ depth (AttainCircuit.nzC B i) ≤ 1 := by
  have hU1 : 1 ≤ U := by omega
  refine ⟨?_, ?_⟩
  · unfold AttainCircuit.nzC
    apply size_or_le hU1 (by simp; omega)
    intro c hc; obtain ⟨p, _, rfl⟩ := List.mem_map.mp hc; simp
  · unfold AttainCircuit.nzC
    apply depth_or_le; intro c hc; obtain ⟨p, _, rfl⟩ := List.mem_map.mp hc; simp

theorem decbitC_res (hU : 2 ≤ U) (hB : B ≤ U) (i p : Nat) :
    size (decbitC B i p) ≤ 6 * U ^ 3 ∧ depth (decbitC B i p) ≤ 5 := by
  have hU1 : 1 ≤ U := by omega
  have hl1 : size (lowZeroC B i p) ≤ 3 * U ^ 1 := by
    unfold lowZeroC
    apply size_and_le hU1 (by simp; omega)
    intro c hc; obtain ⟨r, _, rfl⟩ := List.mem_map.mp hc; simp
  have hl2 : depth (lowZeroC B i p) ≤ 2 := by
    unfold lowZeroC
    apply depth_and_le; intro c hc; obtain ⟨r, _, rfl⟩ := List.mem_map.mp hc; simp
  unfold decbitC xor2
  generalize lowZeroC B i p = L at hl1 hl2
  refine ⟨?_, ?_⟩
  · apply size_or_le hU1 (by simp; omega)
    intro c hc
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · apply size_and_le hU1 (by simp; omega)
      intro c hc
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact lift1 hU1 (show size (input (B * i + p)) ≤ 1 * U ^ 0 by simp) (by omega) (by omega)
      · exact size_not_le hU1 hl1
    · apply size_and_le hU1 (by simp; omega)
      intro c hc
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact lift1 hU1 (show size (not (input (B * i + p))) ≤ 2 * U ^ 0 by simp) (by omega) (by omega)
      · exact lift1 hU1 hl1 (by omega) (Nat.le_refl _)
  · simp only [depth_or, depth_and, depth_not, depth_input, List.map_cons, List.map_nil, listMax,
      List.foldr_cons, List.foldr_nil]
    omega

/-- GENERIC SELECTOR RESOURCES: depth ≤ d + 9, size ≤ 12·U^8 with
    U = (N+2)(B+2)(s+2), inputs below M. -/
theorem genSel_bound (prim : Nat → Circ) (pv : Nat → Nat → Circ) (d s M : Nat)
    (hprim : ∀ i < N, depth (prim i) ≤ d ∧ size (prim i) ≤ s ∧ maxInput (prim i) ≤ M)
    (hpv : ∀ i < N, ∀ p < B, depth (pv i p) ≤ d ∧ size (pv i p) ≤ s ∧ maxInput (pv i p) ≤ M)
    (hM : B * N ≤ M) :
    SelBound (genSel B N prim pv) N B (d + 9) (12 * ((N + 2) * (B + 2) * (s + 2)) ^ 8) M := by
  generalize hUdef : (N + 2) * (B + 2) * (s + 2) = U
  have hNU : N + 2 ≤ U := by
    rw [← hUdef]
    have := Nat.le_mul_of_pos_right (N + 2) (show 0 < (B + 2) * (s + 2) from Nat.mul_pos (by omega) (by omega))
    rw [Nat.mul_assoc]; exact this
  have hBU : B + 2 ≤ U := by
    rw [← hUdef]
    have := Nat.le_mul_of_pos_left (B + 2) (show 0 < N + 2 by omega)
    have h2 := Nat.le_mul_of_pos_right ((N + 2) * (B + 2)) (show 0 < s + 2 by omega)
    exact Nat.le_trans this h2
  have hsU : s + 2 ≤ U := by
    rw [← hUdef]
    exact Nat.le_mul_of_pos_left (s + 2) (show 0 < (N + 2) * (B + 2) from Nat.mul_pos (by omega) (by omega))
  have hU2 : 2 ≤ U := by omega
  have hU1 : 1 ≤ U := by omega
  have hps : ∀ i < N, size (prim i) ≤ 1 * U ^ 1 := fun i hi => by
    have := (hprim i hi).2.1; simp; omega
  have hvs : ∀ i < N, ∀ p < B, size (pv i p) ≤ 1 * U ^ 1 := fun i hi p hp => by
    have := (hpv i hi p hp).2.1; simp; omega
  -- the shared OR of primary tests
  have hA_s : size (anyC' N prim) ≤ 2 * U ^ 2 := by
    unfold anyC'
    apply size_or_le hU1 (by simp; omega)
    intro c hc; obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hc; exact hps i (List.mem_range.mp hi)
  have hA_d : depth (anyC' N prim) ≤ d + 1 := by
    unfold anyC'
    apply depth_or_le
    intro c hc; obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hc; exact (hprim i (List.mem_range.mp hi)).1
  have hA_m : maxInput (anyC' N prim) ≤ M := by
    unfold anyC'
    apply ControllerBits.maxInput_or_le
    intro c hc; obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hc; exact (hprim i (List.mem_range.mp hi)).2.2
  refine ⟨by simp [genSel], by simp [genSel], ?_⟩
  intro c hc
  simp only [genSel, List.mem_cons, List.mem_append, List.mem_map, List.mem_range] at hc
  rcases hc with rfl | ⟨i, hi, rfl⟩ | ⟨p, hp, rfl⟩
  · -- validity
    refine ⟨?_, ?_, ?_⟩
    · unfold validA; apply depth_or_le
      intro c hc; obtain ⟨i, _, rfl⟩ := List.mem_map.mp hc
      have := (nzC_res hU2 (by omega) (B := B) i).2; omega
    · unfold validA
      have h1 := size_or_le (a := 2) (k := 1) hU1 (cs := (List.range N).map (AttainCircuit.nzC B))
        (by simp; omega) (fun c hc => by
          obtain ⟨i, _, rfl⟩ := List.mem_map.mp hc; exact (nzC_res hU2 (by omega) i).1)
      have h2 : (2 + 1) * U ^ (1 + 1) ≤ 12 * U ^ 8 :=
        Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right hU1 (by omega))
      omega
    · unfold validA
      apply ControllerBits.maxInput_or_le
      intro c hc; obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hc
      exact Nat.le_trans (max_nzC (List.mem_range.mp hi)) hM
  · -- selection formula i
    refine ⟨?_, ?_, ?_⟩
    · apply depth_or_le
      intro c hc
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · have := (hprim i hi).1; omega
      · apply depth_and_le
        intro c hc
        simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl
        · simp only [depth_not]; omega
        · have := (nzC_res hU2 (by omega) (B := B) i).2; omega
    · have h1 : size (or [prim i, and [not (anyC' N prim), AttainCircuit.nzC B i]]) ≤ 5 * U ^ 4 := by
        apply size_or_le hU1 (by simp; omega)
        intro c hc
        simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl
        · exact lift1 hU1 (hps i hi) (by omega) (by omega)
        · apply size_and_le hU1 (by simp; omega)
          intro c hc
          simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hc
          rcases hc with rfl | rfl
          · exact lift1 hU1 (size_not_le hU1 hA_s) (by omega) (by omega)
          · exact lift1 hU1 (nzC_res hU2 (by omega) i).1 (by omega) (by omega)
      exact Nat.le_trans h1 (Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right hU1 (by omega)))
    · apply ControllerBits.maxInput_or_le
      intro c hc
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact (hprim i hi).2.2
      · apply ControllerBits.maxInput_and_le
        intro c hc
        simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl
        · simp only [maxInput_not]; exact hA_m
        · exact Nat.le_trans (max_nzC hi) hM
  · -- value bit p
    have hO1s : size (orFirst N prim (fun i => pv i p)) ≤ 5 * U ^ 4 :=
      sz_orFirst hU2 (by omega) hps (fun i hi => hvs i hi p hp)
    have hO2s : size (orFirst N (AttainCircuit.nzC B) (fun i => decbitC B i p)) ≤ 10 * U ^ 6 :=
      sz_orFirst hU2 (by omega) (fun i _ => lift1 hU1 (nzC_res hU2 (by omega) i).1 (by omega) (by omega))
        (fun i _ => (decbitC_res hU2 (by omega) i p).1)
    have hO1d : depth (orFirst N prim (fun i => pv i p)) ≤ d + 4 :=
      dp_orFirst (fun i hi => (hprim i hi).1) (fun i hi => by have := (hpv i hi p hp).1; omega)
    have hO2d : depth (orFirst N (AttainCircuit.nzC B) (fun i => decbitC B i p)) ≤ 3 + 4 :=
      dp_orFirst (fun i _ => by have := (nzC_res hU2 (by omega) (B := B) i).2; omega)
        (fun i _ => (decbitC_res hU2 (by omega) i p).2)
    have hO1m : maxInput (orFirst N prim (fun i => pv i p)) ≤ M :=
      mx_orFirst (fun i hi => (hprim i hi).2.2) (fun i hi => (hpv i hi p hp).2.2)
    have hO2m : maxInput (orFirst N (AttainCircuit.nzC B) (fun i => decbitC B i p)) ≤ M :=
      mx_orFirst (fun i hi => Nat.le_trans (max_nzC hi) hM)
        (fun i hi => Nat.le_trans (max_decbitC hi hp) hM)
    generalize orFirst N prim (fun i => pv i p) = O1 at hO1s hO1d hO1m
    generalize orFirst N (AttainCircuit.nzC B) (fun i => decbitC B i p) = O2 at hO2s hO2d hO2m
    generalize anyC' N prim = A at hA_s hA_d hA_m
    refine ⟨?_, ?_, ?_⟩
    · simp only [depth_or, depth_and, depth_not, List.map_cons, List.map_nil, listMax,
        List.foldr_cons, List.foldr_nil]
      omega
    · apply size_or_le hU1 (by simp; omega)
      intro c hc
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · apply size_and_le hU1 (by simp; omega)
        intro c hc
        simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl
        · exact lift1 hU1 hA_s (by omega) (by omega)
        · exact lift1 hU1 hO1s (by omega) (by omega)
      · apply size_and_le hU1 (by simp; omega)
        intro c hc
        simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl
        · exact lift1 hU1 (size_not_le hU1 hA_s) (by omega) (by omega)
        · exact hO2s
    · simp only [maxInput_or, maxInput_and, maxInput_not, List.map_cons, List.map_nil, listMax,
        List.foldr_cons, List.foldr_nil]
      omega

end GenRes

theorem substR_bound {R : RCirc} {N B D S M D' S' M' : Nat} (τ : Nat → Circ) (hR : SelBound R N B D S M)
    (hτd : ∀ w, depth (τ w) ≤ D') (hτs : ∀ w, size (τ w) ≤ S') (hτm : ∀ w, maxInput (τ w) ≤ M') :
    SelBound (substR τ R) N B (D + D') (S * (S' + 1)) M' := by
  obtain ⟨h1, h2, h3⟩ := hR
  refine ⟨by simp [substR, h1], by simp [substR, h2], ?_⟩
  intro c hc
  have : ∃ c', c' ∈ R.valid :: (R.sel ++ R.val) ∧ c = subst τ c' := by
    simp only [substR, List.mem_cons, List.mem_append, List.mem_map] at hc
    rcases hc with rfl | ⟨c', hc', rfl⟩ | ⟨c', hc', rfl⟩
    · exact ⟨R.valid, by simp, rfl⟩
    · exact ⟨c', by simp [hc'], rfl⟩
    · exact ⟨c', by simp [hc'], rfl⟩
  obtain ⟨c', hc', rfl⟩ := this
  obtain ⟨hd, hs, _⟩ := h3 c' hc'
  refine ⟨Nat.le_trans (depth_subst_le τ D' hτd c') (by omega),
    Nat.le_trans (size_subst_le τ S' hτs c') (Nat.mul_le_mul_right _ hs), maxInput_subst_le τ M' hτm c'⟩

section InstRes
variable {B N : Nat}

theorem cancV_res {i : Nat} (hi : i < N) :
    depth (cancV B N i) ≤ 4 ∧ size (cancV B N i) ≤ B * (2 * B + 3) + 9 ∧ maxInput (cancV B N i) ≤ B * N + B := by
  refine ⟨?_, ?_, ?_⟩
  · unfold cancV; apply depth_or_le; intro c hc
    obtain ⟨k, _, rfl⟩ := List.mem_map.mp hc
    apply depth_and_le; intro c hc
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · unfold topC; apply depth_and_le; intro c hc
      simp only [List.mem_cons, List.mem_map, List.mem_range] at hc
      rcases hc with rfl | ⟨u, _, rfl⟩ <;> simp [sigW]
    · simp
  · unfold cancV
    have := ControllerBits.size_or_le' (S := 2 * B + 3) (cs := (List.range B).map (fun k => and [topC B N k, input (B * i + (B - 1 - k))])) (by
      intro c hc
      obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hc
      have hk' := List.mem_range.mp hk
      have ht := ControllerBits.size_and_le' (S := 2) (cs := sigW B N k :: (List.range (B - 1 - k)).map
        (fun u => not (sigW B N (k + 1 + u)))) (by
          intro c hc
          simp only [List.mem_cons, List.mem_map, List.mem_range] at hc
          rcases hc with rfl | ⟨u, _, rfl⟩ <;> simp [sigW])
      simp only [List.length_cons, List.length_map, List.length_range] at ht
      have ht' : size (topC B N k) ≤ (B - 1 - k + 1) * 2 + 1 := ht
      simp only [size_and, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, size_input]
      have : (B - 1 - k + 1) * 2 + 1 + 2 ≤ 2 * B + 3 := by omega
      omega)
    simp only [List.length_map, List.length_range] at this
    omega
  · unfold cancV; apply ControllerBits.maxInput_or_le; intro c hc
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hc
    have hk' := List.mem_range.mp hk
    apply ControllerBits.maxInput_and_le; intro c hc
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · unfold topC; apply ControllerBits.maxInput_and_le; intro c hc
      simp only [List.mem_cons, List.mem_map, List.mem_range] at hc
      rcases hc with rfl | ⟨u, hu, rfl⟩
      · simp [sigW]; omega
      · simp [sigW]; omega
    · simp; have := heap_lt (B := B) (N := N) hi (show B - 1 - k < B by omega); omega

theorem xbV_res {i p : Nat} (hi : i < N) (hp : p < B) :
    depth (xbV B N i p) ≤ 3 ∧ size (xbV B N i p) ≤ 9 ∧ maxInput (xbV B N i p) ≤ B * N + B := by
  have := heap_lt (B := B) (N := N) hi hp
  refine ⟨?_, ?_, ?_⟩ <;> simp [xbV, xor2, sigW, listMax] <;> omega

/-- The variable-target selector: depth ≤ 13, size ≤ 12·U^8 with
    U = (N+2)(B+2)(2B²+3B+11), inputs below B·N + B. -/
theorem varSel_bound :
    SelBound (varSel B N) N B (4 + 9) (12 * ((N + 2) * (B + 2) * (B * (2 * B + 3) + 9 + 2)) ^ 8) (B * N + B) :=
  genSel_bound (cancV B N) (xbV B N) 4 (B * (2 * B + 3) + 9) (B * N + B)
    (fun i hi => cancV_res hi)
    (fun i hi p hp => by obtain ⟨a, b, c⟩ := xbV_res (B := B) (N := N) hi hp; exact ⟨by omega, by omega, c⟩)
    (by omega)

theorem recC_res (j : Nat) : depth (recC B N j) ≤ 3 ∧ size (recC B N j) ≤ 9 ∧ maxInput (recC B N j) ≤ B * N + B := by
  unfold recC
  by_cases hj : j < B
  · by_cases h0 : j = 0
    · subst h0; simp [hj]; omega
    · simp [hj, h0, xor2, listMax]; omega
  · simp [hj]

/-- The multi-head selector: depth ≤ 16, size ≤ 120·U^8 (U as for `varSel`), reading the
    board and the B outcome wires only. -/
theorem mhSel_bound :
    SelBound (mhSel B N) N B (4 + 9 + 3)
      (12 * ((N + 2) * (B + 2) * (B * (2 * B + 3) + 9 + 2)) ^ 8 * (9 + 1)) (B * N + B) := by
  apply substR_bound (mhSubst B N) varSel_bound
  · intro w; unfold mhSubst; split
    · simp
    · exact (recC_res _).1
  · intro w; unfold mhSubst; split
    · simp
    · exact (recC_res _).2.1
  · intro w; unfold mhSubst; split
    · simp; omega
    · exact (recC_res _).2.2

theorem eligC_res (j : Nat) {i : Nat} (hi : i < N) :
    depth (eligC B j i) ≤ 5 ∧ size (eligC B j i) ≤ 4 * B + 9 ∧ maxInput (eligC B j i) ≤ B * N := by
  refine ⟨?_, ?_, ?_⟩
  · have : depth (eligC B j i) ≤ 1 := by
      unfold eligC; apply depth_or_le; intro c hc; obtain ⟨u, _, rfl⟩ := List.mem_map.mp hc; simp
    omega
  · unfold eligC
    have := ControllerBits.size_or_le' (S := 1) (cs := (List.range (B - j)).map (fun u => input (B * i + (B - 1 - (j + u)))))
      (by intro c hc; obtain ⟨u, _, rfl⟩ := List.mem_map.mp hc; simp)
    simp only [List.length_map, List.length_range] at this
    omega
  · unfold eligC; apply ControllerBits.maxInput_or_le; intro c hc
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hc
    have := List.mem_range.mp hu
    have := heap_lt (B := B) (N := N) hi (show B - 1 - (j + u) < B by omega)
    simp; omega

theorem subbitC_res (j : Nat) {i p : Nat} (hi : i < N) (hp : p < B) :
    depth (subbitC B j i p) ≤ 5 ∧ size (subbitC B j i p) ≤ 4 * B + 9 ∧ maxInput (subbitC B j i p) ≤ B * N := by
  have hip := heap_lt (B := B) (N := N) hi hp
  unfold subbitC
  by_cases hk : B - 1 - p < j
  · simp only [hk, if_true]; simp; omega
  · simp only [hk, if_false]
    have hs := ControllerBits.size_and_le' (S := 2) (cs := (List.range (B - 1 - p - j)).map
      (fun m => not (input (B * i + (B - 1 - (j + m)))))) (by
        intro c hc; obtain ⟨m, _, rfl⟩ := List.mem_map.mp hc; simp)
    have hd : depth (and ((List.range (B - 1 - p - j)).map
        (fun m => not (input (B * i + (B - 1 - (j + m))))))) ≤ 2 := by
      apply depth_and_le; intro c hc; obtain ⟨m, _, rfl⟩ := List.mem_map.mp hc; simp
    have hm : maxInput (and ((List.range (B - 1 - p - j)).map
        (fun m => not (input (B * i + (B - 1 - (j + m))))))) ≤ B * N := by
      apply ControllerBits.maxInput_and_le; intro c hc
      obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hc
      have := List.mem_range.mp hm
      have := heap_lt (B := B) (N := N) hi (show B - 1 - (j + m) < B by omega)
      simp; omega
    simp only [List.length_map, List.length_range] at hs
    generalize and ((List.range (B - 1 - p - j)).map (fun m => not (input (B * i + (B - 1 - (j + m)))))) = A
      at hs hd hm
    unfold xor2
    refine ⟨?_, ?_, ?_⟩
    · simp only [depth_or, depth_and, depth_not, depth_input, List.map_cons, List.map_nil, listMax,
        List.foldr_cons, List.foldr_nil]; omega
    · simp only [size_or, size_and, size_not, size_input, List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil]; omega
    · simp only [maxInput_or, maxInput_and, maxInput_not, maxInput_input, List.map_cons, List.map_nil,
        listMax, List.foldr_cons, List.foldr_nil]; omega

/-- The π_j policy-step circuit: depth ≤ 14, size ≤ 12·U^8 with U = (N+2)(B+2)(4B+11),
    reading only the B·N board wires. -/
theorem polSel_bound (j : Nat) :
    SelBound (polSel B N j) N B (5 + 9) (12 * ((N + 2) * (B + 2) * (4 * B + 9 + 2)) ^ 8) (B * N) :=
  genSel_bound (eligC B j) (subbitC B j) 5 (4 * B + 9) (B * N)
    (fun i hi => eligC_res j hi) (fun i hi p hp => subbitC_res j hi hp) (Nat.le_refl _)

end InstRes


/-! ## Axiom audit -/

#print axioms readoutOf_eq
#print axioms selReadout_subst
#print axioms orFirst_eval
#print axioms firstTrue_isSome
#print axioms max_nzC
#print axioms max_decbitC
#print axioms decbit_eval
#print axioms getD_lt_of_width
#print axioms map_getD_eq
#print axioms firstTrue_map_getD
#print axioms genSel_correct
#print axioms firstIdx_cons
#print axioms cancelIdx_eq_firstIdx
#print axioms attainT_eq_primOr
#print axioms cancelIdx_zero
#print axioms attainT_eq_replayMove
#print axioms applyM_shift
#print axioms subFirstGe_eq
#print axioms subFirstPos_eq
#print axioms policyIdx_step
#print axioms selIn_board
#print axioms selIn_sig
#print axioms heap_lt
#print axioms cancV_eval
#print axioms xbV_eval
#print axioms varSel_correct
#print axioms mh_inputs
#print axioms mhSel_correct
#print axioms mhSel_outcomes
#print axioms pow_le_iff_bit
#print axioms sub_pow_testBit
#print axioms eligC_eval
#print axioms subbitC_eval
#print axioms polSel_correct
#print axioms lift1
#print axioms sz_firstC
#print axioms dp_firstC
#print axioms mx_firstC
#print axioms sz_orFirst
#print axioms dp_orFirst
#print axioms mx_orFirst
#print axioms nzC_res
#print axioms decbitC_res
#print axioms genSel_bound
#print axioms substR_bound
#print axioms cancV_res
#print axioms xbV_res
#print axioms varSel_bound
#print axioms recC_res
#print axioms mhSel_bound
#print axioms eligC_res
#print axioms subbitC_res
#print axioms polSel_bound
end SelectCircuit
end NimAudit
