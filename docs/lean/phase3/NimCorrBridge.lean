import BitBridge

/- Phase 3, target D (paper-specific part).  Written by Claude (10 October 2026).
   Lean 4.26.0, core/Std only.

   Readouts given by circuits.  For each observed bit b the readout is a family of
   formulas on the N·B input bits (heap-major, big-endian): a validity formula,
   N selection formulas (chosen index = first true one) and B value formulas
   (big-endian new value).  `readoutOf` turns this into a phase-2 `Readout`.

   From these formulas we BUILD explicit formulas for
     first-true index selection, the indexed old-heap bits, the legality test
     (value < selected heap, big-endian comparator), the delta XOR, and the
     equality indicator H_{b,a} = 1[g_b(P) = a],
   prove them correct, and bound depth (≤ d + 11) and size (≤ 12 U^10 with
   U = (N+2)(B+2)(s+2)).  Then, ASSUMING the classical parity-correlation premise
   for formulas of that depth and size on every m with N ≤ m ≤ N·B, we derive the
   phase-2 hypothesis CorrHyp B N (readoutOf R) ε.

   CONDITIONAL: the classical AC0 parity-correlation theorem (Hastad et al.) is not
   formalised; it is the explicit hypothesis `ParityCorrPremise`.  No AC0 predicate
   is defined by its correlation property. -/

namespace NimAudit
namespace CorrBridge

open Prob AC0 AC0.Circ Game Bridge Rollout

attribute [local simp] Rat.add_zero Rat.zero_add Rat.zero_mul Rat.mul_zero Rat.one_mul
  Rat.mul_one

/-! ## Readouts given by circuits -/

structure RCirc where
  valid : Circ
  sel : List Circ
  val : List Circ

/-- Input bits of a board: heap i, big-endian position p (bit B-1-p) at index B·i + p. -/
def boardBits (B : Nat) (P : List Nat) : Nat → Bool := fun j =>
  if j < B * P.length then (P.getD (j / B) 0).testBit (B - 1 - j % B) else false

def firstTrue : List Bool → Option Nat
  | [] => none
  | true :: _ => some 0
  | false :: l => (firstTrue l).map (· + 1)

/-- The readout computed by the circuit families R false, R true. -/
def readoutOf (B : Nat) (R : Bool → RCirc) : Readout := fun P b =>
  if eval (boardBits B P) (R b).valid then
    match firstTrue ((R b).sel.map (eval (boardBits B P))) with
    | some i => some (i, toNatBE ((R b).val.map (eval (boardBits B P))))
    | none => none
  else none

theorem firstTrue_some_iff : ∀ (l : List Bool) (i : Nat),
    firstTrue l = some i ↔ i < l.length ∧ l.getD i false = true ∧ ∀ i' < i, l.getD i' false = false
  | [], i => by simp [firstTrue]
  | true :: l, 0 => by simp [firstTrue]
  | true :: l, i + 1 => by
    simp only [firstTrue, Option.some.injEq, List.getD_cons_succ, List.length_cons]
    constructor
    · intro h; omega
    · rintro ⟨_, _, h⟩; have := h 0 (by omega); simp at this
  | false :: l, 0 => by
    simp only [firstTrue, List.getD_cons_zero]
    cases firstTrue l <;> simp
  | false :: l, i + 1 => by
    simp only [firstTrue, List.getD_cons_succ, List.length_cons]
    rw [show (Option.map (· + 1) (firstTrue l) = some (i + 1)) ↔ firstTrue l = some i by
      cases firstTrue l <;> simp]
    rw [firstTrue_some_iff l i]
    constructor
    · rintro ⟨h1, h2, h3⟩
      refine ⟨by omega, h2, ?_⟩
      intro i' hi'
      cases i' with
      | zero => rfl
      | succ i' => simpa using h3 i' (by omega)
    · rintro ⟨h1, h2, h3⟩
      refine ⟨by omega, h2, ?_⟩
      intro i' hi'
      simpa using h3 (i' + 1) (by omega)

/-! ## Building blocks -/

def getC (cs : List Circ) (i : Nat) : Circ := cs.getD i (const false)

theorem eval_getC (z : Nat → Bool) (cs : List Circ) (i : Nat) :
    eval z (getC cs i) = (cs.map (eval z)).getD i false := by
  unfold getC
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases cs[i]? <;> simp

def selC (R : RCirc) (i : Nat) : Circ :=
  and (getC R.sel i :: (List.range i).map (fun i' => not (getC R.sel i')))

def heapC (B i p : Nat) : Circ := input (B * i + p)
def valC (R : RCirc) (p : Nat) : Circ := getC R.val p
def eqC (a b : Circ) : Circ := or [and [a, b], and [not a, not b]]
def xor2 (a b : Circ) : Circ := or [and [a, not b], and [not a, b]]

def ltC (R : RCirc) (B i : Nat) : Circ :=
  or ((List.range B).map (fun p =>
    and ([not (valC R p), heapC B i p] ++ (List.range p).map (fun p' => eqC (valC R p') (heapC B i p')))))

def legalC (R : RCirc) (N B : Nat) : Circ :=
  and [R.valid, or ((List.range N).map (fun i => and [selC R i, ltC R B i]))]

def gbitC (R : RCirc) (N B p : Nat) : Circ :=
  and [legalC R N B, or ((List.range N).map (fun i => and [selC R i, xor2 (valC R p) (heapC B i p)]))]

/-- The indicator formula for H_{b,a} = 1[g_b(P) = a]. -/
def HC (R : RCirc) (N B a : Nat) : Circ :=
  and ((List.range B).map (fun p =>
    if a.testBit (B - 1 - p) then gbitC R N B p else not (gbitC R N B p)))

theorem eval_eqC (z : Nat → Bool) (a b : Circ) : eval z (eqC a b) = (eval z a == eval z b) := by
  unfold eqC
  simp only [eval_or, eval_and, eval_not, List.all_cons, List.all_nil, List.any_cons, List.any_nil]
  generalize eval z a = p; generalize eval z b = q
  cases p <;> cases q <;> rfl

theorem eval_xor2 (z : Nat → Bool) (a b : Circ) : eval z (xor2 a b) = xor (eval z a) (eval z b) := by
  unfold xor2
  simp only [eval_or, eval_and, eval_not, List.all_cons, List.all_nil, List.any_cons, List.any_nil]
  generalize eval z a = p; generalize eval z b = q
  cases p <;> cases q <;> rfl

/-! ## Semantics on encoded boards -/

section Semantics

variable {B N : Nat} {P : List Nat} {R : RCirc}

theorem boardBits_heap (hP : P.length = N) {i p : Nat} (hi : i < N) (hp : p < B) :
    boardBits B P (B * i + p) = (P.getD i 0).testBit (B - 1 - p) := by
  unfold boardBits
  have hB : 0 < B := by omega
  have h1 : B * i + p < B * P.length := by
    rw [hP]
    have := Nat.mul_le_mul_left B (show i + 1 ≤ N by omega)
    rw [Nat.mul_succ] at this; omega
  have h2 : (B * i + p) / B = i := by
    rw [Nat.mul_comm, Nat.add_comm, Nat.add_mul_div_right _ _ hB, Nat.div_eq_of_lt hp]; omega
  have h3 : (B * i + p) % B = p := by
    rw [Nat.mul_comm, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hp]
  simp [h1, h2, h3]

theorem selC_eval (z : Nat → Bool) (hsel : R.sel.length = N) {i : Nat} (hi : i < N) :
    eval z (selC R i) = decide (firstTrue (R.sel.map (eval z)) = some i) := by
  unfold selC
  rw [Bool.eq_iff_iff, decide_eq_true_iff, firstTrue_some_iff]
  simp only [eval_and, List.all_cons, List.all_map, Bool.and_eq_true, List.all_eq_true,
    List.mem_range, Function.comp, eval_not, Bool.not_eq_true', eval_getC, List.length_map, hsel]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨hi, h1, h2⟩
  · rintro ⟨_, h1, h2⟩; exact ⟨h1, h2⟩

theorem val_eval (z : Nat → Bool) (hval : R.val.length = B) {p : Nat} (hp : p < B) :
    eval z (valC R p) = (toNatBE (R.val.map (eval z))).testBit (B - 1 - p) := by
  unfold valC
  rw [eval_getC]
  have := testBit_toNatBE (R.val.map (eval z)) p (by simp [hval, hp])
  simp only [List.length_map, hval] at this
  exact this.symm

/-- Big-endian comparison via the top differing bit. -/
theorem lt_iff_top {v h B : Nat} (hv : v < 2 ^ B) (hh : h < 2 ^ B) :
    v < h ↔ ∃ p < B, v.testBit (B - 1 - p) = false ∧ h.testBit (B - 1 - p) = true ∧
      ∀ p' < p, v.testBit (B - 1 - p') = h.testBit (B - 1 - p') := by
  have above : ∀ x k, x < 2 ^ B → B ≤ k → x.testBit k = false := fun x k hx hk =>
    Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) hk))
  constructor
  · intro hlt
    have hne : v ^^^ h ≠ 0 := fun e => by have := xor_eq_zero_imp e; omega
    let k := (v ^^^ h).log2
    have hk : (v ^^^ h).testBit k = true := by
      cases hb : (v ^^^ h).testBit k with
      | true => rfl
      | false =>
        exfalso
        have : v ^^^ h < 2 ^ k := by
          apply Nat.lt_pow_two_of_testBit
          intro i hi
          by_cases hik : i = k
          · subst hik; exact hb
          · exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le Nat.lt_log2_self
              (Nat.pow_le_pow_right (by decide) (by omega)))
        exact absurd (Nat.log2_self_le hne) (Nat.not_le.mpr this)
    have habove : ∀ i, k < i → v.testBit i = h.testBit i := by
      intro i hi
      have : (v ^^^ h).testBit i = false := Nat.testBit_lt_two_pow
        (Nat.lt_of_lt_of_le Nat.lt_log2_self (Nat.pow_le_pow_right (by decide) (by omega)))
      rw [Nat.testBit_xor] at this
      revert this; cases v.testBit i <;> cases h.testBit i <;> simp
    have hkB : k < B := by
      rcases Nat.lt_or_ge k B with h' | h'
      · exact h'
      · rw [Nat.testBit_xor, above v k hv h', above h k hh h'] at hk; cases hk
    rw [Nat.testBit_xor] at hk
    have hvk : v.testBit k = false := by
      cases hvb : v.testBit k
      · rfl
      · exfalso
        have hhk : h.testBit k = false := by rw [hvb] at hk; revert hk; cases h.testBit k <;> simp
        have := lt_of_top_testBit hhk hvb (fun i hi => (habove i hi).symm)
        omega
    have hhk : h.testBit k = true := by rw [hvk] at hk; simpa using hk
    refine ⟨B - 1 - k, by omega, ?_, ?_, ?_⟩
    · rw [show B - 1 - (B - 1 - k) = k by omega]; exact hvk
    · rw [show B - 1 - (B - 1 - k) = k by omega]; exact hhk
    · intro p' hp'; exact habove _ (by omega)
  · rintro ⟨p, hp, h1, h2, h3⟩
    apply lt_of_top_testBit h1 h2
    intro i hi
    rcases Nat.lt_or_ge i B with hiB | hiB
    · have := h3 (B - 1 - i) (by omega)
      rwa [show B - 1 - (B - 1 - i) = i by omega] at this
    · rw [above v i hv hiB, above h i hh hiB]

theorem ltC_eval (hP : P.length = N) (hw : Width B P) (hval : R.val.length = B)
    {i : Nat} (hi : i < N) :
    eval (boardBits B P) (ltC R B i) =
      decide (toNatBE (R.val.map (eval (boardBits B P))) < P.getD i 0) := by
  have hvlt : toNatBE (R.val.map (eval (boardBits B P))) < 2 ^ B := by
    have := toNatBE_lt (R.val.map (eval (boardBits B P))); simpa [hval] using this
  have hhlt : P.getD i 0 < 2 ^ B := by
    apply hw; simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_getElem (by omega)]; simp
  rw [Bool.eq_iff_iff, decide_eq_true_iff, lt_iff_top hvlt hhlt]
  unfold ltC
  simp only [eval_or, List.any_map, List.any_eq_true, List.mem_range, Function.comp, eval_and,
    List.all_append, List.all_cons, List.all_nil, Bool.and_eq_true, eval_not, Bool.not_eq_true',
    List.all_map, List.all_eq_true, eval_eqC, beq_iff_eq, Bool.and_true]
  constructor
  · rintro ⟨p, hp, ⟨h1, h2⟩, h3⟩
    unfold heapC at h2 h3
    rw [val_eval _ hval hp] at h1
    rw [eval_input, boardBits_heap hP hi hp] at h2
    refine ⟨p, hp, h1, h2, ?_⟩
    intro p' hp'
    have := h3 p' hp'
    rw [val_eval _ hval (by omega), eval_input, boardBits_heap hP hi (by omega)] at this
    exact this
  · rintro ⟨p, hp, h1, h2, h3⟩
    refine ⟨p, hp, ⟨?_, ?_⟩, ?_⟩
    · rw [val_eval _ hval hp]; exact h1
    · unfold heapC; rw [eval_input, boardBits_heap hP hi hp]; exact h2
    · intro p' hp'
      unfold heapC
      rw [val_eval _ hval (by omega), eval_input, boardBits_heap hP hi (by omega)]
      exact h3 p' hp'

/-- The value g_b(P) of the circuit readout. -/
theorem gval_readoutOf (R' : Bool → RCirc) (b : Bool) (P : List Nat) :
    gval (readoutOf B R') b P =
      if eval (boardBits B P) (R' b).valid = true then
        match firstTrue ((R' b).sel.map (eval (boardBits B P))) with
        | some i => (match P[i]? with
            | some x => if toNatBE ((R' b).val.map (eval (boardBits B P))) < x then
                x ^^^ toNatBE ((R' b).val.map (eval (boardBits B P))) else 0
            | none => 0)
        | none => 0
      else 0 := by
  unfold gval readoutOf
  by_cases hv : eval (boardBits B P) (R' b).valid = true
  · simp only [hv, if_true]
    cases firstTrue ((R' b).sel.map (eval (boardBits B P))) <;> rfl
  · simp [hv]

theorem legalC_eval (hP : P.length = N) (hw : Width B P) (hsel : R.sel.length = N)
    (hval : R.val.length = B) :
    eval (boardBits B P) (legalC R N B) =
      decide (eval (boardBits B P) R.valid = true ∧ ∃ i, i < N ∧
        firstTrue (R.sel.map (eval (boardBits B P))) = some i ∧
        toNatBE (R.val.map (eval (boardBits B P))) < P.getD i 0) := by
  unfold legalC
  rw [Bool.eq_iff_iff, decide_eq_true_iff]
  simp only [eval_and, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, eval_or,
    List.any_map, List.any_eq_true, List.mem_range, Function.comp]
  constructor
  · rintro ⟨h1, i, hi, h2, h3⟩
    rw [selC_eval _ hsel hi, decide_eq_true_iff] at h2
    rw [ltC_eval hP hw hval hi, decide_eq_true_iff] at h3
    exact ⟨h1, i, hi, h2, h3⟩
  · rintro ⟨h1, i, hi, h2, h3⟩
    refine ⟨h1, i, hi, ?_, ?_⟩
    · rw [selC_eval _ hsel hi, decide_eq_true_iff]; exact h2
    · rw [ltC_eval hP hw hval hi, decide_eq_true_iff]; exact h3

theorem gval_legal (R' : Bool → RCirc) (b : Bool) {i : Nat} (hP : P.length = N)
    (hv : eval (boardBits B P) (R' b).valid = true)
    (hf : firstTrue ((R' b).sel.map (eval (boardBits B P))) = some i) (hi : i < N)
    (hlt : toNatBE ((R' b).val.map (eval (boardBits B P))) < P.getD i 0) :
    gval (readoutOf B R') b P = P.getD i 0 ^^^ toNatBE ((R' b).val.map (eval (boardBits B P))) := by
  rw [gval_readoutOf]
  have hPi : P[i]? = some (P.getD i 0) := by
    simp only [List.getD_eq_getElem?_getD]; rw [List.getElem?_eq_getElem (by omega)]; simp
  simp only [hv, if_true, hf, hPi, hlt]

theorem gval_illegal (R' : Bool → RCirc) (b : Bool) (hP : P.length = N)
    (h : ¬ (eval (boardBits B P) (R' b).valid = true ∧ ∃ i, i < N ∧
      firstTrue ((R' b).sel.map (eval (boardBits B P))) = some i ∧
      toNatBE ((R' b).val.map (eval (boardBits B P))) < P.getD i 0)) :
    gval (readoutOf B R') b P = 0 := by
  rw [gval_readoutOf]
  by_cases hv : eval (boardBits B P) (R' b).valid = true
  · simp only [hv, if_true]
    cases hf : firstTrue ((R' b).sel.map (eval (boardBits B P))) with
    | none => rfl
    | some i =>
      simp only
      by_cases hi : i < N
      · have hPi : P[i]? = some (P.getD i 0) := by
          simp only [List.getD_eq_getElem?_getD]; rw [List.getElem?_eq_getElem (by omega)]; simp
        simp only [hPi]
        by_cases hlt : toNatBE ((R' b).val.map (eval (boardBits B P))) < P.getD i 0
        · exact absurd ⟨hv, i, hi, hf, hlt⟩ h
        · rw [if_neg hlt]
      · simp [List.getElem?_eq_none (show P.length ≤ i by omega)]
  · simp [hv]

/-- Each g-bit formula computes the corresponding bit of g_b(P). -/
theorem gbitC_eval (R' : Bool → RCirc) (b : Bool) (hP : P.length = N) (hw : Width B P)
    (hsel : (R' b).sel.length = N) (hval : (R' b).val.length = B) {p : Nat} (hp : p < B) :
    eval (boardBits B P) (gbitC (R' b) N B p) = (gval (readoutOf B R') b P).testBit (B - 1 - p) := by
  have hL := legalC_eval (R := R' b) hP hw hsel hval
  unfold gbitC
  simp only [eval_and, List.all_cons, List.all_nil, Bool.and_true]
  rw [hL]
  by_cases hleg : eval (boardBits B P) (R' b).valid = true ∧ ∃ i, i < N ∧
      firstTrue ((R' b).sel.map (eval (boardBits B P))) = some i ∧
      toNatBE ((R' b).val.map (eval (boardBits B P))) < P.getD i 0
  · obtain ⟨hv, i, hi, hf, hlt⟩ := hleg
    rw [gval_legal R' b hP hv hf hi hlt, decide_eq_true ⟨hv, i, hi, hf, hlt⟩, Bool.true_and,
      Nat.testBit_xor]
    apply Bool.eq_iff_iff.mpr
    simp only [eval_or, List.any_map, List.any_eq_true, List.mem_range, Function.comp, eval_and,
      List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
    constructor
    · rintro ⟨i', hi', hs, hx⟩
      rw [selC_eval _ hsel hi', decide_eq_true_iff, hf] at hs
      cases hs
      rw [eval_xor2, val_eval _ hval hp, heapC, eval_input, boardBits_heap hP hi' hp] at hx
      rw [Bool.xor_comm]; exact hx
    · intro hx
      refine ⟨i, hi, ?_, ?_⟩
      · rw [selC_eval _ hsel hi, decide_eq_true_iff]; exact hf
      · rw [eval_xor2, val_eval _ hval hp, heapC, eval_input, boardBits_heap hP hi hp]
        rw [Bool.xor_comm]; exact hx
  · rw [gval_illegal R' b hP hleg, decide_eq_false hleg, Bool.false_and, Nat.zero_testBit]

theorem gval_lt (R' : Bool → RCirc) (b : Bool) (hw : Width B P) (hval : (R' b).val.length = B) :
    gval (readoutOf B R') b P < 2 ^ B := by
  rw [gval_readoutOf]
  have hvlt : toNatBE ((R' b).val.map (eval (boardBits B P))) < 2 ^ B := by
    have := toNatBE_lt ((R' b).val.map (eval (boardBits B P))); simpa [hval] using this
  split
  · split
    · next i _ =>
      split
      · next x hx =>
        split
        · exact Nat.xor_lt_two_pow (hw x (List.mem_of_getElem? hx)) hvlt
        · exact Nat.two_pow_pos B
      · exact Nat.two_pow_pos B
    · exact Nat.two_pow_pos B
  · exact Nat.two_pow_pos B

/-- INDICATOR CORRECTNESS: on boards of N heaps below 2^B and a < 2^B,
    the formula HC evaluates to 1[g_b(P) = a]. -/
theorem HC_eval (R' : Bool → RCirc) (b : Bool) (hP : P.length = N) (hw : Width B P)
    (hsel : (R' b).sel.length = N) (hval : (R' b).val.length = B) {a : Nat} (ha : a < 2 ^ B) :
    eval (boardBits B P) (HC (R' b) N B a) = decide (gval (readoutOf B R') b P = a) := by
  have hg := gval_lt R' b hw hval
  unfold HC
  rw [Bool.eq_iff_iff, decide_eq_true_iff]
  simp only [eval_and, List.all_map, List.all_eq_true, List.mem_range, Function.comp]
  constructor
  · intro h
    apply Nat.eq_of_testBit_eq
    intro k
    rcases Nat.lt_or_ge k B with hk | hk
    · have := h (B - 1 - k) (by omega)
      rw [show B - 1 - (B - 1 - k) = k by omega] at this
      have hb := gbitC_eval R' b hP hw hsel hval (p := B - 1 - k) (by omega)
      rw [show B - 1 - (B - 1 - k) = k by omega] at hb
      revert this
      split
      · next hak => intro h1; rw [hb] at h1; rw [h1, hak]
      · next hak =>
        intro h1; simp only [eval_not, Bool.not_eq_true'] at h1
        rw [hb] at h1; rw [h1]; simpa using hak
    · rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hg (Nat.pow_le_pow_right (by decide) hk)),
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le ha (Nat.pow_le_pow_right (by decide) hk))]
  · intro he p hp
    have hb := gbitC_eval R' b hP hw hsel hval hp
    rw [he] at hb
    split
    · next hak => rw [hb, hak]
    · next hak => simp only [eval_not, hb]; simpa using hak

end Semantics

/-! ## Encoded boards: boardBits agrees with the bit vector -/

theorem getD_take_drop (x : List Bool) (k p B : Nat) (hp : p < B) :
    ((x.drop k).take B).getD p false = x.getD (k + p) false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_take, hp, List.getElem?_drop]

theorem decodeBoard_getD (B : Nat) : ∀ (N : Nat) (x : List Bool) (i : Nat), i < N →
    (decodeBoard B N x).getD i 0 = toNatBE ((x.drop (B * i)).take B)
  | 0, _, i, hi => by omega
  | N + 1, x, 0, _ => by simp [decodeBoard]
  | N + 1, x, i + 1, hi => by
    simp only [decodeBoard, List.getD_cons_succ]
    rw [decodeBoard_getD B N (x.drop B) i (by omega), List.drop_drop, Nat.mul_succ, Nat.add_comm]

theorem boardBits_decode {B N : Nat} {x : List Bool} (hx : x ∈ bitvecs (B * N)) :
    boardBits B (decodeBoard B N x) = vfun x := by
  funext j
  have hl := mem_bitvecs_length hx
  unfold boardBits vfun
  rw [length_decodeBoard]
  by_cases hj : j < B * N
  · simp only [hj, if_true]
    have hB : 0 < B := by
      rcases Nat.eq_zero_or_pos B with h | h
      · subst h; simp at hj
      · exact h
    have hi : j / B < N := by
      rw [Nat.div_lt_iff_lt_mul hB, Nat.mul_comm]; exact hj
    rw [decodeBoard_getD B N x (j / B) hi]
    have hm : j % B < B := Nat.mod_lt _ hB
    have hlen : ((x.drop (B * (j / B))).take B).length = B := by
      simp only [List.length_take, List.length_drop, hl]
      have := Nat.mul_le_mul_left B (show j / B + 1 ≤ N by omega)
      rw [Nat.mul_succ] at this
      omega
    have := testBit_toNatBE ((x.drop (B * (j / B))).take B) (j % B) (by rw [hlen]; exact hm)
    rw [hlen] at this
    rw [this, getD_take_drop x _ _ _ hm, Nat.div_add_mod]
  · simp only [hj, if_false]
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (show x.length ≤ j by omega)]

/-! ## Depth and size bounds -/

section Bounds

theorem depth_and_le {cs : List Circ} {D : Nat} (h : ∀ c ∈ cs, depth c ≤ D) :
    depth (and cs) ≤ D + 1 := by
  simp only [depth_and]
  have : listMax (cs.map depth) ≤ D := by
    apply listMax_le; intro a ha
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ha; exact h c hc
  omega

theorem depth_or_le {cs : List Circ} {D : Nat} (h : ∀ c ∈ cs, depth c ≤ D) :
    depth (or cs) ≤ D + 1 := by
  simp only [depth_or]
  have : listMax (cs.map depth) ≤ D := by
    apply listMax_le; intro a ha
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ha; exact h c hc
  omega

theorem sum_le_len_mul {cs : List Circ} {S : Nat} (h : ∀ c ∈ cs, size c ≤ S) :
    (cs.map size).sum ≤ cs.length * S := by
  have := sum_map_le_mem (l := cs) (f := size) (g := fun _ => S) h
  rw [List.map_const', List.sum_replicate_nat] at this
  exact this

theorem upow_pos {U k : Nat} (hU : 1 ≤ U) : 1 ≤ U ^ k := Nat.pow_pos hU

theorem size_and_le {cs : List Circ} {a k U : Nat} (hU : 1 ≤ U) (hl : cs.length ≤ U)
    (h : ∀ c ∈ cs, size c ≤ a * U ^ k) : size (and cs) ≤ (a + 1) * U ^ (k + 1) := by
  simp only [size_and]
  have h1 := sum_le_len_mul h
  have h2 : cs.length * (a * U ^ k) ≤ U * (a * U ^ k) := Nat.mul_le_mul_right _ hl
  have h3 : U * (a * U ^ k) = a * U ^ (k + 1) := by rw [Nat.pow_succ]; grind
  have h4 := upow_pos (k := k + 1) hU
  rw [Nat.add_mul, Nat.one_mul]
  omega

theorem size_or_le {cs : List Circ} {a k U : Nat} (hU : 1 ≤ U) (hl : cs.length ≤ U)
    (h : ∀ c ∈ cs, size c ≤ a * U ^ k) : size (or cs) ≤ (a + 1) * U ^ (k + 1) := by
  simp only [size_or]
  have h1 := sum_le_len_mul h
  have h2 : cs.length * (a * U ^ k) ≤ U * (a * U ^ k) := Nat.mul_le_mul_right _ hl
  have h3 : U * (a * U ^ k) = a * U ^ (k + 1) := by rw [Nat.pow_succ]; grind
  have h4 := upow_pos (k := k + 1) hU
  rw [Nat.add_mul, Nat.one_mul]
  omega

theorem size_lift {c : Circ} {a a' k k' U : Nat} (hU : 1 ≤ U) (h : size c ≤ a * U ^ k)
    (ha : a ≤ a') (hk : k ≤ k') : size c ≤ a' * U ^ k' :=
  Nat.le_trans h (Nat.mul_le_mul ha (Nat.pow_le_pow_right hU hk))

theorem size_not_le {c : Circ} {a k U : Nat} (hU : 1 ≤ U) (h : size c ≤ a * U ^ k) :
    size (not c) ≤ (a + 1) * U ^ k := by
  simp only [size_not]
  have := upow_pos (k := k) hU
  rw [Nat.add_mul, Nat.one_mul]; omega

/-- Resource hypotheses on the readout formulas. -/
structure RBound (R : RCirc) (N B d s : Nat) : Prop where
  sel_len : R.sel.length = N
  val_len : R.val.length = B
  depth_valid : depth R.valid ≤ d
  depth_sel : ∀ c ∈ R.sel, depth c ≤ d
  depth_val : ∀ c ∈ R.val, depth c ≤ d
  size_valid : size R.valid ≤ s
  size_sel : ∀ c ∈ R.sel, size c ≤ s
  size_val : ∀ c ∈ R.val, size c ≤ s
  max_valid : maxInput R.valid ≤ B * N
  max_sel : ∀ c ∈ R.sel, maxInput c ≤ B * N
  max_val : ∀ c ∈ R.val, maxInput c ≤ B * N

/-- The polynomial size parameter U = (N+2)(B+2)(s+2). -/
def Upar (N B s : Nat) : Nat := (N + 2) * (B + 2) * (s + 2)

variable {R : RCirc} {N B d s : Nat}

theorem Upar_ge (N B s : Nat) : 1 ≤ Upar N B s ∧ N + 1 ≤ Upar N B s ∧ B + 2 ≤ Upar N B s ∧
    s ≤ Upar N B s := by
  unfold Upar
  have h1 : 1 ≤ (N + 2) * (B + 2) := Nat.mul_pos (by omega) (by omega)
  refine ⟨Nat.mul_pos h1 (by omega), ?_, ?_, ?_⟩
  · have := Nat.mul_le_mul (show N + 2 ≤ (N + 2) * (B + 2) from Nat.le_mul_of_pos_right _ (by omega))
      (show 1 ≤ s + 2 by omega)
    omega
  · have := Nat.mul_le_mul (show B + 2 ≤ (N + 2) * (B + 2) from Nat.le_mul_of_pos_left _ (by omega))
      (show 1 ≤ s + 2 by omega)
    omega
  · have := Nat.mul_le_mul h1 (show s + 2 ≤ s + 2 from Nat.le_refl _)
    omega

theorem getC_size (hb : RBound R N B d s) (cs : List Circ) (hcs : ∀ c ∈ cs, size c ≤ s) (i : Nat) :
    size (getC cs i) ≤ 1 * Upar N B s ^ 1 := by
  have hU := (Upar_ge N B s).2.2.2
  unfold getC
  simp only [List.getD_eq_getElem?_getD]
  cases h : cs[i]? with
  | none => simp; exact (Upar_ge N B s).1
  | some c => simp; exact Nat.le_trans (hcs c (List.mem_of_getElem? h)) hU

theorem getC_depth (cs : List Circ) (hcs : ∀ c ∈ cs, depth c ≤ d) (i : Nat) : depth (getC cs i) ≤ d := by
  unfold getC
  simp only [List.getD_eq_getElem?_getD]
  cases h : cs[i]? with
  | none => simp
  | some c => simp; exact hcs c (List.mem_of_getElem? h)

theorem getC_max (cs : List Circ) (m : Nat) (hcs : ∀ c ∈ cs, maxInput c ≤ m) (i : Nat) :
    maxInput (getC cs i) ≤ m := by
  unfold getC
  simp only [List.getD_eq_getElem?_getD]
  cases h : cs[i]? with
  | none => simp
  | some c => simp; exact hcs c (List.mem_of_getElem? h)

/-- DEPTH BOUND: HC has depth ≤ d + 11. -/
theorem HC_depth (hb : RBound R N B d s) (a : Nat) : depth (HC R N B a) ≤ d + 11 := by
  have hsel := getC_depth R.sel hb.depth_sel
  have hval := getC_depth R.val hb.depth_val
  have hselC : ∀ i, depth (selC R i) ≤ d + 2 := by
    intro i; unfold selC
    apply depth_and_le
    intro c hc
    simp only [List.mem_cons, List.mem_map, List.mem_range] at hc
    rcases hc with rfl | ⟨i', _, rfl⟩
    · have := hsel i; omega
    · simp; have := hsel i'; omega
  have heq : ∀ p' i, depth (eqC (valC R p') (heapC B i p')) ≤ d + 3 := by
    intro p' i; unfold eqC valC heapC
    apply depth_or_le; intro c hc
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc
    rcases hc with rfl | rfl <;> apply depth_and_le <;> intro c hc <;>
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc <;>
      rcases hc with rfl | rfl <;> (try simp) <;> have := hval p' <;> omega
  have hlt : ∀ i, depth (ltC R B i) ≤ d + 5 := by
    intro i; unfold ltC
    apply depth_or_le; intro c hc
    obtain ⟨p, _, rfl⟩ := List.mem_map.mp hc
    have : depth (and ([not (valC R p), heapC B i p] ++
        (List.range p).map (fun p' => eqC (valC R p') (heapC B i p')))) ≤ d + 4 := by
      apply depth_and_le; intro c hc
      simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false, List.mem_map] at hc
      rcases hc with (rfl | rfl) | ⟨p', _, rfl⟩
      · unfold valC; simp; have := hval p; omega
      · unfold heapC; simp
      · exact heq p' i
    omega
  have hlegal : depth (legalC R N B) ≤ d + 8 := by
    unfold legalC
    apply depth_and_le; intro c hc
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc
    rcases hc with rfl | rfl
    · have := hb.depth_valid; omega
    · apply depth_or_le; intro c hc
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp hc
      apply depth_and_le; intro c hc
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc
      rcases hc with rfl | rfl
      · have := hselC i; omega
      · exact hlt i
  have hgbit : ∀ p, depth (gbitC R N B p) ≤ d + 9 := by
    intro p; unfold gbitC
    apply depth_and_le; intro c hc
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc
    rcases hc with rfl | rfl
    · exact hlegal
    · apply depth_or_le; intro c hc
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp hc
      apply depth_and_le; intro c hc
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc
      rcases hc with rfl | rfl
      · have := hselC i; omega
      · unfold xor2 valC heapC
        apply depth_or_le; intro c hc
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc
        have hv := hval p
        rcases hc with rfl | rfl <;> apply depth_and_le <;> intro c hc <;>
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc <;>
          rcases hc with rfl | rfl <;> (try simp) <;> omega
  unfold HC
  apply depth_and_le; intro c hc
  obtain ⟨p, _, rfl⟩ := List.mem_map.mp hc
  split
  · have := hgbit p; omega
  · simp; have := hgbit p; omega

/-- SIZE BOUND: HC has size ≤ 12 U^10 with U = (N+2)(B+2)(s+2). -/
theorem HC_size (hb : RBound R N B d s) (a : Nat) : size (HC R N B a) ≤ 12 * Upar N B s ^ 10 := by
  obtain ⟨hU1, hUN, hUB, hUs⟩ := Upar_ge N B s
  generalize hUdef : Upar N B s = U at *
  have base : ∀ c, c = R.valid ∨ (∃ i, c = getC R.sel i) ∨ (∃ p, c = getC R.val p) ∨
      (∃ j, c = input j) → size c ≤ 1 * U ^ 1 := by
    intro c hc
    rcases hc with rfl | ⟨i, rfl⟩ | ⟨p, rfl⟩ | ⟨j, rfl⟩
    · simp; exact Nat.le_trans hb.size_valid hUs
    · have := getC_size hb R.sel hb.size_sel i; rw [hUdef] at this; exact this
    · have := getC_size hb R.val hb.size_val p; rw [hUdef] at this; exact this
    · simp; exact hU1
  have hselC : ∀ i, i < N → size (selC R i) ≤ 3 * U ^ 2 := by
    intro i hi; unfold selC
    apply size_and_le hU1 (by simp; omega)
    intro c hc
    simp only [List.mem_cons, List.mem_map, List.mem_range] at hc
    rcases hc with rfl | ⟨i', _, rfl⟩
    · exact size_lift hU1 (base _ (Or.inr (Or.inl ⟨i, rfl⟩))) (by omega) (Nat.le_refl _)
    · exact size_not_le hU1 (base _ (Or.inr (Or.inl ⟨i', rfl⟩)))
  have hvalU : ∀ p, size (valC R p) ≤ 1 * U ^ 1 := fun p => base _ (Or.inr (Or.inr (Or.inl ⟨p, rfl⟩)))
  have hheapU : ∀ i p, size (heapC B i p) ≤ 1 * U ^ 1 := fun i p =>
    base _ (Or.inr (Or.inr (Or.inr ⟨_, rfl⟩)))
  have hpair : ∀ x y : Circ, size x ≤ 1 * U ^ 1 → size y ≤ 1 * U ^ 1 →
      size (or [and [x, not y], and [not x, y]]) ≤ 4 * U ^ 3 ∧
      size (or [and [x, y], and [not x, not y]]) ≤ 4 * U ^ 3 := by
    intro x y hx hy
    have hnx := size_not_le hU1 hx
    have hny := size_not_le hU1 hy
    have l2 : (2 : Nat) ≤ U := by omega
    have a1 : size (and [x, not y]) ≤ 3 * U ^ 2 := by
      apply size_and_le hU1 (by simp; omega); intro c hc
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc
      rcases hc with rfl | rfl
      · exact size_lift hU1 hx (by omega) (Nat.le_refl _)
      · exact hny
    have a2 : size (and [not x, y]) ≤ 3 * U ^ 2 := by
      apply size_and_le hU1 (by simp; omega); intro c hc
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc
      rcases hc with rfl | rfl
      · exact hnx
      · exact size_lift hU1 hy (by omega) (Nat.le_refl _)
    have a3 : size (and [x, y]) ≤ 3 * U ^ 2 := by
      apply size_and_le hU1 (by simp; omega); intro c hc
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc
      rcases hc with rfl | rfl
      · exact size_lift hU1 hx (by omega) (Nat.le_refl _)
      · exact size_lift hU1 hy (by omega) (Nat.le_refl _)
    have a4 : size (and [not x, not y]) ≤ 3 * U ^ 2 := by
      apply size_and_le hU1 (by simp; omega); intro c hc
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc
      rcases hc with rfl | rfl
      · exact hnx
      · exact hny
    constructor
    · apply size_or_le hU1 (by simp; omega); intro c hc
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc
      rcases hc with rfl | rfl
      · exact a1
      · exact a2
    · apply size_or_le hU1 (by simp; omega); intro c hc
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc
      rcases hc with rfl | rfl
      · exact a3
      · exact a4
  have hlt : ∀ i, size (ltC R B i) ≤ 6 * U ^ 5 := by
    intro i; unfold ltC
    apply size_or_le hU1 (by simp; omega); intro c hc
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hc
    have hp' := List.mem_range.mp hp
    apply size_and_le hU1 (by simp; omega); intro c hc
    simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false, List.mem_map] at hc
    rcases hc with (rfl | rfl) | ⟨p', _, rfl⟩
    · exact size_lift hU1 (size_not_le hU1 (hvalU p)) (by omega) (by omega)
    · exact size_lift hU1 (hheapU i p) (by omega) (by omega)
    · exact (hpair _ _ (hvalU p') (hheapU i p')).2
  have hlegal : size (legalC R N B) ≤ 9 * U ^ 8 := by
    unfold legalC
    apply size_and_le hU1 (by simp; omega); intro c hc
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc
    rcases hc with rfl | rfl
    · exact size_lift hU1 (base _ (Or.inl rfl)) (by omega) (by omega)
    · apply size_or_le hU1 (by simp; omega); intro c hc
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hc
      apply size_and_le hU1 (by simp; omega); intro c hc
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc
      rcases hc with rfl | rfl
      · exact size_lift hU1 (hselC i (List.mem_range.mp hi)) (by omega) (by omega)
      · exact hlt i
  have hgbit : ∀ p, size (gbitC R N B p) ≤ 10 * U ^ 9 := by
    intro p; unfold gbitC
    apply size_and_le hU1 (by simp; omega); intro c hc
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc
    rcases hc with rfl | rfl
    · exact hlegal
    · have : size (or ((List.range N).map (fun i => and [selC R i, xor2 (valC R p) (heapC B i p)]))) ≤
          6 * U ^ 5 := by
        apply size_or_le hU1 (by simp; omega); intro c hc
        obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hc
        apply size_and_le hU1 (by simp; omega); intro c hc
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc
        rcases hc with rfl | rfl
        · exact size_lift hU1 (hselC i (List.mem_range.mp hi)) (by omega) (by omega)
        · exact (hpair _ _ (hvalU p) (hheapU i p)).1
      exact size_lift hU1 this (by omega) (by omega)
  unfold HC
  apply size_and_le hU1 (by simp; omega); intro c hc
  obtain ⟨p, _, rfl⟩ := List.mem_map.mp hc
  split
  · exact size_lift hU1 (hgbit p) (by omega) (Nat.le_refl _)
  · exact size_not_le hU1 (hgbit p)

/-- HC reads only the N·B board bits. -/
theorem HC_max (hb : RBound R N B d s) (a : Nat) : maxInput (HC R N B a) ≤ B * N := by
  have hheap : ∀ i p, i < N → p < B → maxInput (heapC B i p) ≤ B * N := by
    intro i p hi hp
    unfold heapC; simp
    have := Nat.mul_le_mul_left B (show i + 1 ≤ N by omega)
    rw [Nat.mul_succ] at this; omega
  have hsel := getC_max R.sel (B * N) hb.max_sel
  have hval := getC_max R.val (B * N) hb.max_val
  have and_max : ∀ cs : List Circ, (∀ c ∈ cs, maxInput c ≤ B * N) → maxInput (and cs) ≤ B * N := by
    intro cs h; simp only [maxInput_and]; apply listMax_le; intro a ha
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ha; exact h c hc
  have or_max : ∀ cs : List Circ, (∀ c ∈ cs, maxInput c ≤ B * N) → maxInput (or cs) ≤ B * N := by
    intro cs h; simp only [maxInput_or]; apply listMax_le; intro a ha
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ha; exact h c hc
  have hselC : ∀ i, maxInput (selC R i) ≤ B * N := by
    intro i; unfold selC; apply and_max; intro c hc
    simp only [List.mem_cons, List.mem_map, List.mem_range] at hc
    rcases hc with rfl | ⟨i', _, rfl⟩
    · exact hsel i
    · simp; exact hsel i'
  have hpair : ∀ x y : Circ, maxInput x ≤ B * N → maxInput y ≤ B * N →
      maxInput (or [and [x, not y], and [not x, y]]) ≤ B * N ∧
      maxInput (or [and [x, y], and [not x, not y]]) ≤ B * N := by
    intro x y hx hy
    constructor <;> apply or_max <;> intro c hc <;>
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc <;>
      rcases hc with rfl | rfl <;> apply and_max <;> intro c hc <;>
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc <;>
      rcases hc with rfl | rfl <;> (try simp only [maxInput_not]) <;> assumption
  have hlt : ∀ i, i < N → maxInput (ltC R B i) ≤ B * N := by
    intro i hi; unfold ltC; apply or_max; intro c hc
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hc
    have hp' := List.mem_range.mp hp
    apply and_max; intro c hc
    simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false, List.mem_map] at hc
    rcases hc with (rfl | rfl) | ⟨p', hp'', rfl⟩
    · simp; exact hval p
    · exact hheap i p hi hp'
    · exact (hpair _ _ (hval p') (hheap i p' hi (by have := List.mem_range.mp hp''; omega))).2
  have hlegal : maxInput (legalC R N B) ≤ B * N := by
    unfold legalC; apply and_max; intro c hc
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc
    rcases hc with rfl | rfl
    · exact hb.max_valid
    · apply or_max; intro c hc
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hc
      apply and_max; intro c hc
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc
      rcases hc with rfl | rfl
      · exact hselC i
      · exact hlt i (List.mem_range.mp hi)
  have hgbit : ∀ p, p < B → maxInput (gbitC R N B p) ≤ B * N := by
    intro p hp; unfold gbitC; apply and_max; intro c hc
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc
    rcases hc with rfl | rfl
    · exact hlegal
    · apply or_max; intro c hc
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hc
      apply and_max; intro c hc
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc
      rcases hc with rfl | rfl
      · exact hselC i
      · exact (hpair _ _ (hval p) (hheap i p (List.mem_range.mp hi) hp)).1
  unfold HC; apply and_max; intro c hc
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hc
  have := hgbit p (List.mem_range.mp hp)
  split
  · exact this
  · simp; exact this

end Bounds

/-! ## The conditional bridge to CorrHyp -/

/-- CONDITIONAL BRIDGE (paper Appendix G(i), circuit part).  Let the readout be
    given, for each observed bit b, by formulas R b with the resource bounds of
    `RBound` (depth ≤ d, size ≤ s, reading the N·B input bits).  ASSUME the
    classical parity-correlation premise for formulas of depth ≤ d + 11 and size
    ≤ 12 U^10 (U = (N+2)(B+2)(s+2)) on every m with N ≤ m ≤ B·N, with error ε.
    Then the phase-2 hypothesis CorrHyp B N (readoutOf B R) ε holds. -/
theorem corrHyp_of_premise {B N d s : Nat} (R : Bool → RCirc)
    (hb : ∀ b, RBound (R b) N B d s) {ε : Rat}
    (hprem : ∀ m, N ≤ m → m ≤ B * N → ParityCorrPremise (d + 11) (12 * Upar N B s ^ 10) m ε) :
    CorrHyp B N (readoutOf B R) ε := by
  intro b a u ha hu0 hu
  -- the mask for chi_u
  let mask := maskU B N u
  have hml : mask.length = B * N := length_maskU B N u
  have hones : N ≤ ones mask ∧ ones mask ≤ B * N := by
    have h1 := ones_maskU B N u
    have h2 := ones_toBitsBE_pos (by omega) hu
    have h3 : ones (toBitsBE B u) ≤ B := by
      have := ones_le_length (toBitsBE B u); rwa [length_toBitsBE] at this
    constructor
    · show N ≤ ones (maskU B N u)
      rw [h1]; have := Nat.mul_le_mul_left N h2; omega
    · show ones (maskU B N u) ≤ B * N
      rw [h1, Nat.mul_comm B N]; exact Nat.mul_le_mul_left N h3
  have hC := masked_correlation mask (HC (R b) N B a)
    (by rw [hml]; exact HC_max (hb b) a) (HC_depth (hb b) a) (HC_size (hb b) a)
    (hprem (ones mask) hones.1 hones.2)
  rw [hml] at hC
  -- identify the phase-2 correlation with the masked correlation
  have e : corr B N (readoutOf B R) b a u =
      rsum (bitvecs (B * N)) (fun x => ind (eval (vfun x) (HC (R b) N B a)) * sgn (pm mask x)) /
        (2 : Rat) ^ (B * N) := by
    unfold corr expect T
    rw [rsum_boards_bitvecs]
    have hT : ((2 ^ B : Nat) : Rat) ^ N = (2 : Rat) ^ (B * N) := by
      rw [← Rat.natCast_pow, ← Nat.pow_mul]; simp
    rw [hT]
    congr 1
    apply rsum_congr
    intro x hx
    have hw := decodeBoard_width hx
    have hl := length_decodeBoard B N x
    have hH : H (readoutOf B R) b a (decodeBoard B N x) = ind (eval (vfun x) (HC (R b) N B a)) := by
      unfold H ind
      rw [← boardBits_decode hx, HC_eval R b hl hw (hb b).sel_len (hb b).val_len ha]
      by_cases h : gval (readoutOf B R) b (decodeBoard B N x) = a <;> simp [h]
    have hchi : chi B u (nimSum (decodeBoard B N x)) = sgn (pm mask x) := by
      unfold chi sgn
      rw [chi_parity B N u hx]
    rw [hH, hchi]
  rw [e]
  exact hC

/-- Combined with phase 2: under the same premise, the circuit readout fed the
    executed outcome of head pi_j succeeds with conditional probability at most
    2/(2^B-1) + (2^B-1) ε. -/
theorem circuit_readout_bound {B N j d s : Nat} (hj : j < B) (R : Bool → RCirc)
    (hb : ∀ b, RBound (R b) (N + 1) B d s) {ε : Rat}
    (hprem : ∀ m, N + 1 ≤ m → m ≤ B * (N + 1) →
      ParityCorrPremise (d + 11) (12 * Upar (N + 1) B s ^ 10) m ε) :
    succCountRO B (N + 1) (readoutOf B R) j / nonzeroCount B (N + 1) ≤
      2 / (((2 ^ B : Nat) : Rat) - 1) + (((2 ^ B : Nat) : Rat) - 1) * ε :=
  structured_head_bound hj _ (corrHyp_of_premise R hb hprem)

#print axioms firstTrue_some_iff
#print axioms eval_getC
#print axioms eval_eqC
#print axioms eval_xor2
#print axioms boardBits_heap
#print axioms selC_eval
#print axioms val_eval
#print axioms lt_iff_top
#print axioms ltC_eval
#print axioms gval_readoutOf
#print axioms legalC_eval
#print axioms gval_legal
#print axioms gval_illegal
#print axioms gbitC_eval
#print axioms gval_lt
#print axioms HC_eval
#print axioms getD_take_drop
#print axioms decodeBoard_getD
#print axioms boardBits_decode
#print axioms depth_and_le
#print axioms depth_or_le
#print axioms sum_le_len_mul
#print axioms upow_pos
#print axioms size_and_le
#print axioms size_or_le
#print axioms size_lift
#print axioms size_not_le
#print axioms Upar_ge
#print axioms getC_size
#print axioms getC_depth
#print axioms getC_max
#print axioms HC_depth
#print axioms HC_size
#print axioms HC_max
#print axioms corrHyp_of_premise
#print axioms circuit_readout_bound

end CorrBridge
end NimAudit
