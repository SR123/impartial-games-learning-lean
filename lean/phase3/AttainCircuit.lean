import NimCorrBridge
import NimAttain

/- Phase 3, targets A + D: an explicit circuit realisation of the attainability
   readout, and the resulting CONDITIONAL sharpness.  Written by Claude
   (10 October 2026).  Lean 4.26.0, core/Std only.

   For a nonzero guess t < 2^B with top bit k = log2 t:
     cancel test   x XOR t < x  ⟺  bit k of x        (one input literal)
     nonzero test  x ≠ 0        ⟺  OR of the B bits of x
     decrement     bit k' of x-1 = bit k' of x XOR (all lower bits of x are 0)
   The selection formulas choose the first cancelling heap if one exists, else the
   first nonzero heap; the value formulas output x XOR t or x - 1 accordingly.
   We prove that `readoutOf` of these formulas equals `attainF` on every board, and
   bound depth and size.  With the phase-3 exactness theorem and the conditional
   bridge this gives: UNDER THE PARITY-CORRELATION PREMISE, the class of readouts
   with these resource bounds has optimal conditional success in
   [2/(q-1), 2/(q-1) + (q-1) ε]. -/

namespace NimAudit
namespace AttainCircuit

open Prob AC0 AC0.Circ Game Bridge Rollout Attain CorrBridge

attribute [local simp] Rat.add_zero Rat.zero_add

/-! ## Arithmetic facts -/

/-- x XOR t < x iff x has t's top bit (t ≠ 0). -/
theorem cancel_iff_bit {x t : Nat} (ht : t ≠ 0) : x ^^^ t < x ↔ x.testBit t.log2 = true := by
  have htk : t.testBit t.log2 = true := by
    cases hb : t.testBit t.log2 with
    | true => rfl
    | false =>
      exfalso
      have hlt : t < 2 ^ t.log2 := by
        apply Nat.lt_pow_two_of_testBit
        intro i hi
        by_cases hik : i = t.log2
        · subst hik; exact hb
        · exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le Nat.lt_log2_self
            (Nat.pow_le_pow_right (by decide) (by omega)))
      exact absurd (Nat.log2_self_le ht) (Nat.not_le.mpr hlt)
  have habove : ∀ i, t.log2 < i → t.testBit i = false := fun i hi =>
    Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le Nat.lt_log2_self
      (Nat.pow_le_pow_right (by decide) (by omega)))
  constructor
  · intro hlt
    cases hx : x.testBit t.log2 with
    | true => rfl
    | false =>
      exfalso
      have : x < x ^^^ t := by
        apply lt_of_top_testBit (k := t.log2) hx
        · rw [Nat.testBit_xor, hx, htk]; rfl
        · intro i hi; rw [Nat.testBit_xor, habove i hi, Bool.xor_false]
      omega
  · intro hx
    apply lt_of_top_testBit (k := t.log2)
    · rw [Nat.testBit_xor, hx, htk]; rfl
    · exact hx
    · intro i hi; rw [Nat.testBit_xor, habove i hi, Bool.xor_false]

/-- Bits of x - 1 (x > 0). -/
theorem testBit_pred (x : Nat) (hx : 0 < x) (k : Nat) :
    (x - 1).testBit k = xor (x.testBit k) (decide (∀ j < k, x.testBit j = false)) := by
  induction x using Nat.strongRecOn generalizing k with
  | ind x ih =>
    rcases Nat.mod_two_eq_zero_or_one x with hev | hod
    · have hy : 0 < x / 2 := by omega
      cases k with
      | zero =>
        simp only [Nat.testBit_zero]
        have : (x - 1) % 2 = 1 := by omega
        simp [hev, this]
      | succ k =>
        rw [← Nat.testBit_div_two (x - 1) k, ← Nat.testBit_div_two x k,
          show (x - 1) / 2 = x / 2 - 1 by omega, ih (x / 2) (by omega) hy k]
        congr 1
        apply Bool.eq_iff_iff.mpr
        simp only [decide_eq_true_iff]
        constructor
        · intro h j hj
          cases j with
          | zero => simp [Nat.testBit_zero, hev]
          | succ j => rw [← Nat.testBit_div_two]; exact h j (by omega)
        · intro h j hj
          rw [Nat.testBit_div_two]; exact h (j + 1) (by omega)
    · cases k with
      | zero =>
        simp only [Nat.testBit_zero]
        have : (x - 1) % 2 = 0 := by omega
        simp [hod, this]
      | succ k =>
        rw [← Nat.testBit_div_two (x - 1) k, ← Nat.testBit_div_two x k,
          show (x - 1) / 2 = x / 2 by omega]
        have : ¬ ∀ j < k + 1, x.testBit j = false := by
          intro h; have := h 0 (by omega); simp [Nat.testBit_zero, hod] at this
        simp [this]

theorem pos_iff_bit {x B : Nat} (hx : x < 2 ^ B) :
    0 < x ↔ ∃ p < B, x.testBit (B - 1 - p) = true := by
  constructor
  · intro h
    obtain ⟨i, hi⟩ := Nat.exists_testBit_of_ne_zero (Nat.pos_iff_ne_zero.mp h)
    have hiB : i < B := by
      rcases Nat.lt_or_ge i B with h' | h'
      · exact h'
      · rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) h'))] at hi
        cases hi
    exact ⟨B - 1 - i, by omega, by rwa [show B - 1 - (B - 1 - i) = i by omega]⟩
  · rintro ⟨p, _, hp⟩
    rcases Nat.eq_zero_or_pos x with h | h
    · subst h; simp at hp
    · exact h

/-! ## Readout indices via firstTrue -/

theorem cancelIdx_firstTrue (t : Nat) : ∀ P : List Nat,
    cancelIdx t P = (firstTrue (P.map (fun x => decide (x ^^^ t < x)))).map
      (fun i => (i, P.getD i 0 ^^^ t))
  | [] => rfl
  | x :: P => by
    simp only [cancelIdx, List.map_cons]
    by_cases hx : x ^^^ t < x
    · simp [hx, firstTrue]
    · simp only [hx, if_false, decide_false, firstTrue]
      rw [cancelIdx_firstTrue t P]
      cases firstTrue (P.map (fun x => decide (x ^^^ t < x))) <;> simp

theorem decIdx_firstTrue : ∀ P : List Nat,
    decIdx P = (firstTrue (P.map (fun x => decide (0 < x)))).map (fun i => (i, P.getD i 0 - 1))
  | [] => rfl
  | x :: P => by
    simp only [decIdx, List.map_cons]
    by_cases hx : 0 < x
    · simp [hx, firstTrue]
    · simp only [hx, if_false, decide_false, firstTrue]
      rw [decIdx_firstTrue P]
      cases firstTrue (P.map (fun x => decide (0 < x))) <;> simp

theorem range_map_getD {α : Type} (f : Nat → α) : ∀ P : List Nat,
    (List.range P.length).map (fun i => f (P.getD i 0)) = P.map f
  | [] => rfl
  | x :: P => by
    rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map]
    simp only [List.getD_cons_zero, List.map_cons]
    congr 1
    rw [← range_map_getD f P]
    apply List.map_congr_left
    intro i _
    simp

theorem firstTrue_or (N : Nat) (c n : Nat → Bool) :
    firstTrue ((List.range N).map (fun i => c i || (!((List.range N).any c) && n i))) =
      if (List.range N).any c then firstTrue ((List.range N).map c)
      else firstTrue ((List.range N).map n) := by
  by_cases h : (List.range N).any c = true
  · simp only [h, Bool.not_true, Bool.false_and, Bool.or_false, if_true]
  · simp only [h, Bool.not_false, Bool.true_and, Bool.false_eq_true, if_false]
    congr 1
    apply List.map_congr_left
    intro i hi
    have : c i = false := by
      cases hc : c i
      · rfl
      · exact absurd (List.any_eq_true.mpr ⟨i, hi, hc⟩) h
    simp [this]

theorem firstTrue_lt {l : List Bool} {i : Nat} (h : firstTrue l = some i) : i < l.length :=
  ((firstTrue_some_iff l i).1 h).1

/-! ## The circuits -/

def cancelC (B k i : Nat) : Circ := input (B * i + (B - 1 - k))
def nzC (B i : Nat) : Circ := or ((List.range B).map (fun p => input (B * i + p)))
def anyC (B N k : Nat) : Circ := or ((List.range N).map (cancelC B k))
def selA (B N k i : Nat) : Circ := or [cancelC B k i, and [not (anyC B N k), nzC B i]]

/-- "i is the first index (below i) with cs true". -/
def firstC (cs : Nat → Circ) (i : Nat) : Circ :=
  and (cs i :: (List.range i).map (fun i' => not (cs i')))

def xbitC (B t i p : Nat) : Circ :=
  if t.testBit (B - 1 - p) then not (input (B * i + p)) else input (B * i + p)

/-- All bits of heap i strictly below big-endian position p are zero. -/
def lowZeroC (B i p : Nat) : Circ :=
  and ((List.range (B - 1 - p)).map (fun r => not (input (B * i + (p + 1 + r)))))

def decbitC (B i p : Nat) : Circ := xor2 (input (B * i + p)) (lowZeroC B i p)

def valA (B N t k p : Nat) : Circ :=
  or [and [anyC B N k, or ((List.range N).map (fun i => and [firstC (cancelC B k) i, xbitC B t i p]))],
      and [not (anyC B N k), or ((List.range N).map (fun i => and [firstC (nzC B) i, decbitC B i p]))]]

def validA (B N : Nat) : Circ := or ((List.range N).map (nzC B))

/-- The attainability readout for a single guess t (as in `attainF`). -/
def attainT (t : Nat) (P : List Nat) : Option (Nat × Nat) :=
  match cancelIdx t P with
  | some m => some m
  | none => decIdx P

theorem attainF_eq (a0 a1 : Nat) (P : List Nat) (b : Bool) :
    attainF a0 a1 P b = attainT (if b then a1 else a0) P := rfl

/-- The readout circuits for guess t. -/
def attRC (B N t : Nat) : RCirc :=
  ⟨validA B N, (List.range N).map (selA B N t.log2), (List.range B).map (valA B N t t.log2)⟩

/-- The two-guess circuit readout. -/
def attR (B N a0 a1 : Nat) : Bool → RCirc := fun b => attRC B N (if b then a1 else a0)

/-! ## Semantics -/

section Sem

variable {B N : Nat} {P : List Nat}

theorem firstC_eval (z : Nat → Bool) (cs : Nat → Circ) {i : Nat} (hi : i < N) :
    eval z (firstC cs i) = decide (firstTrue ((List.range N).map (fun i => eval z (cs i))) = some i) := by
  unfold firstC
  rw [Bool.eq_iff_iff, decide_eq_true_iff, firstTrue_some_iff]
  simp only [eval_and, List.all_cons, List.all_map, Bool.and_eq_true, List.all_eq_true,
    List.mem_range, Function.comp, eval_not, Bool.not_eq_true', List.length_map, List.length_range]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨hi, by simpa using h1, ?_⟩
    intro i' hi'
    rw [List.getElem?_range (by omega)]; simpa using h2 i' hi'
  · rintro ⟨_, h1, h2⟩
    refine ⟨by simpa using h1, ?_⟩
    intro i' hi'
    have := h2 i' hi'
    rw [List.getElem?_range (by omega)] at this; simpa using this

theorem cancel_eval (hP : P.length = N) {t : Nat} (ht : t < 2 ^ B) (ht0 : t ≠ 0) {i : Nat} (hi : i < N) :
    eval (boardBits B P) (cancelC B t.log2 i) = decide (P.getD i 0 ^^^ t < P.getD i 0) := by
  have hk : t.log2 < B := by
    rcases Nat.lt_or_ge t.log2 B with h | h
    · exact h
    · exfalso
      exact absurd (Nat.lt_of_lt_of_le ht (Nat.pow_le_pow_right (by decide) h))
        (Nat.not_lt.mpr (Nat.log2_self_le ht0))
  unfold cancelC
  rw [eval_input, boardBits_heap hP hi (by omega), show B - 1 - (B - 1 - t.log2) = t.log2 by omega]
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_iff, cancel_iff_bit ht0]

theorem nz_eval (hP : P.length = N) (hw : Width B P) {i : Nat} (hi : i < N) :
    eval (boardBits B P) (nzC B i) = decide (0 < P.getD i 0) := by
  have hx : P.getD i 0 < 2 ^ B := by
    apply hw; simp only [List.getD_eq_getElem?_getD]; rw [List.getElem?_eq_getElem (by omega)]; simp
  unfold nzC
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_iff, pos_iff_bit hx]
  simp only [eval_or, List.any_map, List.any_eq_true, List.mem_range, Function.comp, eval_input]
  constructor
  · rintro ⟨p, hp, h⟩; rw [boardBits_heap hP hi hp] at h; exact ⟨p, hp, h⟩
  · rintro ⟨p, hp, h⟩; exact ⟨p, hp, by rw [boardBits_heap hP hi hp]; exact h⟩

theorem toNatBE_of_bits {h : Nat} (hh : h < 2 ^ B) (f : Nat → Bool)
    (hf : ∀ p < B, f p = h.testBit (B - 1 - p)) : toNatBE ((List.range B).map f) = h := by
  apply Nat.eq_of_testBit_eq
  intro k
  have hlen : ((List.range B).map f).length = B := by simp
  rcases Nat.lt_or_ge k B with hk | hk
  · have := testBit_toNatBE ((List.range B).map f) (B - 1 - k) (by rw [hlen]; omega)
    rw [hlen, show B - 1 - (B - 1 - k) = k by omega] at this
    rw [this]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (show B - 1 - k < B by omega),
      Option.map_some, Option.getD_some]
    rw [hf _ (by omega), show B - 1 - (B - 1 - k) = k by omega]
  · have h1 := toNatBE_lt ((List.range B).map f)
    rw [hlen] at h1
    rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by decide) hk)),
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hh (Nat.pow_le_pow_right (by decide) hk))]

/-- CIRCUIT REALISATION IS EXACT: the circuit readout equals the attainability
    readout `attainF` on every board of N heaps below 2^B (nonzero guesses). -/
theorem attR_correct {a0 a1 : Nat} (h0 : a0 ≠ 0) (h1 : a1 ≠ 0) (hl0 : a0 < 2 ^ B) (hl1 : a1 < 2 ^ B)
    (hP : P.length = N) (hw : Width B P) (b : Bool) :
    readoutOf B (attR B N a0 a1) P b = attainF a0 a1 P b := by
  generalize ht : (if b then a1 else a0) = t
  have ht0 : t ≠ 0 := by rw [← ht]; cases b <;> simp [h0, h1]
  have htl : t < 2 ^ B := by rw [← ht]; cases b <;> simp [hl0, hl1]
  have hRb : attR B N a0 a1 b = attRC B N t := by unfold attR; rw [ht]
  rw [attainF_eq, ht]
  unfold readoutOf attainT
  rw [hRb]
  generalize hz : boardBits B P = z
  -- evaluated tests as lists over heaps
  have hcan : (List.range N).map (fun i => eval z (cancelC B t.log2 i)) =
      P.map (fun x => decide (x ^^^ t < x)) := by
    have hrm := range_map_getD (fun x => decide (x ^^^ t < x)) P
    rw [← hrm, hP]
    apply List.map_congr_left; intro i hi
    rw [← hz, cancel_eval hP htl ht0 (List.mem_range.mp hi)]
  have hnz : (List.range N).map (fun i => eval z (nzC B i)) = P.map (fun x => decide (0 < x)) := by
    have hrm := range_map_getD (fun x => decide (0 < x)) P
    rw [← hrm, hP]
    apply List.map_congr_left; intro i hi
    rw [← hz, nz_eval hP hw (List.mem_range.mp hi)]
  have hany : eval z (anyC B N t.log2) = (List.range N).any (fun i => eval z (cancelC B t.log2 i)) := by
    unfold anyC; rw [eval_or, List.any_map]; rfl
  have hsel : ((attRC B N t).sel.map (eval z)) =
      (List.range N).map (fun i => eval z (cancelC B t.log2 i) ||
        (!((List.range N).any (fun i => eval z (cancelC B t.log2 i))) && eval z (nzC B i))) := by
    unfold attRC
    rw [List.map_map]
    apply List.map_congr_left; intro i _
    simp only [Function.comp, selA, eval_or, eval_and, eval_not, List.any_cons, List.any_nil,
      List.all_cons, List.all_nil, Bool.or_false, Bool.and_true, hany]
  have hvalid : eval z (attRC B N t).valid = (List.range N).any (fun i => eval z (nzC B i)) := by
    unfold attRC validA; rw [eval_or, List.any_map]; rfl
  rw [hsel, firstTrue_or, hvalid]
  rw [cancelIdx_firstTrue, decIdx_firstTrue]
  have hanyP : (List.range N).any (fun i => eval z (cancelC B t.log2 i)) =
      (P.map (fun x => decide (x ^^^ t < x))).any id := by
    rw [← hcan]; simp [List.any_map, Function.comp]
  by_cases hA : (List.range N).any (fun i => eval z (cancelC B t.log2 i)) = true
  · -- a cancelling heap exists
    simp only [hA, if_true]
    rw [hcan]
    obtain ⟨i, hi⟩ : ∃ i, firstTrue (P.map (fun x => decide (x ^^^ t < x))) = some i := by
      rw [hanyP] at hA
      cases hf : firstTrue (P.map (fun x => decide (x ^^^ t < x))) with
      | some i => exact ⟨i, rfl⟩
      | none =>
        exfalso
        obtain ⟨y, hy, hyb⟩ := List.any_eq_true.mp hA
        have key : ∀ l : List Bool, firstTrue l = none → ∀ y ∈ l, y = false := by
          intro l; induction l with
          | nil => simp
          | cons c l ihl =>
            cases c
            · intro h y hy
              simp only [firstTrue] at h
              rcases List.mem_cons.mp hy with rfl | hy
              · rfl
              · exact ihl (by cases hfl : firstTrue l <;> simp_all) y hy
            · intro h; simp [firstTrue] at h
        have := key _ hf y hy; simp at hyb; rw [this] at hyb; cases hyb
    have hiN : i < N := by have := firstTrue_lt hi; rw [List.length_map, hP] at this; exact this
    obtain ⟨_, hbit, _⟩ := (firstTrue_some_iff _ i).1 hi
    have hPi : P.getD i 0 ^^^ t < P.getD i 0 := by
      simp only [List.getD_eq_getElem?_getD, List.getElem?_map] at hbit
      rw [List.getElem?_eq_getElem (by omega)] at hbit
      simp only [Option.map_some, Option.getD_some, decide_eq_true_eq] at hbit
      simp only [List.getD_eq_getElem?_getD]; rw [List.getElem?_eq_getElem (by omega)]; simpa using hbit
    have hvalidT : (List.range N).any (fun i => eval z (nzC B i)) = true := by
      apply List.any_eq_true.mpr
      refine ⟨i, List.mem_range.mpr hiN, ?_⟩
      rw [← hz, nz_eval hP hw hiN, decide_eq_true_iff]; omega
    simp only [hvalidT, if_true, hi, Option.map_some]
    congr 2
    -- the value bits give P_i XOR t
    unfold attRC
    simp only [List.map_map]
    apply toNatBE_of_bits (Nat.xor_lt_two_pow (hw _ (by
      simp only [List.getD_eq_getElem?_getD]; rw [List.getElem?_eq_getElem (by omega)]; simp)) htl)
    intro p hp
    simp only [Function.comp, valA, eval_or, eval_and, eval_not, List.any_cons, List.any_nil,
      List.all_cons, List.all_nil, Bool.and_true, Bool.or_false, hany, hA, Bool.not_true,
      Bool.false_and, Bool.true_and]
    apply Bool.eq_iff_iff.mpr
    simp only [List.any_map, List.any_eq_true, List.mem_range, Function.comp, eval_and,
      List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
    rw [Nat.testBit_xor]
    have hfc : ∀ i', i' < N → (eval z (firstC (cancelC B t.log2) i') = true ↔ i' = i) := by
      intro i' hi'
      rw [← hz, firstC_eval _ _ hi', hz, hcan, decide_eq_true_iff, hi]
      constructor
      · intro h; cases h; rfl
      · intro h; rw [h]
    have hxb : ∀ i', i' < N → eval z (xbitC B t i' p) =
        xor ((P.getD i' 0).testBit (B - 1 - p)) (t.testBit (B - 1 - p)) := by
      intro i' hi'
      unfold xbitC
      rw [← hz]
      split
      · next htb =>
        rw [eval_not, eval_input, boardBits_heap hP hi' hp, htb]
        cases (P.getD i' 0).testBit (B - 1 - p) <;> rfl
      · next htb =>
        rw [eval_input, boardBits_heap hP hi' hp]
        have : t.testBit (B - 1 - p) = false := by simpa using htb
        rw [this, Bool.xor_false]
    constructor
    · rintro ⟨i', hi', hf', hx⟩
      rw [(hfc i' hi').1 hf'] at hx
      rw [hxb i hiN] at hx; exact hx
    · intro hx
      exact ⟨i, hiN, (hfc i hiN).2 rfl, by rw [hxb i hiN]; exact hx⟩
  · -- no cancelling heap
    simp only [hA, Bool.false_eq_true, if_false]
    rw [hnz]
    have hcnone : firstTrue (P.map (fun x => decide (x ^^^ t < x))) = none := by
      cases hf : firstTrue (P.map (fun x => decide (x ^^^ t < x))) with
      | none => rfl
      | some i =>
        exfalso; apply hA
        rw [hanyP]
        obtain ⟨hl, hb, _⟩ := (firstTrue_some_iff _ i).1 hf
        apply List.any_eq_true.mpr
        refine ⟨true, ?_, rfl⟩
        simp only [List.getD_eq_getElem?_getD] at hb
        rw [List.getElem?_eq_getElem hl] at hb
        simp at hb
        exact List.mem_iff_getElem.mpr ⟨i, hl, by simpa using hb⟩
    simp only [hcnone, Option.map_none]
    by_cases hV : (List.range N).any (fun i => eval z (nzC B i)) = true
    · simp only [hV, if_true]
      obtain ⟨i, hi⟩ : ∃ i, firstTrue (P.map (fun x => decide (0 < x))) = some i := by
        rw [← hnz]
        cases hf : firstTrue ((List.range N).map (fun i => eval z (nzC B i))) with
        | some i => exact ⟨i, rfl⟩
        | none =>
          exfalso
          obtain ⟨j, hj, hjb⟩ := List.any_eq_true.mp hV
          have key : ∀ l : List Bool, firstTrue l = none → ∀ y ∈ l, y = false := by
            intro l; induction l with
            | nil => simp
            | cons c l ihl =>
              cases c
              · intro h y hy
                simp only [firstTrue] at h
                rcases List.mem_cons.mp hy with rfl | hy
                · rfl
                · exact ihl (by cases hfl : firstTrue l <;> simp_all) y hy
              · intro h; simp [firstTrue] at h
          have := key _ hf (eval z (nzC B j)) (List.mem_map.mpr ⟨j, hj, rfl⟩)
          rw [this] at hjb; cases hjb
      have hiN : i < N := by have := firstTrue_lt hi; rw [List.length_map, hP] at this; exact this
      obtain ⟨_, hbit, _⟩ := (firstTrue_some_iff _ i).1 hi
      have hpos : 0 < P.getD i 0 := by
        simp only [List.getD_eq_getElem?_getD, List.getElem?_map] at hbit
        rw [List.getElem?_eq_getElem (by omega)] at hbit
        simp only [Option.map_some, Option.getD_some, decide_eq_true_eq] at hbit
        simp only [List.getD_eq_getElem?_getD]; rw [List.getElem?_eq_getElem (by omega)]; simpa using hbit
      simp only [hi, Option.map_some]
      congr 2
      unfold attRC
      simp only [List.map_map]
      have hxlt : P.getD i 0 < 2 ^ B := hw _ (by
        simp only [List.getD_eq_getElem?_getD]; rw [List.getElem?_eq_getElem (by omega)]; simp)
      apply toNatBE_of_bits (Nat.lt_of_le_of_lt (Nat.sub_le _ _) hxlt)
      intro p hp
      simp only [Function.comp, valA, eval_or, eval_and, eval_not, List.any_cons, List.any_nil,
        List.all_cons, List.all_nil, Bool.and_true, Bool.or_false, hany, hA, Bool.not_false,
        Bool.false_and, Bool.true_and, Bool.false_or]
      apply Bool.eq_iff_iff.mpr
      simp only [List.any_map, List.any_eq_true, List.mem_range, Function.comp, eval_and,
        List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
      rw [testBit_pred _ hpos]
      have hfn : ∀ i', i' < N → (eval z (firstC (nzC B) i') = true ↔ i' = i) := by
        intro i' hi'
        rw [← hz, firstC_eval _ _ hi', hz, hnz, decide_eq_true_iff, hi]
        constructor
        · intro h; cases h; rfl
        · intro h; rw [h]
      have hdb : ∀ i', i' < N → eval z (decbitC B i' p) =
          xor ((P.getD i' 0).testBit (B - 1 - p))
            (decide (∀ j < B - 1 - p, (P.getD i' 0).testBit j = false)) := by
        intro i' hi'
        unfold decbitC
        rw [eval_xor2, ← hz, eval_input, boardBits_heap hP hi' hp]
        congr 1
        unfold lowZeroC
        apply Bool.eq_iff_iff.mpr
        simp only [eval_and, List.all_map, List.all_eq_true, List.mem_range, Function.comp,
          eval_not, eval_input, Bool.not_eq_true', decide_eq_true_iff]
        constructor
        · intro h j hj
          have := h (B - 1 - p - 1 - j) (by omega)
          rw [boardBits_heap hP hi' (by omega)] at this
          rwa [show B - 1 - (p + 1 + (B - 1 - p - 1 - j)) = j by omega] at this
        · intro h r hr
          rw [boardBits_heap hP hi' (by omega)]
          exact h _ (by omega)
      constructor
      · rintro ⟨i', hi', hf', hx⟩
        rw [(hfn i' hi').1 hf'] at hx
        rw [hdb i hiN] at hx; exact hx
      · intro hx
        exact ⟨i, hiN, (hfn i hiN).2 rfl, by rw [hdb i hiN]; exact hx⟩
    · simp only [hV, Bool.false_eq_true, if_false]
      have hnone : firstTrue (P.map (fun x => decide (0 < x))) = none := by
        cases hf : firstTrue (P.map (fun x => decide (0 < x))) with
        | none => rfl
        | some i =>
          exfalso; apply hV
          obtain ⟨hl, hb, _⟩ := (firstTrue_some_iff _ i).1 hf
          have hiN : i < N := by rw [List.length_map, hP] at hl; exact hl
          apply List.any_eq_true.mpr
          refine ⟨i, List.mem_range.mpr hiN, ?_⟩
          rw [← hz, nz_eval hP hw hiN, decide_eq_true_iff]
          simp only [List.getD_eq_getElem?_getD, List.getElem?_map] at hb
          rw [List.getElem?_eq_getElem (by omega)] at hb
          simp only [Option.map_some, Option.getD_some, decide_eq_true_eq] at hb
          simp only [List.getD_eq_getElem?_getD]; rw [List.getElem?_eq_getElem (by omega)]; simpa using hb
      simp [hnone]

end Sem

/-- The success counts of the circuit readout and of `attainF` coincide. -/
theorem succCount_attR {B N w a0 a1 : Nat} (h0 : a0 ≠ 0) (h1 : a1 ≠ 0) (hl0 : a0 < 2 ^ B)
    (hl1 : a1 < 2 ^ B) :
    succCount B N (readoutOf B (attR B N a0 a1)) w = succCount B N (attainF a0 a1) w := by
  unfold succCount
  apply rsum_congr
  intro P hP
  obtain ⟨hlen, hw⟩ := mem_boards hP
  have : ∀ b, readoutOf B (attR B N a0 a1) P b = attainF a0 a1 P b :=
    fun b => attR_correct h0 h1 hl0 hl1 hlen hw b
  unfold successB
  rw [this]

/-! ## Resource bounds of the attainability circuits -/

/-- Size parameter for the attainability circuits. -/
def Ua (N B : Nat) : Nat := (N + 2) * (B + 2)

theorem Ua_ge (N B : Nat) : 1 ≤ Ua N B ∧ N + 2 ≤ Ua N B ∧ B + 2 ≤ Ua N B := by
  unfold Ua
  refine ⟨Nat.mul_pos (by omega) (by omega), ?_, ?_⟩
  · have := Nat.le_mul_of_pos_right (N + 2) (show 0 < B + 2 by omega); omega
  · have := Nat.le_mul_of_pos_left (B + 2) (show 0 < N + 2 by omega); omega

section ABounds

variable {B N t : Nat}

theorem mem_pair {x a b : Circ} (h : x ∈ [a, b]) : x = a ∨ x = b := by
  simpa using h

theorem attRC_depth_size (t p i : Nat) :
    depth (selA B N t.log2 i) ≤ 9 ∧ depth (valA B N t t.log2 p) ≤ 9 ∧ depth (validA B N) ≤ 9 ∧
    size (selA B N t.log2 i) ≤ 10 * Ua N B ^ 8 ∧ size (valA B N t t.log2 p) ≤ 10 * Ua N B ^ 8 ∧
    size (validA B N) ≤ 10 * Ua N B ^ 8 := by
  obtain ⟨hU, hUN, hUB⟩ := Ua_ge N B
  generalize Ua N B = U at *
  have sin : ∀ j, size (input j) ≤ 1 * U ^ 1 := fun j => by simp; omega
  -- basic blocks
  have hcan : ∀ i, size (cancelC B t.log2 i) ≤ 1 * U ^ 1 ∧ depth (cancelC B t.log2 i) ≤ 0 :=
    fun i => ⟨sin _, by simp [cancelC]⟩
  have hnz : ∀ i, size (nzC B i) ≤ 2 * U ^ 2 ∧ depth (nzC B i) ≤ 1 := by
    intro i; unfold nzC
    refine ⟨size_or_le hU (by simp; omega) ?_, depth_or_le ?_⟩
    · intro c hc; obtain ⟨p, _, rfl⟩ := List.mem_map.mp hc; exact sin _
    · intro c hc; obtain ⟨p, _, rfl⟩ := List.mem_map.mp hc; simp
  have hany : size (anyC B N t.log2) ≤ 2 * U ^ 2 ∧ depth (anyC B N t.log2) ≤ 1 := by
    unfold anyC
    refine ⟨size_or_le hU (by simp; omega) ?_, depth_or_le ?_⟩
    · intro c hc; obtain ⟨i, _, rfl⟩ := List.mem_map.mp hc; exact (hcan i).1
    · intro c hc; obtain ⟨i, _, rfl⟩ := List.mem_map.mp hc; exact (hcan i).2
  have hnany : size (not (anyC B N t.log2)) ≤ 3 * U ^ 2 ∧ depth (not (anyC B N t.log2)) ≤ 2 :=
    ⟨size_not_le hU hany.1, by simp; have := hany.2; omega⟩
  -- selA
  have hsel : size (selA B N t.log2 i) ≤ 5 * U ^ 4 ∧ depth (selA B N t.log2 i) ≤ 4 := by
    unfold selA
    have hand : size (and [not (anyC B N t.log2), nzC B i]) ≤ 4 * U ^ 3 ∧
        depth (and [not (anyC B N t.log2), nzC B i]) ≤ 3 := by
      refine ⟨size_and_le hU (by simp; omega) ?_, depth_and_le ?_⟩
      · intro c hc; rcases mem_pair hc with rfl | rfl
        · exact hnany.1
        · exact size_lift hU (hnz i).1 (by omega) (Nat.le_refl _)
      · intro c hc; rcases mem_pair hc with rfl | rfl
        · exact hnany.2
        · have := (hnz i).2; omega
    refine ⟨size_or_le hU (by simp; omega) ?_, depth_or_le ?_⟩
    · intro c hc; rcases mem_pair hc with rfl | rfl
      · exact size_lift hU (hcan i).1 (by omega) (by omega)
      · exact hand.1
    · intro c hc; rcases mem_pair hc with rfl | rfl
      · have := (hcan i).2; omega
      · exact hand.2
  -- firstC blocks
  have hfc : ∀ i', i' ≤ N → size (firstC (cancelC B t.log2) i') ≤ 3 * U ^ 2 ∧
      depth (firstC (cancelC B t.log2) i') ≤ 2 := by
    intro i' hi'; unfold firstC
    refine ⟨size_and_le hU (by simp; omega) ?_, depth_and_le ?_⟩
    · intro c hc
      simp only [List.mem_cons, List.mem_map] at hc
      rcases hc with rfl | ⟨i'', _, rfl⟩
      · exact size_lift hU (hcan i').1 (by omega) (Nat.le_refl _)
      · exact size_not_le hU (hcan i'').1
    · intro c hc
      simp only [List.mem_cons, List.mem_map] at hc
      rcases hc with rfl | ⟨i'', _, rfl⟩
      · have := (hcan i').2; omega
      · simp [cancelC]
  have hfn : ∀ i', i' ≤ N → size (firstC (nzC B) i') ≤ 4 * U ^ 3 ∧ depth (firstC (nzC B) i') ≤ 3 := by
    intro i' hi'; unfold firstC
    refine ⟨size_and_le hU (by simp; omega) ?_, depth_and_le ?_⟩
    · intro c hc
      simp only [List.mem_cons, List.mem_map] at hc
      rcases hc with rfl | ⟨i'', _, rfl⟩
      · exact size_lift hU (hnz i').1 (by omega) (Nat.le_refl _)
      · exact size_not_le hU (hnz i'').1
    · intro c hc
      simp only [List.mem_cons, List.mem_map] at hc
      rcases hc with rfl | ⟨i'', _, rfl⟩
      · have := (hnz i').2; omega
      · simp; have := (hnz i'').2; omega
  have hxb : ∀ i', size (xbitC B t i' p) ≤ 2 * U ^ 1 ∧ depth (xbitC B t i' p) ≤ 1 := by
    intro i'; unfold xbitC; split
    · exact ⟨size_not_le hU (sin _), by simp⟩
    · exact ⟨size_lift hU (sin _) (by omega) (Nat.le_refl _), by simp⟩
  have hlz : ∀ i', size (lowZeroC B i' p) ≤ 3 * U ^ 2 ∧ depth (lowZeroC B i' p) ≤ 2 := by
    intro i'; unfold lowZeroC
    refine ⟨size_and_le hU (by simp; omega) ?_, depth_and_le ?_⟩
    · intro c hc; obtain ⟨r, _, rfl⟩ := List.mem_map.mp hc; exact size_not_le hU (sin _)
    · intro c hc; obtain ⟨r, _, rfl⟩ := List.mem_map.mp hc; simp
  have hdb : ∀ i', size (decbitC B i' p) ≤ 6 * U ^ 4 ∧ depth (decbitC B i' p) ≤ 5 := by
    intro i'; unfold decbitC xor2
    have a1 : size (and [input (B * i' + p), not (lowZeroC B i' p)]) ≤ 5 * U ^ 3 ∧
        depth (and [input (B * i' + p), not (lowZeroC B i' p)]) ≤ 4 := by
      refine ⟨size_and_le hU (by simp; omega) ?_, depth_and_le ?_⟩
      · intro c hc; rcases mem_pair hc with rfl | rfl
        · exact size_lift hU (sin _) (by omega) (by omega)
        · exact size_not_le hU (hlz i').1
      · intro c hc; rcases mem_pair hc with rfl | rfl
        · simp
        · simp; have := (hlz i').2; omega
    have a2 : size (and [not (input (B * i' + p)), lowZeroC B i' p]) ≤ 4 * U ^ 3 ∧
        depth (and [not (input (B * i' + p)), lowZeroC B i' p]) ≤ 3 := by
      refine ⟨size_and_le hU (by simp; omega) ?_, depth_and_le ?_⟩
      · intro c hc; rcases mem_pair hc with rfl | rfl
        · exact size_lift hU (size_not_le hU (sin _)) (by omega) (by omega)
        · exact (hlz i').1
      · intro c hc; rcases mem_pair hc with rfl | rfl
        · simp
        · have := (hlz i').2; omega
    refine ⟨size_or_le hU (by simp; omega) ?_, depth_or_le ?_⟩
    · intro c hc; rcases mem_pair hc with rfl | rfl
      · exact a1.1
      · exact size_lift hU a2.1 (by omega) (Nat.le_refl _)
    · intro c hc; rcases mem_pair hc with rfl | rfl
      · exact a1.2
      · have := a2.2; omega
  -- valA
  have hval : size (valA B N t t.log2 p) ≤ 10 * U ^ 8 ∧ depth (valA B N t t.log2 p) ≤ 9 := by
    unfold valA
    have o1 : size (or ((List.range N).map (fun i => and [firstC (cancelC B t.log2) i, xbitC B t i p])))
        ≤ 5 * U ^ 4 ∧
        depth (or ((List.range N).map (fun i => and [firstC (cancelC B t.log2) i, xbitC B t i p]))) ≤ 4 := by
      refine ⟨size_or_le hU (by simp; omega) ?_, depth_or_le ?_⟩
      · intro c hc; obtain ⟨i', hi', rfl⟩ := List.mem_map.mp hc
        have hi'' := List.mem_range.mp hi'
        apply size_and_le hU (by simp; omega)
        intro c hc; rcases mem_pair hc with rfl | rfl
        · exact (hfc i' (by omega)).1
        · exact size_lift hU (hxb i').1 (by omega) (by omega)
      · intro c hc; obtain ⟨i', hi', rfl⟩ := List.mem_map.mp hc
        have hi'' := List.mem_range.mp hi'
        apply depth_and_le
        intro c hc; rcases mem_pair hc with rfl | rfl
        · exact (hfc i' (by omega)).2
        · have := (hxb i').2; omega
    have o2 : size (or ((List.range N).map (fun i => and [firstC (nzC B) i, decbitC B i p]))) ≤ 8 * U ^ 6 ∧
        depth (or ((List.range N).map (fun i => and [firstC (nzC B) i, decbitC B i p]))) ≤ 7 := by
      refine ⟨size_lift hU (size_or_le hU (by simp; omega) (a := 7) (k := 5) ?_) (by omega) (Nat.le_refl _),
        depth_or_le ?_⟩
      · intro c hc; obtain ⟨i', hi', rfl⟩ := List.mem_map.mp hc
        have hi'' := List.mem_range.mp hi'
        apply size_and_le hU (by simp; omega)
        intro c hc; rcases mem_pair hc with rfl | rfl
        · exact size_lift hU (hfn i' (by omega)).1 (by omega) (by omega)
        · exact (hdb i').1
      · intro c hc; obtain ⟨i', hi', rfl⟩ := List.mem_map.mp hc
        have hi'' := List.mem_range.mp hi'
        apply depth_and_le
        intro c hc; rcases mem_pair hc with rfl | rfl
        · have := (hfn i' (by omega)).2; omega
        · have := (hdb i').2; omega
    have b1 : size (and [anyC B N t.log2, or ((List.range N).map
        (fun i => and [firstC (cancelC B t.log2) i, xbitC B t i p]))]) ≤ 9 * U ^ 7 ∧
        depth (and [anyC B N t.log2, or ((List.range N).map
        (fun i => and [firstC (cancelC B t.log2) i, xbitC B t i p]))]) ≤ 8 := by
      refine ⟨size_lift hU (size_and_le hU (by simp; omega) (a := 5) (k := 4) ?_) (by omega) (by omega),
        depth_and_le ?_⟩
      · intro c hc; rcases mem_pair hc with rfl | rfl
        · exact size_lift hU hany.1 (by omega) (by omega)
        · exact o1.1
      · intro c hc; rcases mem_pair hc with rfl | rfl
        · have := hany.2; omega
        · have := o1.2; omega
    have b2 : size (and [not (anyC B N t.log2), or ((List.range N).map
        (fun i => and [firstC (nzC B) i, decbitC B i p]))]) ≤ 9 * U ^ 7 ∧
        depth (and [not (anyC B N t.log2), or ((List.range N).map
        (fun i => and [firstC (nzC B) i, decbitC B i p]))]) ≤ 8 := by
      refine ⟨size_and_le hU (by simp; omega) ?_, depth_and_le ?_⟩
      · intro c hc; rcases mem_pair hc with rfl | rfl
        · exact size_lift hU hnany.1 (by omega) (by omega)
        · exact o2.1
      · intro c hc; rcases mem_pair hc with rfl | rfl
        · have := hnany.2; omega
        · exact o2.2
    refine ⟨size_or_le hU (by simp; omega) ?_, depth_or_le ?_⟩
    · intro c hc; rcases mem_pair hc with rfl | rfl
      · exact b1.1
      · exact b2.1
    · intro c hc; rcases mem_pair hc with rfl | rfl
      · exact b1.2
      · exact b2.2
  have hvalid : size (validA B N) ≤ 3 * U ^ 3 ∧ depth (validA B N) ≤ 2 := by
    unfold validA
    refine ⟨size_or_le hU (by simp; omega) ?_, depth_or_le ?_⟩
    · intro c hc; obtain ⟨i', _, rfl⟩ := List.mem_map.mp hc; exact (hnz i').1
    · intro c hc; obtain ⟨i', _, rfl⟩ := List.mem_map.mp hc; exact (hnz i').2
  refine ⟨by have := hsel.2; omega, hval.2, by have := hvalid.2; omega,
    size_lift hU hsel.1 (by omega) (by omega), hval.1, size_lift hU hvalid.1 (by omega) (by omega)⟩

theorem and_max' {cs : List Circ} {m : Nat} (h : ∀ c ∈ cs, maxInput c ≤ m) : maxInput (and cs) ≤ m := by
  simp only [maxInput_and]; apply listMax_le; intro a ha
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ha; exact h c hc

theorem or_max' {cs : List Circ} {m : Nat} (h : ∀ c ∈ cs, maxInput c ≤ m) : maxInput (or cs) ≤ m := by
  simp only [maxInput_or]; apply listMax_le; intro a ha
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ha; exact h c hc

theorem in_max {i p : Nat} (hi : i < N) (hp : p < B) : maxInput (input (B * i + p)) ≤ B * N := by
  simp only [maxInput_input]
  have := Nat.mul_le_mul_left B (show i + 1 ≤ N by omega)
  rw [Nat.mul_succ] at this; omega

theorem attRC_max {k : Nat} (hk : k < B) (t : Nat) :
    (∀ i, i < N → maxInput (selA B N k i) ≤ B * N) ∧
    (∀ p, p < B → maxInput (valA B N t k p) ≤ B * N) ∧ maxInput (validA B N) ≤ B * N := by
  have hcan : ∀ i, i < N → maxInput (cancelC B k i) ≤ B * N := fun i hi => in_max hi (by omega)
  have hnz : ∀ i, i < N → maxInput (nzC B i) ≤ B * N := by
    intro i hi; unfold nzC; apply or_max'; intro c hc
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hc; exact in_max hi (List.mem_range.mp hp)
  have hany : maxInput (anyC B N k) ≤ B * N := by
    unfold anyC; apply or_max'; intro c hc
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hc; exact hcan i (List.mem_range.mp hi)
  refine ⟨?_, ?_, ?_⟩
  · intro i hi; unfold selA; apply or_max'; intro c hc; rcases mem_pair hc with rfl | rfl
    · exact hcan i hi
    · apply and_max'; intro c hc; rcases mem_pair hc with rfl | rfl
      · simp only [maxInput_not]; exact hany
      · exact hnz i hi
  · intro p hp; unfold valA; apply or_max'; intro c hc; rcases mem_pair hc with rfl | rfl
    · apply and_max'; intro c hc; rcases mem_pair hc with rfl | rfl
      · exact hany
      · apply or_max'; intro c hc
        obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hc
        have hi' := List.mem_range.mp hi
        apply and_max'; intro c hc; rcases mem_pair hc with rfl | rfl
        · unfold firstC; apply and_max'; intro c hc
          simp only [List.mem_cons, List.mem_map, List.mem_range] at hc
          rcases hc with rfl | ⟨i', hi'', rfl⟩
          · exact hcan i hi'
          · simp only [maxInput_not]; exact hcan i' (by omega)
        · unfold xbitC; split
          · simp only [maxInput_not]; exact in_max hi' hp
          · exact in_max hi' hp
    · apply and_max'; intro c hc; rcases mem_pair hc with rfl | rfl
      · simp only [maxInput_not]; exact hany
      · apply or_max'; intro c hc
        obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hc
        have hi' := List.mem_range.mp hi
        apply and_max'; intro c hc; rcases mem_pair hc with rfl | rfl
        · unfold firstC; apply and_max'; intro c hc
          simp only [List.mem_cons, List.mem_map, List.mem_range] at hc
          rcases hc with rfl | ⟨i', hi'', rfl⟩
          · exact hnz i hi'
          · simp only [maxInput_not]; exact hnz i' (by omega)
        · unfold decbitC xor2; apply or_max'; intro c hc; rcases mem_pair hc with rfl | rfl
          · apply and_max'; intro c hc; rcases mem_pair hc with rfl | rfl
            · exact in_max hi' hp
            · simp only [maxInput_not]; unfold lowZeroC; apply and_max'; intro c hc
              obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hc
              simp only [maxInput_not]; exact in_max hi' (by have := List.mem_range.mp hr; omega)
          · apply and_max'; intro c hc; rcases mem_pair hc with rfl | rfl
            · simp only [maxInput_not]; exact in_max hi' hp
            · unfold lowZeroC; apply and_max'; intro c hc
              obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hc
              simp only [maxInput_not]; exact in_max hi' (by have := List.mem_range.mp hr; omega)
  · unfold validA; apply or_max'; intro c hc
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hc; exact hnz i (List.mem_range.mp hi)

theorem log2_lt {t : Nat} (ht0 : t ≠ 0) (ht : t < 2 ^ B) : t.log2 < B := by
  rcases Nat.lt_or_ge t.log2 B with h | h
  · exact h
  · exact absurd (Nat.lt_of_lt_of_le ht (Nat.pow_le_pow_right (by decide) h))
      (Nat.not_lt.mpr (Nat.log2_self_le ht0))

/-- The attainability circuits satisfy the resource bounds: depth ≤ 9,
    size ≤ 10 ((N+2)(B+2))^8, reading only the N·B board bits. -/
theorem attRC_RBound {t : Nat} (ht0 : t ≠ 0) (ht : t < 2 ^ B) :
    RBound (attRC B N t) N B 9 (10 * Ua N B ^ 8) := by
  have hm := attRC_max (N := N) (log2_lt ht0 ht) t
  refine ⟨by simp [attRC], by simp [attRC], (attRC_depth_size (N := N) (B := B) t 0 0).2.2.1, ?_, ?_,
    (attRC_depth_size (N := N) (B := B) t 0 0).2.2.2.2.2, ?_, ?_, hm.2.2, ?_, ?_⟩
  · intro c hc; simp only [attRC, List.mem_map, List.mem_range] at hc
    obtain ⟨i, _, rfl⟩ := hc; exact (attRC_depth_size t 0 i).1
  · intro c hc; simp only [attRC, List.mem_map, List.mem_range] at hc
    obtain ⟨p, _, rfl⟩ := hc; exact (attRC_depth_size t p 0).2.1
  · intro c hc; simp only [attRC, List.mem_map, List.mem_range] at hc
    obtain ⟨i, _, rfl⟩ := hc; exact (attRC_depth_size t 0 i).2.2.2.1
  · intro c hc; simp only [attRC, List.mem_map, List.mem_range] at hc
    obtain ⟨p, _, rfl⟩ := hc; exact (attRC_depth_size t p 0).2.2.2.2.1
  · intro c hc; simp only [attRC, List.mem_map, List.mem_range] at hc
    obtain ⟨i, hi, rfl⟩ := hc; exact hm.1 i hi
  · intro c hc; simp only [attRC, List.mem_map, List.mem_range] at hc
    obtain ⟨p, hp, rfl⟩ := hc; exact hm.2.1 p hp

end ABounds

theorem RBound_mono {R : RCirc} {N B d s d' s' : Nat} (h : RBound R N B d s) (hd : d ≤ d')
    (hs : s ≤ s') : RBound R N B d' s' :=
  ⟨h.sel_len, h.val_len, Nat.le_trans h.depth_valid hd, fun c hc => Nat.le_trans (h.depth_sel c hc) hd,
    fun c hc => Nat.le_trans (h.depth_val c hc) hd, Nat.le_trans h.size_valid hs,
    fun c hc => Nat.le_trans (h.size_sel c hc) hs, fun c hc => Nat.le_trans (h.size_val c hc) hs,
    h.max_valid, h.max_sel, h.max_val⟩

/-- The premise forces ε ≥ 0 (use the constant-false formula). -/
theorem premise_nonneg {d s m : Nat} {ε : Rat} (hs : 1 ≤ s) (h : ParityCorrPremise d s m ε) :
    0 ≤ ε := by
  obtain ⟨k1, _⟩ := h (const false) (by simp) (by simp; omega) (by simp)
  have : rsum (bitvecs m) (fun y => ind (eval (vfun y) (const false)) * sgn (par y)) = 0 := by
    rw [rsum_congr (g := fun _ => (0 : Rat)) (by intro y _; simp [ind])]
    exact rsum_zero _
  rw [this] at k1
  have h0 : (0 : Rat) / (2 : Rat) ^ m = 0 := by grind
  rw [h0] at k1
  grind

/-- CONDITIONAL SHARPNESS (targets A + C + D combined).  Fix B ≥ 2, a structured
    head j < B, N ≥ 1 (written N + 1), and resource bounds d ≥ 9,
    s ≥ 10 ((N+3)(B+2))^8.  ASSUME the classical parity-correlation premise with
    error ε for formulas of depth ≤ d + 11 and size ≤ 12 U^10 (U = (N+3)(B+2)(s+2))
    on every m with N + 1 ≤ m ≤ B (N + 1).  Then:
    (1) the explicit attainability circuits lie in the class (RBound d s);
    (2) fed RO_{pi_j}, they succeed with conditional probability exactly 2/(q-1);
    (3) they satisfy CorrHyp with error ε;
    (4) every readout in the class succeeds with conditional probability
        ≤ 2/(q-1) + (q-1) ε.
    So the optimum over the class lies in [2/(q-1), 2/(q-1) + (q-1) ε]. -/
theorem conditional_sharpness {B N j d s : Nat} (hB : 2 ≤ B) (hj : j < B) (hd : 9 ≤ d)
    (hs : 10 * Ua (N + 1) B ^ 8 ≤ s) {ε : Rat}
    (hprem : ∀ m, N + 1 ≤ m → m ≤ B * (N + 1) →
      ParityCorrPremise (d + 11) (12 * Upar (N + 1) B s ^ 10) m ε) :
    (∀ b, RBound (attR B (N + 1) (fibreRep B (headVec j) false) (fibreRep B (headVec j) true) b)
      (N + 1) B d s) ∧
    succCountRO B (N + 1) (readoutOf B (attR B (N + 1) (fibreRep B (headVec j) false)
        (fibreRep B (headVec j) true))) j / nonzeroCount B (N + 1) =
      2 / (((2 ^ B : Nat) : Rat) - 1) ∧
    CorrHyp B (N + 1) (readoutOf B (attR B (N + 1) (fibreRep B (headVec j) false)
        (fibreRep B (headVec j) true))) ε ∧
    (∀ R : Bool → RCirc, (∀ b, RBound (R b) (N + 1) B d s) →
      succCountRO B (N + 1) (readoutOf B R) j / nonzeroCount B (N + 1) ≤
        2 / (((2 ^ B : Nat) : Rat) - 1) + (((2 ^ B : Nat) : Rat) - 1) * ε) := by
  have hw0 := headVec_ne_zero j
  have hwl := headVec_lt hj
  obtain ⟨n0, l0, _, _⟩ := fibreRep_spec hB hw0 hwl false
  obtain ⟨n1, l1, _, _⟩ := fibreRep_spec hB hw0 hwl true
  have hRB : ∀ b, RBound (attR B (N + 1) (fibreRep B (headVec j) false)
      (fibreRep B (headVec j) true) b) (N + 1) B d s := by
    intro b
    apply RBound_mono _ hd hs
    unfold attR
    cases b
    · exact attRC_RBound n0 l0
    · exact attRC_RBound n1 l1
  refine ⟨hRB, ?_, corrHyp_of_premise _ hRB hprem, fun R hR => circuit_readout_bound hj R hR hprem⟩
  rw [succCountRO_eq hj, succCount_attR n0 n1 l0 l1]
  exact attain_exact hB hw0 hwl

/-- ASYMPTOTIC FORM (absolute-error convention).  Fix B ≥ 2, j < B, d ≥ 9 and size
    bounds s N ≥ 10 ((N+3)(B+2))^8.  If the premise holds for every N with error
    ε N and ε is negligible, then there is δ with δ N ≥ 0, δ negligible, such that
    for every N the explicit circuits succeed with exactly 2/(q-1) and every
    readout in the class succeeds with at most 2/(q-1) + δ N. -/
theorem asymptotic_sharpness {B j d : Nat} (hB : 2 ≤ B) (hj : j < B) (hd : 9 ≤ d)
    (s : Nat → Nat) (hs : ∀ N, 10 * Ua (N + 1) B ^ 8 ≤ s N) (ε : Nat → Rat) (hε : Negligible ε)
    (hprem : ∀ N m, N + 1 ≤ m → m ≤ B * (N + 1) →
      ParityCorrPremise (d + 11) (12 * Upar (N + 1) B (s N) ^ 10) m (ε N)) :
    ∃ δ : Nat → Rat, Negligible δ ∧ (∀ N, 0 ≤ δ N) ∧ ∀ N,
      succCountRO B (N + 1) (readoutOf B (attR B (N + 1) (fibreRep B (headVec j) false)
          (fibreRep B (headVec j) true))) j / nonzeroCount B (N + 1) =
        2 / (((2 ^ B : Nat) : Rat) - 1) ∧
      ∀ R : Bool → RCirc, (∀ b, RBound (R b) (N + 1) B d (s N)) →
        succCountRO B (N + 1) (readoutOf B R) j / nonzeroCount B (N + 1) ≤
          2 / (((2 ^ B : Nat) : Rat) - 1) + δ N := by
  refine ⟨fun N => ((2 ^ B - 1 : Nat) : Rat) * ε N, negligible_const_mul _ hε, ?_, ?_⟩
  · intro N
    have hpos : 1 ≤ 12 * Upar (N + 1) B (s N) ^ 10 := by
      have := (Upar_ge (N + 1) B (s N)).1
      have := Nat.pow_pos (n := 10) this
      omega
    have h0 := premise_nonneg hpos (hprem N (N + 1) (Nat.le_refl _)
      (by have := Nat.mul_le_mul_right (N + 1) (show 1 ≤ B by omega); omega))
    exact Rat.mul_nonneg Rat.natCast_nonneg h0
  · intro N
    obtain ⟨_, hex, _, hup⟩ := conditional_sharpness (N := N) hB hj hd (hs N) (hprem N)
    refine ⟨hex, fun R hR => ?_⟩
    rw [natCast_pred]
    exact hup R hR

#print axioms cancel_iff_bit
#print axioms testBit_pred
#print axioms pos_iff_bit
#print axioms cancelIdx_firstTrue
#print axioms decIdx_firstTrue
#print axioms range_map_getD
#print axioms firstTrue_or
#print axioms firstTrue_lt
#print axioms attainF_eq
#print axioms firstC_eval
#print axioms cancel_eval
#print axioms nz_eval
#print axioms toNatBE_of_bits
#print axioms attR_correct
#print axioms succCount_attR
#print axioms Ua_ge
#print axioms mem_pair
#print axioms attRC_depth_size
#print axioms and_max'
#print axioms or_max'
#print axioms in_max
#print axioms attRC_max
#print axioms log2_lt
#print axioms attRC_RBound
#print axioms RBound_mono
#print axioms premise_nonneg
#print axioms conditional_sharpness
#print axioms asymptotic_sharpness

end AttainCircuit
end NimAudit
