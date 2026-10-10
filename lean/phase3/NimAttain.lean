import NimProbability

/- Phase 3, target A: attainability.  Written by Claude (10 October 2026).
   Lean 4.26.0, core/Std only.  Imports the unchanged phase 1-2 files.

   For B ≥ 2 and any nonzero B-bit functional ell(sigma) = <w, sigma>, an explicit
   readout (cancel a guessed nim-sum a_b at the first eligible heap, else subtract
   1 from the first nonzero heap, halt only on terminal boards) has conditional
   success
     * at least 2/(2^B-1) for ANY nonzero fibre representatives a_0, a_1, and
     * exactly 2/(2^B-1) when a_b is the least nonzero value in its fibre.
   The paper's B = 2, pi_0 example (a_0 = 2, a_1 = 1) is the least-representative
   case, so its success is exactly 2/3 for every N ≥ 1.

   This file proves the finite combinatorics only; it says nothing about circuit
   complexity of the readout (that belongs to targets C/D). -/

namespace NimAudit
namespace Attain

open Game Rollout Prob

attribute [local simp] Rat.add_zero Rat.zero_add Rat.zero_mul Rat.mul_zero Rat.one_mul

/-! ## The readout -/

/-- First index i with x_i XOR t < x_i, with the new value x_i XOR t. -/
def cancelIdx (t : Nat) : List Nat → Option (Nat × Nat)
  | [] => none
  | x :: rest =>
    if x ^^^ t < x then some (0, x ^^^ t) else (cancelIdx t rest).map (fun p => (p.1 + 1, p.2))

/-- First nonzero index i with new value x_i - 1. -/
def decIdx : List Nat → Option (Nat × Nat)
  | [] => none
  | x :: rest => if 0 < x then some (0, x - 1) else (decIdx rest).map (fun p => (p.1 + 1, p.2))

/-- Attainability readout with guesses a_0 (observed bit false) and a_1 (true). -/
def attainF (a0 a1 : Nat) : Readout := fun P b =>
  match cancelIdx (if b then a1 else a0) P with
  | some m => some m
  | none => decIdx P

theorem cancelIdx_some {t : Nat} {P : List Nat} {i v : Nat} (h : cancelIdx t P = some (i, v)) :
    ∃ x, P[i]? = some x ∧ v = x ^^^ t ∧ v < x := by
  induction P generalizing i v with
  | nil => simp [cancelIdx] at h
  | cons x rest ih =>
    by_cases hx : x ^^^ t < x
    · simp only [cancelIdx, hx, if_true, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨x, rfl, rfl, hx⟩
    · simp only [cancelIdx, hx, if_false] at h
      cases hr : cancelIdx t rest with
      | none => simp [hr] at h
      | some p =>
        obtain ⟨i', v'⟩ := p
        simp only [hr, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨y, hy, rfl, hlt⟩ := ih hr
        exact ⟨y, by simpa using hy, rfl, hlt⟩

theorem cancelIdx_none {t : Nat} {P : List Nat} (h : cancelIdx t P = none) :
    ∀ x ∈ P, ¬ x ^^^ t < x := by
  induction P with
  | nil => simp
  | cons x rest ih =>
    by_cases hx : x ^^^ t < x
    · simp [cancelIdx, hx] at h
    · simp only [cancelIdx, hx, if_false] at h
      cases hr : cancelIdx t rest with
      | some p => simp [hr] at h
      | none =>
        intro y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · exact hx
        · exact ih hr y hy

theorem decIdx_some {P : List Nat} {i v : Nat} (h : decIdx P = some (i, v)) :
    ∃ x, P[i]? = some x ∧ v = x - 1 ∧ 0 < x := by
  induction P generalizing i v with
  | nil => simp [decIdx] at h
  | cons x rest ih =>
    by_cases hx : 0 < x
    · simp only [decIdx, hx, if_true, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨x, rfl, rfl, hx⟩
    · simp only [decIdx, hx, if_false] at h
      cases hr : decIdx rest with
      | none => simp [hr] at h
      | some p =>
        obtain ⟨i', v'⟩ := p
        simp only [hr, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨y, hy, rfl, hlt⟩ := ih hr
        exact ⟨y, by simpa using hy, rfl, hlt⟩

theorem decIdx_none {P : List Nat} (h : decIdx P = none) : Terminal P := by
  induction P with
  | nil => intro x hx; simp at hx
  | cons x rest ih =>
    by_cases hx : 0 < x
    · simp [decIdx, hx] at h
    · simp only [decIdx, hx, if_false] at h
      cases hr : decIdx rest with
      | some p => simp [hr] at h
      | none =>
        intro y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · omega
        · exact ih hr y hy

theorem decIdx_terminal {P : List Nat} (h : Terminal P) : decIdx P = none := by
  induction P with
  | nil => rfl
  | cons x rest ih =>
    have hx : x = 0 := h x (by simp)
    subst hx
    simp [decIdx, ih (fun y hy => h y (List.mem_cons_of_mem _ hy))]

theorem cancelIdx_terminal {t : Nat} {P : List Nat} (h : Terminal P) : cancelIdx t P = none := by
  induction P with
  | nil => rfl
  | cons x rest ih =>
    have hx : x = 0 := h x (by simp)
    subst hx
    simp [cancelIdx, ih (fun y hy => h y (List.mem_cons_of_mem _ hy))]

/-- Every output of the readout is a legal move (index in range, value strictly smaller). -/
theorem attainF_legal {a0 a1 : Nat} {P : List Nat} {b : Bool} {i v : Nat}
    (h : attainF a0 a1 P b = some (i, v)) : ∃ x, P[i]? = some x ∧ v < x := by
  unfold attainF at h
  split at h
  · next m hm =>
    cases h
    obtain ⟨x, hx, rfl, hlt⟩ := cancelIdx_some hm
    exact ⟨x, hx, hlt⟩
  · obtain ⟨x, hx, rfl, hlt⟩ := decIdx_some h
    exact ⟨x, hx, by omega⟩

theorem attainF_move {a0 a1 : Nat} {P : List Nat} {b : Bool} {i v : Nat}
    (h : attainF a0 a1 P b = some (i, v)) : Move P (P.set i v) := by
  obtain ⟨x, hx, hlt⟩ := attainF_legal h
  exact set_move hx hlt

/-- The readout halts exactly on terminal boards. -/
theorem attainF_none_iff (a0 a1 : Nat) (P : List Nat) (b : Bool) :
    attainF a0 a1 P b = none ↔ Terminal P := by
  constructor
  · intro h
    unfold attainF at h
    split at h
    · cases h
    · exact decIdx_none h
  · intro ht
    unfold attainF
    rw [cancelIdx_terminal ht, decIdx_terminal ht]

theorem gval_attainF_cancel {a0 a1 : Nat} {P : List Nat} {b : Bool} {i v : Nat}
    (hc : cancelIdx (if b then a1 else a0) P = some (i, v)) :
    gval (attainF a0 a1) b P = (if b then a1 else a0) := by
  obtain ⟨x, hx, rfl, hlt⟩ := cancelIdx_some hc
  have hF : attainF a0 a1 P b = some (i, x ^^^ (if b then a1 else a0)) := by
    unfold attainF; rw [hc]
  unfold gval
  rw [hF]
  simp only [hx, hlt, if_true]
  exact xor_cancel_left x _

/-- SUCCESS WHEN THE GUESS IS RIGHT: if sigma(P) = a_b ≠ 0 the readout wins. -/
theorem attain_success {a0 a1 : Nat} {P : List Nat} {b : Bool}
    (hs : nimSum P = (if b then a1 else a0)) (h0 : nimSum P ≠ 0) :
    successB (attainF a0 a1) b P = true := by
  rw [success_iff_gval h0]
  obtain ⟨pre, x, post, hp, hlt, _⟩ := exists_decreasing_heap P h0
  cases hc : cancelIdx (if b then a1 else a0) P with
  | none =>
    exact absurd (hs ▸ hlt) (cancelIdx_none hc x (by rw [hp]; simp))
  | some m =>
    obtain ⟨i, v⟩ := m
    rw [gval_attainF_cancel hc, hs]

/-! ## Lower bound 2/(2^B - 1) for any fibre representatives -/

theorem rsum_nonneg_ite {α : Type} (l : List α) (p : α → Prop) [DecidablePred p] :
    (0 : Rat) ≤ rsum l (fun x => if p x then 1 else 0) := by
  have := rsum_le (l := l) (f := fun _ => (0 : Rat)) (g := fun x => if p x then 1 else 0)
    (by intro x _; show (0 : Rat) ≤ if p x then 1 else 0; split <;> grind)
  rw [rsum_zero] at this
  exact this

/-- (counting form) #success ≥ #{sigma = a_0} + #{sigma = a_1} = 2 q^N. -/
theorem attain_count_lower {B N w a0 a1 : Nat} (ha0 : a0 ≠ 0) (ha1 : a1 ≠ 0)
    (hd0 : dotB B w a0 = false) (hd1 : dotB B w a1 = true)
    (hl0 : a0 < 2 ^ B) (hl1 : a1 < 2 ^ B) :
    2 * ((2 ^ B : Nat) : Rat) ^ N ≤ succCount B (N + 1) (attainF a0 a1) w := by
  have hne : a0 ≠ a1 := by intro e; rw [e, hd1] at hd0; cases hd0
  have hle : rsum (boards (2 ^ B) (N + 1))
      (fun P => (if nimSum P = a0 then 1 else 0) + (if nimSum P = a1 then 1 else 0)) ≤
      succCount B (N + 1) (attainF a0 a1) w := by
    unfold succCount
    apply rsum_le
    intro P _
    by_cases h0 : nimSum P = a0
    · have hs : successB (attainF a0 a1) (dotB B w (nimSum P)) P = true := by
        apply attain_success
        · rw [h0, hd0]; simp
        · rw [h0]; exact ha0
      rw [h0] at hs
      simp [h0, hne, hs, ha0]
      exact Rat.le_refl
    · by_cases h1 : nimSum P = a1
      · have hs : successB (attainF a0 a1) (dotB B w (nimSum P)) P = true := by
          apply attain_success
          · rw [h1, hd1]; simp
          · rw [h1]; exact ha1
        rw [h1] at hs
        simp [h1, hs, ha1, Ne.symm hne]
        exact Rat.le_refl
      · simp only [h0, h1, if_false, Rat.add_zero]
        split <;> grind
  rw [rsum_add, sigma_uniform B N a0 hl0, sigma_uniform B N a1 hl1] at hle
  grind

theorem nonzeroCount_eq' (B N : Nat) :
    nonzeroCount B (N + 1) = (((2 ^ B : Nat) : Rat) - 1) * ((2 ^ B : Nat) : Rat) ^ N := by
  rw [nonzeroCount_eq]
  unfold T
  rw [Rat.pow_succ]
  grind

theorem qpow_pos (B N : Nat) : (0 : Rat) < ((2 ^ B : Nat) : Rat) ^ N := by
  rw [← Rat.natCast_pow]; exact Rat.natCast_pos.mpr (Nat.pow_pos (Nat.two_pow_pos B))

theorem q_ge_two {B : Nat} (hB : 1 ≤ B) : (2 : Rat) ≤ ((2 ^ B : Nat) : Rat) := by
  have hqge : 2 ≤ 2 ^ B := by
    have := Nat.pow_le_pow_right (show 0 < 2 by decide) hB; simpa using this
  have := Rat.natCast_le_natCast.mpr hqge; simpa using this

/-- LOWER BOUND: for B ≥ 1 and any nonzero fibre representatives a_0, a_1,
    Pr[legal winning move | sigma ≠ 0] ≥ 2/(2^B - 1). -/
theorem attain_lower {B N w a0 a1 : Nat} (hB : 1 ≤ B) (ha0 : a0 ≠ 0) (ha1 : a1 ≠ 0)
    (hd0 : dotB B w a0 = false) (hd1 : dotB B w a1 = true)
    (hl0 : a0 < 2 ^ B) (hl1 : a1 < 2 ^ B) :
    2 / (((2 ^ B : Nat) : Rat) - 1) ≤
      succCount B (N + 1) (attainF a0 a1) w / nonzeroCount B (N + 1) := by
  have hc := attain_count_lower (N := N) ha0 ha1 hd0 hd1 hl0 hl1
  rw [nonzeroCount_eq']
  have ht := qpow_pos B N
  have hq2 := q_ge_two hB
  generalize succCount B (N + 1) (attainF a0 a1) w = S at *
  generalize ((2 ^ B : Nat) : Rat) ^ N = t at *
  generalize ((2 ^ B : Nat) : Rat) = q at *
  have h1 : (0 : Rat) < q - 1 := by grind
  have hZ : 0 < (q - 1) * t := Rat.mul_pos h1 ht
  have hZ' : (q - 1) * t ≠ 0 := Rat.ne_of_gt hZ
  have hq1 : q - 1 ≠ 0 := Rat.ne_of_gt h1
  -- 2/(q-1) * Z = 2 t ≤ S, so 2/(q-1) ≤ S/Z
  apply Rat.le_of_mul_le_mul_right _ hZ
  have e1 : 2 / (q - 1) * ((q - 1) * t) = 2 * t := by grind
  have e2 : S / ((q - 1) * t) * ((q - 1) * t) = S := by grind
  rw [e1, e2]
  exact hc

/-! ## Least fibre representatives and exact equality -/

/-- Least n' < n with p n' (if any). -/
def findLeast (p : Nat → Bool) : Nat → Option Nat
  | 0 => none
  | n + 1 =>
    match findLeast p n with
    | some a => some a
    | none => if p n then some n else none

theorem findLeast_some {p : Nat → Bool} {n a : Nat} (h : findLeast p n = some a) :
    p a = true ∧ a < n ∧ ∀ c < a, p c = false := by
  induction n generalizing a with
  | zero => simp [findLeast] at h
  | succ n ih =>
    unfold findLeast at h
    split at h
    · next a' ha' =>
      cases h
      obtain ⟨h1, h2, h3⟩ := ih ha'
      exact ⟨h1, by omega, h3⟩
    · next hnone =>
      by_cases hp : p n = true
      · simp only [hp, if_true, Option.some.injEq] at h
        subst h
        refine ⟨hp, by omega, ?_⟩
        intro c hc
        have key : ∀ m, findLeast p m = none → ∀ c < m, p c = false := by
          intro m
          induction m with
          | zero => intro _ c hc; omega
          | succ m ihm =>
            intro hm c hc
            unfold findLeast at hm
            split at hm
            · cases hm
            · next hm' =>
              by_cases hpm : p m = true
              · simp [hpm] at hm
              · by_cases hcm : c = m
                · subst hcm; simpa using hpm
                · exact ihm hm' c (by omega)
        exact key n hnone c hc
      · simp [hp] at h

theorem findLeast_isSome {p : Nat → Bool} {n c : Nat} (hc : c < n) (hp : p c = true) :
    ∃ a, findLeast p n = some a := by
  induction n with
  | zero => omega
  | succ n ih =>
    unfold findLeast
    cases hf : findLeast p n with
    | some a => exact ⟨a, rfl⟩
    | none =>
      by_cases hcn : c = n
      · subst hcn; exact ⟨c, by simp [hp]⟩
      · obtain ⟨a, ha⟩ := ih (by omega)
        rw [hf] at ha; cases ha

/-- The fibre predicate: nonzero with ell(a) = b. -/
def inFibre (B w : Nat) (b : Bool) (a : Nat) : Bool := a != 0 && dotB B w a == b

/-- Least nonzero B-bit value in the fibre ell = b (0 if none). -/
def fibreRep (B w : Nat) (b : Bool) : Nat := (findLeast (inFibre B w b) (2 ^ B)).getD 0

theorem dotB_comm (B u v : Nat) : dotB B u v = dotB B v u := by
  induction B with
  | zero => rfl
  | succ B ih => simp only [dotB, ih, Bool.and_comm]

theorem dotB_two_pow_right (B j v : Nat) : dotB B v (2 ^ j) = (decide (j < B) && v.testBit j) := by
  rw [dotB_comm, dotB_two_pow]

/-- Both fibres of a nonzero functional on F_2^B (B ≥ 2) contain a nonzero vector. -/
theorem fibre_nonempty {B w : Nat} (hB : 2 ≤ B) (hw0 : w ≠ 0) (hw : w < 2 ^ B) (b : Bool) :
    ∃ c, c < 2 ^ B ∧ inFibre B w b c = true := by
  obtain ⟨i, hi⟩ := Nat.exists_testBit_of_ne_zero hw0
  have hiB : i < B := by
    rcases Nat.lt_or_ge i B with hlt | hge
    · exact hlt
    exfalso
    have := Nat.testBit_lt_two_pow
      (Nat.lt_of_lt_of_le hw (Nat.pow_le_pow_right (by decide) (by omega)) : w < 2 ^ i)
    rw [this] at hi; cases hi
  have hpi : 2 ^ i < 2 ^ B := Nat.pow_lt_pow_right (by decide) hiB
  cases b with
  | true =>
    refine ⟨2 ^ i, hpi, ?_⟩
    simp [inFibre, dotB_two_pow_right, hiB, hi, Nat.ne_of_gt (Nat.two_pow_pos i)]
  | false =>
    let k := if i = 0 then 1 else 0
    have hkB : k < B := by simp only [k]; split <;> omega
    have hki : k ≠ i := by simp only [k]; split <;> omega
    have hpk : 2 ^ k < 2 ^ B := Nat.pow_lt_pow_right (by decide) hkB
    cases hwk : w.testBit k with
    | false =>
      refine ⟨2 ^ k, hpk, ?_⟩
      simp [inFibre, dotB_two_pow_right, hkB, hwk, Nat.ne_of_gt (Nat.two_pow_pos k)]
    | true =>
      refine ⟨2 ^ i ^^^ 2 ^ k, Nat.xor_lt_two_pow hpi hpk, ?_⟩
      have hne : 2 ^ i ^^^ 2 ^ k ≠ 0 := by
        intro h
        have e := congrArg (fun z => z.testBit i) (xor_eq_zero_imp h)
        simp only [Nat.testBit_two_pow, decide_true] at e
        exact hki (of_decide_eq_true e.symm)
      simp only [inFibre, dotB_xor_right, dotB_two_pow_right, hiB, hkB, hi, hwk,
        decide_true, Bool.true_and]
      simp [hne]

theorem fibreRep_spec {B w : Nat} (hB : 2 ≤ B) (hw0 : w ≠ 0) (hw : w < 2 ^ B) (b : Bool) :
    fibreRep B w b ≠ 0 ∧ fibreRep B w b < 2 ^ B ∧ dotB B w (fibreRep B w b) = b ∧
      ∀ c, c < fibreRep B w b → c ≠ 0 → dotB B w c ≠ b := by
  obtain ⟨c, hc, hpc⟩ := fibre_nonempty hB hw0 hw b
  obtain ⟨a, ha⟩ := findLeast_isSome hc hpc
  obtain ⟨h1, h2, h3⟩ := findLeast_some ha
  have hrep : fibreRep B w b = a := by simp [fibreRep, ha]
  rw [hrep]
  simp only [inFibre, Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at h1
  refine ⟨h1.1, h2, h1.2, ?_⟩
  intro c' hc' hc0 hd
  have := h3 c' hc'
  simp [inFibre, hc0, hd] at this

/-- x XOR (x - 1) is a low mask 2^s - 1, for x > 0. -/
theorem xor_pred_mask (x : Nat) (hx : 0 < x) : ∃ s, x ^^^ (x - 1) = 2 ^ s - 1 := by
  induction x using Nat.strongRecOn with
  | ind x ih =>
    rcases Nat.mod_two_eq_zero_or_one x with hev | hod
    · -- x = 2y with y > 0
      have hy : 0 < x / 2 := by omega
      obtain ⟨s, hs⟩ := ih (x / 2) (by omega) hy
      refine ⟨s + 1, ?_⟩
      have key : x ^^^ (x - 1) = 2 * ((x / 2) ^^^ (x / 2 - 1)) + 1 := by
        apply Nat.eq_of_testBit_eq
        intro i
        cases i with
        | zero =>
          rw [Nat.testBit_xor, Nat.testBit_zero, Nat.testBit_zero, Nat.testBit_zero]
          have h1 : (x - 1) % 2 = 1 := by omega
          have h2 : (2 * ((x / 2) ^^^ (x / 2 - 1)) + 1) % 2 = 1 := by omega
          simp [hev, h1, h2]
        | succ i =>
          rw [Nat.testBit_xor, ← Nat.testBit_div_two x i, ← Nat.testBit_div_two (x - 1) i,
            ← Nat.testBit_div_two (2 * ((x / 2) ^^^ (x / 2 - 1)) + 1) i]
          have e1 : (x - 1) / 2 = x / 2 - 1 := by omega
          have e2 : (2 * ((x / 2) ^^^ (x / 2 - 1)) + 1) / 2 = (x / 2) ^^^ (x / 2 - 1) := by omega
          rw [e1, e2, Nat.testBit_xor]
      rw [key, hs, Nat.pow_succ]
      have := Nat.two_pow_pos s
      omega
    · refine ⟨1, ?_⟩
      apply Nat.eq_of_testBit_eq
      intro i
      cases i with
      | zero =>
        rw [Nat.testBit_xor, Nat.testBit_zero, Nat.testBit_zero]
        have h1 : (x - 1) % 2 = 0 := by omega
        simp [hod, h1]
      | succ i =>
        rw [Nat.testBit_xor, ← Nat.testBit_div_two x i, ← Nat.testBit_div_two (x - 1) i]
        have e1 : (x - 1) / 2 = x / 2 := by omega
        rw [e1, Bool.xor_self]
        exact (Nat.testBit_lt_two_pow (Nat.one_lt_two_pow (by omega) : (2 ^ 1 - 1) < 2 ^ (i + 1))).symm

/-- NO ADDITIONAL SUCCESS for least representatives: if sigma ≠ 0 and sigma differs
    from the guess a_{ell(sigma)}, the readout's move does not win. -/
theorem attain_no_extra {B w : Nat} (hB : 2 ≤ B) (hw0 : w ≠ 0) (hw : w < 2 ^ B)
    {P : List Nat} (h0 : nimSum P ≠ 0)
    (hne : nimSum P ≠ fibreRep B w (dotB B w (nimSum P))) :
    successB (attainF (fibreRep B w false) (fibreRep B w true)) (dotB B w (nimSum P)) P = false := by
  have key : ¬ gval (attainF (fibreRep B w false) (fibreRep B w true)) (dotB B w (nimSum P)) P =
      nimSum P := by
    generalize hbdef : dotB B w (nimSum P) = b at hne
    have ht : (if b then fibreRep B w true else fibreRep B w false) = fibreRep B w b := by
      cases b <;> rfl
    obtain ⟨tnz, _, tdot, tmin⟩ := fibreRep_spec hB hw0 hw b
    cases hc : cancelIdx (if b then fibreRep B w true else fibreRep B w false) P with
    | some m =>
      obtain ⟨i, v⟩ := m
      rw [gval_attainF_cancel hc, ht]
      exact fun e => hne e.symm
    | none =>
      rw [ht] at hc
      -- the fallback is used
      have hnt : ¬ Terminal P := by
        intro hterm
        apply h0
        have : ∀ q : List Nat, Terminal q → nimSum q = 0 := by
          intro q hq
          induction q with
          | nil => rfl
          | cons y ys ihq =>
            simp only [nimSum, hq y (by simp), Nat.zero_xor]
            exact ihq (fun z hz => hq z (List.mem_cons_of_mem _ hz))
        exact this P hterm
      cases hd : decIdx P with
      | none => exact absurd (decIdx_none hd) hnt
      | some m =>
        obtain ⟨i, v⟩ := m
        obtain ⟨x, hx, rfl, hxpos⟩ := decIdx_some hd
        have hF : attainF (fibreRep B w false) (fibreRep B w true) P b = some (i, x - 1) := by
          unfold attainF; rw [ht, hc]; exact hd
        unfold gval
        rw [hF]
        simp only [hx, show x - 1 < x by omega, if_true]
        intro hdelta
        -- top bit k of t = fibreRep B w b is absent from every heap
        let t := fibreRep B w b
        let k := t.log2
        have htk : t.testBit k = true := by
          cases hb' : t.testBit k with
          | true => rfl
          | false =>
            exfalso
            have hlt : t < 2 ^ k := by
              apply Nat.lt_pow_two_of_testBit
              intro i' hi'
              by_cases hik : i' = k
              · subst hik; exact hb'
              · apply Nat.testBit_lt_two_pow
                exact Nat.lt_of_lt_of_le Nat.lt_log2_self
                  (Nat.pow_le_pow_right (by decide) (by omega))
            exact absurd (Nat.log2_self_le tnz) (Nat.not_le.mpr hlt)
        have habove : ∀ i', k < i' → t.testBit i' = false := by
          intro i' hi'
          apply Nat.testBit_lt_two_pow
          exact Nat.lt_of_lt_of_le Nat.lt_log2_self (Nat.pow_le_pow_right (by decide) (by omega))
        have hnoheap : ∀ y ∈ P, y.testBit k = false := by
          intro y hy
          cases hyk : y.testBit k with
          | false => rfl
          | true =>
            exfalso
            apply cancelIdx_none hc y hy
            apply lt_of_top_testBit (k := k)
            · rw [Nat.testBit_xor, hyk, htk]; rfl
            · exact hyk
            · intro i' hi'; rw [Nat.testBit_xor, habove i' hi', Bool.xor_false]
        have hsk : (nimSum P).testBit k = false := by
          cases hsk' : (nimSum P).testBit k with
          | false => rfl
          | true =>
            obtain ⟨y, hy, hyk⟩ := exists_heap_testBit hsk'
            rw [hnoheap y hy] at hyk; cases hyk
        obtain ⟨s, hs⟩ := xor_pred_mask x hxpos
        rw [hdelta] at hs
        have hks : ¬ k < s := by
          intro hlt
          have := Nat.testBit_two_pow_sub_one s k
          rw [← hs, hsk] at this
          simp [hlt] at this
        have hσlt : nimSum P < t := by
          have h1 : nimSum P < 2 ^ s := by rw [hs]; have := Nat.two_pow_pos s; omega
          have h2 : 2 ^ s ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) (by omega)
          have h3 : 2 ^ k ≤ t := Nat.log2_self_le tnz
          omega
        exact tmin (nimSum P) hσlt h0 hbdef
  cases hs : successB (attainF (fibreRep B w false) (fibreRep B w true)) (dotB B w (nimSum P)) P
  · rfl
  · exact absurd ((success_iff_gval h0).1 hs) key

/-- EXACT SUCCESS COUNT for least representatives: #success = 2 q^N. -/
theorem attain_count_exact {B N w : Nat} (hB : 2 ≤ B) (hw0 : w ≠ 0) (hw : w < 2 ^ B) :
    succCount B (N + 1) (attainF (fibreRep B w false) (fibreRep B w true)) w =
      2 * ((2 ^ B : Nat) : Rat) ^ N := by
  obtain ⟨n0, l0, d0, _⟩ := fibreRep_spec hB hw0 hw false
  obtain ⟨n1, l1, d1, _⟩ := fibreRep_spec hB hw0 hw true
  have hne : fibreRep B w false ≠ fibreRep B w true := by
    intro e; rw [e, d1] at d0; cases d0
  have heq : succCount B (N + 1) (attainF (fibreRep B w false) (fibreRep B w true)) w =
      rsum (boards (2 ^ B) (N + 1))
        (fun P => (if nimSum P = fibreRep B w false then 1 else 0) +
          (if nimSum P = fibreRep B w true then 1 else 0)) := by
    unfold succCount
    apply rsum_congr
    intro P _
    by_cases h0 : nimSum P = fibreRep B w false
    · have hs := attain_success (a0 := fibreRep B w false) (a1 := fibreRep B w true)
        (b := dotB B w (nimSum P)) (P := P) (by rw [h0, d0]; simp) (by rw [h0]; exact n0)
      rw [h0] at hs
      simp [h0, hne, hs, n0]
    · by_cases h1 : nimSum P = fibreRep B w true
      · have hs := attain_success (a0 := fibreRep B w false) (a1 := fibreRep B w true)
          (b := dotB B w (nimSum P)) (P := P) (by rw [h1, d1]; simp) (by rw [h1]; exact n1)
        rw [h1] at hs
        simp [h1, hs, n1, Ne.symm hne]
      · simp only [h0, h1, if_false, Rat.add_zero]
        by_cases hz : nimSum P = 0
        · simp [hz]
        · have hguess : nimSum P ≠ fibreRep B w (dotB B w (nimSum P)) := by
            cases hb : dotB B w (nimSum P)
            · exact h0
            · exact h1
          have := attain_no_extra hB hw0 hw hz hguess
          simp [this]
  rw [heq, rsum_add, sigma_uniform B N _ l0, sigma_uniform B N _ l1]
  grind

/-- EXACT ATTAINABILITY: for B ≥ 2, any nonzero B-bit functional w, every N ≥ 1,
    the least-representative readout succeeds with conditional probability exactly
    2/(2^B - 1). -/
theorem attain_exact {B N w : Nat} (hB : 2 ≤ B) (hw0 : w ≠ 0) (hw : w < 2 ^ B) :
    succCount B (N + 1) (attainF (fibreRep B w false) (fibreRep B w true)) w /
        nonzeroCount B (N + 1) = 2 / (((2 ^ B : Nat) : Rat) - 1) := by
  rw [attain_count_exact hB hw0 hw, nonzeroCount_eq']
  have ht := qpow_pos B N
  have hq2 := q_ge_two (B := B) (by omega)
  generalize ((2 ^ B : Nat) : Rat) ^ N = t at *
  generalize ((2 ^ B : Nat) : Rat) = q at *
  have h1 : q - 1 ≠ 0 := by grind
  have h2 : t ≠ 0 := Rat.ne_of_gt ht
  grind

/-! ## Structured heads and the paper's B = 2 example -/

/-- The readout fed the actual rollout outcome RO_{pi_j}(P) has the same success
    count as when fed <w_j, sigma(P)>. -/
theorem succCountRO_eq {B N j : Nat} (hj : j < B) (F : Readout) :
    succCountRO B N F j = succCount B N F (headVec j) := by
  unfold succCountRO succCount
  apply rsum_congr; intro P _
  rw [rollout_outcome_linear hj]

/-- EXACT ATTAINABILITY FOR EACH STRUCTURED HEAD pi_j (j < B, B ≥ 2), with the
    readout fed the executed rollout outcome. -/
theorem attain_exact_head {B N j : Nat} (hB : 2 ≤ B) (hj : j < B) :
    succCountRO B (N + 1)
        (attainF (fibreRep B (headVec j) false) (fibreRep B (headVec j) true)) j /
      nonzeroCount B (N + 1) = 2 / (((2 ^ B : Nat) : Rat) - 1) := by
  rw [succCountRO_eq hj]
  exact attain_exact hB (headVec_ne_zero j) (headVec_lt hj)

theorem rep_B2_false : fibreRep 2 (headVec 0) false = 2 := by decide
theorem rep_B2_true : fibreRep 2 (headVec 0) true = 1 := by decide

/-- THE PAPER'S EXAMPLE: B = 2, head pi_0, guesses a_0 = 2, a_1 = 1, fallback
    "subtract 1": conditional success exactly 2/3 for every N ≥ 1. -/
theorem paper_example_two_thirds (N : Nat) :
    succCountRO 2 (N + 1) (attainF 2 1) 0 / nonzeroCount 2 (N + 1) = 2 / 3 := by
  have := attain_exact_head (B := 2) (N := N) (j := 0) (by decide) (by decide)
  rw [rep_B2_false, rep_B2_true] at this
  rw [this]
  have e : (((2 ^ 2 : Nat) : Rat) - 1) = 3 := by
    rw [show (2 ^ 2 : Nat) = 4 from rfl]; simp; grind
  rw [e]

/-! ## Sharpness of the leading constant -/

/-- CorrHyp forces η ≥ 0 (B ≥ 1). -/
theorem corrHyp_nonneg {B N : Nat} {F : Readout} {η : Rat} (hB : 1 ≤ B)
    (hyp : CorrHyp B N F η) : 0 ≤ η := by
  have h1 : 1 < 2 ^ B := Nat.one_lt_two_pow (by omega)
  obtain ⟨k1, k2⟩ := hyp false 0 1 (Nat.two_pow_pos B) (by decide) h1
  grind

/-- SHARPNESS (finite, two-sided).  For B ≥ 2, N ≥ 1 and a structured head j < B:
    (1) the explicit readout attains exactly 2/(q-1);
    (2) every readout satisfying CorrHyp with error η succeeds with conditional
        probability at most 2/(q-1) + (q-1) η.
    Hence no constant below 2/(q-1) can replace the leading term in (2) for any
    class containing the explicit readout, PROVIDED that readout satisfies the
    correlation premise with η_N → 0.  That proviso is the circuit/correlation
    bridge (targets C/D); it is not proved here. -/
theorem sharpness {B N j : Nat} (hB : 2 ≤ B) (hj : j < B) :
    succCountRO B (N + 1)
        (attainF (fibreRep B (headVec j) false) (fibreRep B (headVec j) true)) j /
      nonzeroCount B (N + 1) = 2 / (((2 ^ B : Nat) : Rat) - 1) ∧
    ∀ (F : Readout) (η : Rat), CorrHyp B (N + 1) F η →
      succCountRO B (N + 1) F j / nonzeroCount B (N + 1) ≤
        2 / (((2 ^ B : Nat) : Rat) - 1) + (((2 ^ B : Nat) : Rat) - 1) * η :=
  ⟨attain_exact_head hB hj, fun F _ hyp => structured_head_bound hj F hyp⟩

#print axioms cancelIdx_some
#print axioms cancelIdx_none
#print axioms decIdx_some
#print axioms decIdx_none
#print axioms decIdx_terminal
#print axioms cancelIdx_terminal
#print axioms attainF_legal
#print axioms attainF_move
#print axioms attainF_none_iff
#print axioms gval_attainF_cancel
#print axioms attain_success
#print axioms rsum_nonneg_ite
#print axioms attain_count_lower
#print axioms nonzeroCount_eq'
#print axioms qpow_pos
#print axioms q_ge_two
#print axioms attain_lower
#print axioms findLeast_some
#print axioms findLeast_isSome
#print axioms dotB_comm
#print axioms dotB_two_pow_right
#print axioms fibre_nonempty
#print axioms fibreRep_spec
#print axioms xor_pred_mask
#print axioms attain_no_extra
#print axioms attain_count_exact
#print axioms attain_exact
#print axioms succCountRO_eq
#print axioms attain_exact_head
#print axioms rep_B2_false
#print axioms rep_B2_true
#print axioms paper_example_two_thirds
#print axioms corrHyp_nonneg
#print axioms sharpness

end Attain
end NimAudit
