import NimCore

/- Extension to NimCore.lean, written for the independent Claude review (9 October 2026).
   Lean 4.26.0, core/Std only.  NimCore.lean is imported unchanged.

   Part A.  Actual execution of the structured rollout policy pi_j.
     A legal policy move from board p (a list of heap sizes) to board q is:
       * subtract 2^j from some heap of size >= 2^j, or
       * if every heap is < 2^j, subtract 1 from some nonzero heap.
     The tie-breaking rule (which eligible heap is used) is left arbitrary in
     `PolicyMove`/`Run`, so the count theorem covers every tie-breaking rule.
     `rolloutMoves` is a concrete deterministic simulator that uses the first
     eligible heap, exactly as `rollout` in checks/check_revision.py.
     Main results: every complete run has length rolloutCount j p
     (= sum of h / 2^j + h % 2^j), and its parity is channel j (nimSum p).

   Part B.  If the nim-sum is nonzero, some heap x satisfies x ^^^ nimSum p < x,
     so the replacement in `move_to_zero_algebra` is a legal (strictly
     decreasing) Nim move to a zero-nim-sum position.

   Nothing here concerns circuit complexity, probability or learning. -/

namespace NimAudit
namespace Rollout

/-! ## Part A: rollout execution -/

/-- One legal move of the structured policy `pi_j` (tie-breaking unspecified). -/
def PolicyMove (j : Nat) (p q : List Nat) : Prop :=
  (∃ pre x post, p = pre ++ x :: post ∧ 2 ^ j ≤ x ∧ q = pre ++ (x - 2 ^ j) :: post) ∨
  ((∀ x ∈ p, x < 2 ^ j) ∧
    ∃ pre x post, p = pre ++ x :: post ∧ 0 < x ∧ q = pre ++ (x - 1) :: post)

/-- `Run j p n`: following `pi_j` from board `p` reaches the all-zero board after
    exactly `n` policy moves. -/
inductive Run (j : Nat) : List Nat → Nat → Prop
  | done (p : List Nat) : (∀ x ∈ p, x = 0) → Run j p 0
  | step (p q : List Nat) (n : Nat) : PolicyMove j p q → Run j q n → Run j p (n + 1)

/-- Every policy move is a legal Nim move: one heap decreases by a positive
    amount `d ≤ x`, with `d = 2^j` or `d = 1`; all other heaps are unchanged. -/
theorem policyMove_legal {j : Nat} {p q : List Nat} (hm : PolicyMove j p q) :
    ∃ pre x post d, p = pre ++ x :: post ∧ q = pre ++ (x - d) :: post ∧
      0 < d ∧ d ≤ x ∧ (d = 2 ^ j ∨ d = 1) := by
  rcases hm with ⟨pre, x, post, hp, hx, hq⟩ | ⟨_, pre, x, post, hp, hx, hq⟩
  · exact ⟨pre, x, post, 2 ^ j, hp, hq, Nat.two_pow_pos j, hx, Or.inl rfl⟩
  · exact ⟨pre, x, post, 1, hp, hq, Nat.one_pos, hx, Or.inr rfl⟩

theorem rolloutCount_split (j : Nat) (pre post : List Nat) (x : Nat) :
    rolloutCount j (pre ++ x :: post) =
      rolloutCount j pre + heapCount j x + rolloutCount j post := by
  simp [rolloutCount, List.sum_append_nat, Nat.add_assoc]

theorem heapCount_sub_pow {j x : Nat} (hx : 2 ^ j ≤ x) :
    heapCount j (x - 2 ^ j) + 1 = heapCount j x := by
  obtain ⟨y, rfl⟩ : ∃ y, x = y + 2 ^ j := ⟨x - 2 ^ j, (Nat.sub_add_cancel hx).symm⟩
  simp only [heapCount, Nat.add_sub_cancel, Nat.add_div_right _ (Nat.two_pow_pos j),
    Nat.add_mod_right]
  omega

theorem heapCount_sub_one {j x : Nat} (hpos : 0 < x) (hlt : x < 2 ^ j) :
    heapCount j (x - 1) + 1 = heapCount j x := by
  have h1 : x - 1 < 2 ^ j := by omega
  simp only [heapCount, Nat.div_eq_of_lt hlt, Nat.mod_eq_of_lt hlt,
    Nat.div_eq_of_lt h1, Nat.mod_eq_of_lt h1]
  omega

theorem rolloutCount_zero {j : Nat} {p : List Nat} (hz : ∀ x ∈ p, x = 0) :
    rolloutCount j p = 0 := by
  induction p with
  | nil => rfl
  | cons h t ih =>
    have hh : h = 0 := hz h (List.mem_cons_self ..)
    have ht : ∀ x ∈ t, x = 0 := fun x hx => hz x (List.mem_cons_of_mem _ hx)
    simp [rolloutCount, heapCount, hh] at ih ⊢
    exact ih ht

/-- Each policy move lowers the algebraic count by exactly one. -/
theorem policyMove_count {j : Nat} {p q : List Nat} (hm : PolicyMove j p q) :
    rolloutCount j q + 1 = rolloutCount j p := by
  rcases hm with ⟨pre, x, post, rfl, hx, rfl⟩ | ⟨hall, pre, x, post, rfl, hx, rfl⟩
  · rw [rolloutCount_split, rolloutCount_split, ← heapCount_sub_pow hx]
    omega
  · have hlt : x < 2 ^ j := hall x (by simp)
    rw [rolloutCount_split, rolloutCount_split, ← heapCount_sub_one hx hlt]
    omega

/-- EXECUTION COUNT: every complete run of `pi_j`, under any tie-breaking rule,
    has exactly `sum_h (h / 2^j + h % 2^j)` moves. -/
theorem run_length {j : Nat} {p : List Nat} {n : Nat} (hr : Run j p n) :
    n = rolloutCount j p := by
  induction hr with
  | done p hz => exact (rolloutCount_zero hz).symm
  | step p q n hm _ ih => rw [ih, policyMove_count hm]

/-- PARITY OF EXECUTION: the number of moves of any complete run of `pi_j` has
    low bit equal to the channel value of the nim-sum
    (bit 0 for j = 0; bit j XOR bit 0 for j ≥ 1). -/
theorem run_parity {j : Nat} {p : List Nat} {n : Nat} (hr : Run j p n) :
    n.testBit 0 = channel j (nimSum p) := by
  rw [run_length hr]
  exact rollout_count_channel j p

/-! ### A concrete deterministic simulator (first eligible heap), and its correctness -/

/-- Subtract `u` from the first heap of size ≥ `u`. -/
def subFirstGe (u : Nat) : List Nat → Option (List Nat)
  | [] => none
  | h :: t => if u ≤ h then some ((h - u) :: t) else (subFirstGe u t).map (h :: ·)

/-- Subtract 1 from the first nonzero heap. -/
def subFirstPos : List Nat → Option (List Nat)
  | [] => none
  | h :: t => if 0 < h then some ((h - 1) :: t) else (subFirstPos t).map (h :: ·)

/-- One step of `pi_j` with first-eligible tie-breaking; `none` means no move. -/
def policyStep (j : Nat) (p : List Nat) : Option (List Nat) :=
  match subFirstGe (2 ^ j) p with
  | some q => some q
  | none => subFirstPos p

theorem subFirstGe_some {u : Nat} {p q : List Nat} (h : subFirstGe u p = some q) :
    ∃ pre x post, p = pre ++ x :: post ∧ u ≤ x ∧ q = pre ++ (x - u) :: post := by
  induction p generalizing q with
  | nil => simp [subFirstGe] at h
  | cons x t ih =>
    by_cases hx : u ≤ x
    · simp only [subFirstGe, hx, if_true, Option.some.injEq] at h
      exact ⟨[], x, t, rfl, hx, h.symm⟩
    · simp only [subFirstGe, hx, if_false] at h
      cases ht : subFirstGe u t with
      | none => simp [ht] at h
      | some a =>
        simp only [ht, Option.map_some, Option.some.injEq] at h
        obtain ⟨pre, y, post, h1, h2, h3⟩ := ih ht
        exact ⟨x :: pre, y, post, by simp [h1], h2, by rw [← h, h3]; rfl⟩

theorem subFirstGe_none {u : Nat} {p : List Nat} (h : subFirstGe u p = none) :
    ∀ x ∈ p, x < u := by
  induction p with
  | nil => simp
  | cons x t ih =>
    by_cases hx : u ≤ x
    · simp [subFirstGe, hx] at h
    · simp only [subFirstGe, hx, if_false] at h
      cases ht : subFirstGe u t with
      | some a => simp [ht] at h
      | none =>
        intro y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · omega
        · exact ih ht y hy

theorem subFirstPos_some {p q : List Nat} (h : subFirstPos p = some q) :
    ∃ pre x post, p = pre ++ x :: post ∧ 0 < x ∧ q = pre ++ (x - 1) :: post := by
  induction p generalizing q with
  | nil => simp [subFirstPos] at h
  | cons x t ih =>
    by_cases hx : 0 < x
    · simp only [subFirstPos, hx, if_true, Option.some.injEq] at h
      exact ⟨[], x, t, rfl, hx, h.symm⟩
    · simp only [subFirstPos, hx, if_false] at h
      cases ht : subFirstPos t with
      | none => simp [ht] at h
      | some a =>
        simp only [ht, Option.map_some, Option.some.injEq] at h
        obtain ⟨pre, y, post, h1, h2, h3⟩ := ih ht
        exact ⟨x :: pre, y, post, by simp [h1], h2, by rw [← h, h3]; rfl⟩

theorem subFirstPos_none {p : List Nat} (h : subFirstPos p = none) :
    ∀ x ∈ p, x = 0 := by
  induction p with
  | nil => simp
  | cons x t ih =>
    by_cases hx : 0 < x
    · simp [subFirstPos, hx] at h
    · simp only [subFirstPos, hx, if_false] at h
      cases ht : subFirstPos t with
      | some a => simp [ht] at h
      | none =>
        intro y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · omega
        · exact ih ht y hy

theorem policyStep_some {j : Nat} {p q : List Nat} (h : policyStep j p = some q) :
    PolicyMove j p q := by
  unfold policyStep at h
  cases hg : subFirstGe (2 ^ j) p with
  | some a =>
    rw [hg] at h
    cases h
    exact Or.inl (subFirstGe_some hg)
  | none =>
    rw [hg] at h
    exact Or.inr ⟨subFirstGe_none hg, subFirstPos_some h⟩

theorem policyStep_none {j : Nat} {p : List Nat} (h : policyStep j p = none) :
    ∀ x ∈ p, x = 0 := by
  unfold policyStep at h
  cases hg : subFirstGe (2 ^ j) p with
  | some a => rw [hg] at h; cases h
  | none => rw [hg] at h; exact subFirstPos_none h

/-- The simulator: apply `policyStep` until no move is available, counting moves.
    Termination is justified by `policyMove_count`. -/
def rolloutMoves (j : Nat) (p : List Nat) : Nat :=
  match h : policyStep j p with
  | none => 0
  | some q => rolloutMoves j q + 1
termination_by rolloutCount j p
decreasing_by
  have := policyMove_count (policyStep_some h)
  omega

/-- The simulator's trace is a complete run of `pi_j`. -/
theorem rolloutMoves_run (j : Nat) (p : List Nat) : Run j p (rolloutMoves j p) := by
  induction p using rolloutMoves.induct j with
  | case1 p h =>
    rw [rolloutMoves, h]
    exact Run.done p (policyStep_none h)
  | case2 p q h ih =>
    rw [rolloutMoves, h]
    exact Run.step p q _ (policyStep_some h) ih

/-- The simulated rollout length equals the algebraic count. -/
theorem rolloutMoves_eq (j : Nat) (p : List Nat) :
    rolloutMoves j p = rolloutCount j p :=
  run_length (rolloutMoves_run j p)

/-- Per-heap execution count (single-heap board). -/
theorem rolloutMoves_single (j h : Nat) :
    rolloutMoves j [h] = h / 2 ^ j + h % 2 ^ j := by
  rw [rolloutMoves_eq]
  simp [rolloutCount, heapCount]

/-- Parity of the simulated rollout length equals the channel of the nim-sum. -/
theorem rolloutMoves_parity (j : Nat) (p : List Nat) :
    (rolloutMoves j p).testBit 0 = channel j (nimSum p) :=
  run_parity (rolloutMoves_run j p)

/-! ## Part B: a decreasing heap exists when the nim-sum is nonzero -/

/-- Two numbers agreeing above bit `k`, with bit `k` 0 in `a` and 1 in `b`, satisfy `a < b`. -/
theorem lt_of_top_testBit {a b k : Nat}
    (hk : a.testBit k = false) (hb : b.testBit k = true)
    (hi : ∀ i, k < i → a.testBit i = b.testBit i) : a < b := by
  have hq : a / 2 ^ (k + 1) = b / 2 ^ (k + 1) := by
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_div_two_pow, Nat.testBit_div_two_pow]
    exact hi _ (by omega)
  have hra : a % 2 ^ (k + 1) < 2 ^ k := by
    apply Nat.lt_pow_two_of_testBit
    intro i hi'
    rw [Nat.testBit_mod_two_pow]
    by_cases hik : i = k
    · subst hik; simp [hk]
    · have : ¬ i < k + 1 := by omega
      simp [this]
  have hrb : 2 ^ k ≤ b % 2 ^ (k + 1) := by
    apply Nat.ge_two_pow_of_testBit
    rw [Nat.testBit_mod_two_pow]
    simp [hb]
  rw [← Nat.div_add_mod a (2 ^ (k + 1)), ← Nat.div_add_mod b (2 ^ (k + 1)), hq]
  exact Nat.add_lt_add_left (Nat.lt_of_lt_of_le hra hrb) _

theorem exists_heap_testBit {p : List Nat} {k : Nat}
    (h : (nimSum p).testBit k = true) : ∃ x ∈ p, x.testBit k = true := by
  induction p with
  | nil => simp [nimSum] at h
  | cons x t ih =>
    simp only [nimSum, Nat.testBit_xor] at h
    cases hx : x.testBit k with
    | true => exact ⟨x, List.mem_cons_self .., hx⟩
    | false =>
      rw [hx, Bool.false_xor] at h
      obtain ⟨y, hy, hyk⟩ := ih h
      exact ⟨y, List.mem_cons_of_mem _ hy, hyk⟩

/-- LEGAL MOVE TO ZERO: if the nim-sum `s` is nonzero, some heap `x` has
    `x ^^^ s < x`; replacing it by `x ^^^ s` is a legal Nim move and, by
    `move_to_zero_algebra`, yields nim-sum zero. -/
theorem exists_decreasing_heap (p : List Nat) (hs : nimSum p ≠ 0) :
    ∃ pre x post, p = pre ++ x :: post ∧ x ^^^ nimSum p < x ∧
      nimSum (pre ++ (x ^^^ nimSum p) :: post) = 0 := by
  let s := nimSum p
  let k := s.log2
  have htop : s.testBit k = true := by
    cases hb : s.testBit k with
    | true => rfl
    | false =>
      exfalso
      have hlt : s < 2 ^ k := by
        apply Nat.lt_pow_two_of_testBit
        intro i hi
        by_cases hik : i = k
        · subst hik; exact hb
        · apply Nat.testBit_lt_two_pow
          exact Nat.lt_of_lt_of_le Nat.lt_log2_self (Nat.pow_le_pow_right (by decide) (by omega))
      exact absurd (Nat.log2_self_le hs) (Nat.not_le.mpr hlt)
  have habove : ∀ i, k < i → s.testBit i = false := by
    intro i hi
    apply Nat.testBit_lt_two_pow
    exact Nat.lt_of_lt_of_le Nat.lt_log2_self (Nat.pow_le_pow_right (by decide) (by omega))
  obtain ⟨x, hxmem, hxk⟩ := exists_heap_testBit htop
  have hlt : x ^^^ s < x := by
    apply lt_of_top_testBit (k := k)
    · rw [Nat.testBit_xor, hxk, htop]; rfl
    · exact hxk
    · intro i hi
      rw [Nat.testBit_xor, habove i hi, Bool.xor_false]
  obtain ⟨pre, post, rfl⟩ := List.append_of_mem hxmem
  exact ⟨pre, x, post, rfl, hlt, move_to_zero_algebra pre post x⟩

/-! ## A sharper form of the zero-predecessor caveat -/

/-- Matching deltas alone never force a zero result: the universal statement is false. -/
theorem matching_deltas_do_not_force_zero :
    ¬ ∀ q q' r : Nat, q ^^^ q' = q' ^^^ r → r = 0 := by
  intro h
  have := h 1 3 1 (by decide)
  exact absurd this (by decide)

#print axioms policyMove_legal
#print axioms rolloutCount_split
#print axioms heapCount_sub_pow
#print axioms heapCount_sub_one
#print axioms rolloutCount_zero
#print axioms policyMove_count
#print axioms run_length
#print axioms run_parity
#print axioms subFirstGe_some
#print axioms subFirstGe_none
#print axioms subFirstPos_some
#print axioms subFirstPos_none
#print axioms policyStep_some
#print axioms policyStep_none
#print axioms rolloutMoves_run
#print axioms rolloutMoves_eq
#print axioms rolloutMoves_single
#print axioms rolloutMoves_parity
#print axioms lt_of_top_testBit
#print axioms exists_heap_testBit
#print axioms exists_decreasing_heap
#print axioms matching_deltas_do_not_force_zero

end Rollout
end NimAudit
