import SelectCircuit

/- Phase 4, Priority 4: LOCAL two-frame delta and restoration circuits, and the
   bounded-change difference lemma.  Written by Claude (10 October 2026).
   Lean 4.26.0, core/Std only.

   Input: two frames Q (wires below B·N) and Q' (wires B·N … 2B·N − 1), each in the
   `boardBits` layout.  Nothing here computes a global nim-sum: every circuit is built
   from per-heap bit comparisons.
   * changed-row detection  `chgC i`  (OR over the block of bitwise XORs);
   * single-change delta    `dC q`    (OR over heaps of the bit-q XORs) — equal to
     nim(Q) ⊕ nim(Q') whenever the frames differ in at most one heap (`OneChange`,
     implied by any legal move);
   * restoration circuit    `restC`   = variable-target selector on Q' with σ := δ;
     under the zero-predecessor / legal-transition promise it outputs exactly the
     move of `NimGame.restore` (whose specification uses global nim-sums) and that
     move is legal and restores nim-sum 0;
   * bounded-change delta   `bdC t q` for any constant t: exact counting circuits
     "at least k of the heaps differ in bit q" give the parity of the at most t
     differing heaps; equal to nim(Q) ⊕ nim(Q') when at most t heaps changed
     (paper Lemma "bounded-change differences"), with depth 2t + 8 and size
     (2t+6)·U^(3t+6), U = N + t + 11. -/

namespace NimAudit
namespace LocalRestore

open Game Rollout Prob Attain Recurrent AC0 AC0.Circ CorrBridge AttainCircuit Bridge SelectCircuit

/-- Two-frame input vector. -/
def tf (B N : Nat) (Q Q' : List Nat) : Nat → Bool := fun j =>
  if j < B * N then boardBits B Q j else boardBits B Q' (j - B * N)

section Frames
variable {B N : Nat} {Q Q' : List Nat}

theorem tf_left {j : Nat} (hj : j < B * N) : tf B N Q Q' j = boardBits B Q j := by simp [tf, hj]

theorem tf_right (j : Nat) : tf B N Q Q' (B * N + j) = boardBits B Q' j := by
  simp only [tf, if_neg (show ¬ (B * N + j < B * N) by omega), Nat.add_sub_cancel_left]

theorem tf_heapL (hQ : Q.length = N) {i p : Nat} (hi : i < N) (hp : p < B) :
    tf B N Q Q' (B * i + p) = (Q.getD i 0).testBit (B - 1 - p) := by
  rw [tf_left (heap_lt hi hp), boardBits_heap hQ hi hp]

theorem tf_heapR (hQ' : Q'.length = N) {i p : Nat} (hi : i < N) (hp : p < B) :
    tf B N Q Q' (B * N + (B * i + p)) = (Q'.getD i 0).testBit (B - 1 - p) := by
  rw [tf_right, boardBits_heap hQ' hi hp]

end Frames

/-- Bitwise XOR of heap i of the two frames at big-endian position p. -/
def yC (B N i p : Nat) : Circ := xor2 (input (B * i + p)) (input (B * N + (B * i + p)))

/-- Heap i changed between the frames. -/
def chgC (B N i : Nat) : Circ := or ((List.range B).map (yC B N i))

/-- Little-endian bit q of the single-change delta: OR over heaps of the bit-q XORs. -/
def dC (B N q : Nat) : Circ := if q < B then or ((List.range N).map (fun i => yC B N i (B - 1 - q))) else const false

theorem yC_eval {B N : Nat} {Q Q' : List Nat} (hQ : Q.length = N) (hQ' : Q'.length = N) {i p : Nat}
    (hi : i < N) (hp : p < B) :
    eval (tf B N Q Q') (yC B N i p) = ((Q.getD i 0).testBit (B - 1 - p) != (Q'.getD i 0).testBit (B - 1 - p)) := by
  simp only [yC, eval_xor2, eval_input, tf_heapL hQ hi hp, tf_heapR hQ' hi hp]
  try (cases (Q.getD i 0).testBit (B - 1 - p) <;> cases (Q'.getD i 0).testBit (B - 1 - p) <;> rfl)

theorem testBit_ne_iff {x y B : Nat} (hx : x < 2 ^ B) (hy : y < 2 ^ B) :
    x ≠ y ↔ ∃ k < B, x.testBit k ≠ y.testBit k := by
  constructor
  · intro h
    apply Classical.byContradiction; intro hall
    apply h
    apply Nat.eq_of_testBit_eq
    intro k
    rcases Nat.lt_or_ge k B with hk | hk
    · apply Classical.byContradiction; intro hne; exact hall ⟨k, hk, hne⟩
    · rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) hk)),
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hy (Nat.pow_le_pow_right (by decide) hk))]
  · rintro ⟨k, _, hk⟩ h; subst h; exact hk rfl

/-- CHANGED-ROW DETECTION. -/
theorem chgC_eval {B N : Nat} {Q Q' : List Nat} (hQ : Q.length = N) (hQ' : Q'.length = N)
    (hw : Width B Q) (hw' : Width B Q') {i : Nat} (hi : i < N) :
    eval (tf B N Q Q') (chgC B N i) = decide (Q.getD i 0 ≠ Q'.getD i 0) := by
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_iff, testBit_ne_iff (getD_lt_of_width hQ hw hi) (getD_lt_of_width hQ' hw' hi)]
  simp only [chgC, eval_or, List.any_map, List.any_eq_true, List.mem_range, Function.comp_apply]
  constructor
  · rintro ⟨p, hp, h⟩
    rw [yC_eval hQ hQ' hi hp] at h
    refine ⟨B - 1 - p, by omega, ?_⟩
    simpa using h
  · rintro ⟨k, hk, h⟩
    refine ⟨B - 1 - k, by omega, ?_⟩
    rw [yC_eval hQ hQ' hi (by omega), show B - 1 - (B - 1 - k) = k by omega]
    simpa using h

/-! ## Single-change delta -/

/-- The frames differ in at most one heap. -/
def OneChange (Q Q' : List Nat) : Prop :=
  Q = Q' ∨ ∃ pre x post y, Q = pre ++ x :: post ∧ Q' = pre ++ y :: post

theorem oneChange_of_move {Q Q' : List Nat} (h : Move Q Q') : OneChange Q Q' := by
  obtain ⟨pre, x, post, y, h1, h2, _⟩ := h
  exact Or.inr ⟨pre, x, post, y, h1, h2⟩

theorem nimSum_split (pre post : List Nat) (x : Nat) :
    nimSum (pre ++ x :: post) = nimSum pre ^^^ (x ^^^ nimSum post) := by
  rw [NimAudit.nimSum_append]; rfl

theorem delta_oneChange {pre post : List Nat} (x y : Nat) :
    nimSum (pre ++ x :: post) ^^^ nimSum (pre ++ y :: post) = x ^^^ y := by
  rw [nimSum_split, nimSum_split]
  apply Nat.eq_of_testBit_eq; intro k
  simp only [Nat.testBit_xor]
  cases (nimSum pre).testBit k <;> cases x.testBit k <;> cases y.testBit k <;>
    cases (nimSum post).testBit k <;> rfl

theorem getD_split (pre post : List Nat) (x i : Nat) :
    (pre ++ x :: post).getD i 0 =
      if i < pre.length then pre.getD i 0 else if i = pre.length then x else post.getD (i - pre.length - 1) 0 := by
  simp only [List.getD_eq_getElem?_getD]
  by_cases h1 : i < pre.length
  · simp [h1, List.getElem?_append_left h1]
  · rw [List.getElem?_append_right (by omega)]
    by_cases h2 : i = pre.length
    · subst h2; simp
    · simp only [h1, h2, if_false]
      rw [show i - pre.length = (i - pre.length - 1) + 1 by omega, List.getElem?_cons_succ]
      simp only [Nat.add_sub_cancel]

/-- The local delta value read off the circuit (no promise). -/
def localDelta (B N : Nat) (Q Q' : List Nat) : Nat :=
  ofBits B (fun q => (List.range N).any (fun i => (Q.getD i 0).testBit q != (Q'.getD i 0).testBit q))

theorem dC_eval {B N : Nat} {Q Q' : List Nat} (hQ : Q.length = N) (hQ' : Q'.length = N) (q : Nat) :
    eval (tf B N Q Q') (dC B N q) = (localDelta B N Q Q').testBit q := by
  unfold dC localDelta
  rw [testBit_ofBits]
  by_cases hq : q < B
  · simp only [hq, if_true, decide_true, Bool.true_and, eval_or, List.any_map]
    apply Bool.eq_iff_iff.mpr
    simp only [List.any_eq_true, List.mem_range, Function.comp_apply]
    constructor
    · rintro ⟨i, hi, h⟩
      refine ⟨i, hi, ?_⟩
      rwa [yC_eval hQ hQ' hi (by omega), show B - 1 - (B - 1 - q) = q by omega] at h
    · rintro ⟨i, hi, h⟩
      refine ⟨i, hi, ?_⟩
      rwa [yC_eval hQ hQ' hi (by omega), show B - 1 - (B - 1 - q) = q by omega]
  · simp [hq]

/-- SINGLE-CHANGE DELTA: on frames differing in at most one heap the local delta is
    nim(Q) ⊕ nim(Q'). -/
theorem localDelta_eq {B N : Nat} {Q Q' : List Nat} (hQ : Q.length = N) (hQ' : Q'.length = N)
    (hw : Width B Q) (hw' : Width B Q') (h1 : OneChange Q Q') :
    localDelta B N Q Q' = nimSum Q ^^^ nimSum Q' := by
  apply ofBits_testBit_eq (Nat.xor_lt_two_pow (nimSum_lt hw) (nimSum_lt hw'))
  intro q _
  rcases h1 with rfl | ⟨pre, x, post, y, rfl, rfl⟩
  · simp
  · rw [delta_oneChange, Nat.testBit_xor]
    have hN : N = pre.length + 1 + post.length := by rw [← hQ]; simp; omega
    apply Bool.eq_iff_iff.mpr
    simp only [List.any_eq_true, List.mem_range, getD_split]
    constructor
    · rintro ⟨i, _, hi⟩
      by_cases h1 : i < pre.length
      · simp [h1] at hi
      · by_cases h2 : i = pre.length
        · simpa [h2] using hi
        · simp [h1, h2] at hi
    · intro h
      exact ⟨pre.length, by omega, by simpa using h⟩

/-! ## The restoration circuit -/

/-- Board wires read Q'; σ wires read the local delta circuits. -/
def restSubst (B N : Nat) : Nat → Circ := fun w => if w < B * N then input (B * N + w) else dC B N (w - B * N)

def restC (B N : Nat) : RCirc := substR (restSubst B N) (varSel B N)

theorem rest_inputs {B N : Nat} {Q Q' : List Nat} (hQ : Q.length = N) (hQ' : Q'.length = N) :
    (fun w => eval (tf B N Q Q') (restSubst B N w)) = selIn B N Q' (localDelta B N Q Q') := by
  funext w
  unfold restSubst selIn
  by_cases hw : w < B * N
  · simp only [hw, if_true, eval_input, tf_right]
  · simp only [hw, if_false]
    exact dC_eval hQ hQ' _

/-- RESTORATION CIRCUIT (no promise): it outputs `attainT δ Q'` for the local delta δ. -/
theorem restC_eval {B N : Nat} {Q Q' : List Nat} (hQ : Q.length = N) (hQ' : Q'.length = N)
    (hw' : Width B Q') :
    selReadout (restC B N) (tf B N Q Q') = attainT (localDelta B N Q Q') Q' := by
  unfold restC
  rw [selReadout_subst, rest_inputs hQ hQ']
  exact varSel_correct hQ' hw' (ofBits_lt B _)

theorem cancelFirst_eq (t : Nat) : ∀ P : List Nat, cancelFirst t P = applyM P (cancelIdx t P)
  | [] => rfl
  | x :: rest => by
    by_cases h : x ^^^ t < x
    · simp [cancelFirst, cancelIdx, h, applyM]
    · simp only [cancelFirst, cancelIdx, h, if_false]
      rw [applyM_shift, cancelFirst_eq t rest]

/-- LOCAL RESTORATION EQUIVALENCE: under the zero-predecessor / legal-transition
    promise (nim(Q) = 0 and Q → Q' a legal move), the purely local circuit outputs a
    move (i, v) whose application is exactly `NimGame.restore Q Q'`; the move is legal
    and restores nim-sum 0. -/
theorem restore_equiv {B N : Nat} {Q Q' : List Nat} (hQ : Q.length = N) (hQ' : Q'.length = N)
    (hw : Width B Q) (hw' : Width B Q') (h0 : nimSum Q = 0) (hm : Move Q Q') :
    ∃ i v, selReadout (restC B N) (tf B N Q Q') = some (i, v) ∧
      restore Q Q' = some (Q'.set i v) ∧ Move Q' (Q'.set i v) ∧ nimSum (Q'.set i v) = 0 := by
  rw [restC_eval hQ hQ' hw', localDelta_eq hQ hQ' hw hw' (oneChange_of_move hm)]
  obtain ⟨R, hR, hmR, hzR⟩ := restore_correct h0 hm
  have hR' := hR
  unfold restore at hR'
  rw [cancelFirst_eq] at hR'
  cases hc : cancelIdx (nimSum Q ^^^ nimSum Q') Q' with
  | none => rw [hc] at hR'; cases hR'
  | some m =>
    obtain ⟨i, v⟩ := m
    rw [hc] at hR'
    simp only [applyM, Option.some.injEq] at hR'
    subst hR'
    refine ⟨i, v, ?_, hR, hmR, hzR⟩
    unfold attainT; rw [hc]

/-! ## Bounded-change differences (any constant t) -/

/-- Number of indices below n satisfying p. -/
def cntR (p : Nat → Bool) (n : Nat) : Nat := ((List.range n).filter p).length

theorem cntR_zero (p : Nat → Bool) : cntR p 0 = 0 := rfl

theorem cntR_succ (p : Nat → Bool) (n : Nat) : cntR p (n + 1) = cntR p n + (if p n then 1 else 0) := by
  unfold cntR
  rw [List.range_succ, List.filter_append, List.length_append]
  cases h : p n <;> simp [h]

theorem cntR_mono {p p' : Nat → Bool} (n : Nat) (h : ∀ i < n, p i = true → p' i = true) :
    cntR p n ≤ cntR p' n := by
  induction n with
  | zero => simp [cntR_zero]
  | succ n ih =>
    rw [cntR_succ, cntR_succ]
    have := ih (fun i hi => h i (by omega))
    cases hp : p n
    · simp only [Bool.false_eq_true, if_false]; split <;> omega
    · simp [h n (by omega) hp]; omega

/-- "At least k of y 0, …, y (n-1) are true". -/
def atLeastC (y : Nat → Circ) : Nat → Nat → Circ
  | 0, _ => const true
  | k + 1, n => or ((List.range n).map (fun i => and [y i, atLeastC y k i]))

theorem atLeastC_eval (z : Nat → Bool) (y : Nat → Circ) :
    ∀ k n, eval z (atLeastC y k n) = decide (k ≤ cntR (fun i => eval z (y i)) n)
  | 0, n => by simp [atLeastC]
  | k + 1, n => by
    induction n with
    | zero => simp [atLeastC, cntR_zero]
    | succ n ih =>
      have e : atLeastC y (k + 1) (n + 1) =
          or ((List.range n).map (fun i => and [y i, atLeastC y k i]) ++ [and [y n, atLeastC y k n]]) := by
        simp [atLeastC, List.range_succ]
      rw [e, eval_or, List.any_append, cntR_succ]
      have ih' : ((List.range n).map (fun i => and [y i, atLeastC y k i])).any (eval z) =
          decide (k + 1 ≤ cntR (fun i => eval z (y i)) n) := by
        rw [← ih]; simp [atLeastC]
      rw [ih']
      simp only [List.any_cons, List.any_nil, Bool.or_false, eval_and, List.all_cons, List.all_nil,
        Bool.and_true, atLeastC_eval z y k n]
      cases hy : eval z (y n) <;> simp [hy] <;> omega

/-- Parity of the number of true y_i, valid when at most t are true. -/
def parC (y : Nat → Circ) (t n : Nat) : Circ :=
  or ((List.range (t + 1)).map (fun k =>
    if k % 2 = 1 then and [atLeastC y k n, not (atLeastC y (k + 1) n)] else const false))

theorem parC_eval (z : Nat → Bool) (y : Nat → Circ) (t n : Nat)
    (ht : cntR (fun i => eval z (y i)) n ≤ t) :
    eval z (parC y t n) = decide (cntR (fun i => eval z (y i)) n % 2 = 1) := by
  generalize hc : cntR (fun i => eval z (y i)) n = c at ht
  apply Bool.eq_iff_iff.mpr
  simp only [parC, eval_or, List.any_map, List.any_eq_true, List.mem_range, Function.comp_apply,
    decide_eq_true_iff]
  constructor
  · rintro ⟨k, _, hk⟩
    by_cases hodd : k % 2 = 1
    · simp only [hodd, if_true, eval_and, List.all_cons, List.all_nil, Bool.and_true, eval_not,
        atLeastC_eval, hc, Bool.and_eq_true, decide_eq_true_iff, Bool.not_eq_true',
        decide_eq_false_iff_not] at hk
      have : k = c := by omega
      subst this; exact hodd
    · simp [hodd] at hk
  · intro h
    refine ⟨c, by omega, ?_⟩
    simp [h, atLeastC_eval, hc]

/-- Little-endian bit q of the bounded-change delta (t = maximum number of changed heaps). -/
def bdC (B N t q : Nat) : Circ := if q < B then parC (fun i => yC B N i (B - 1 - q)) t N else const false

/-- Parity of the bit-q differences equals bit q of nim(Q) ⊕ nim(Q'). -/
theorem nimSum_xor_testBit : ∀ (Q Q' : List Nat), Q.length = Q'.length → ∀ q,
    (nimSum Q ^^^ nimSum Q').testBit q =
      decide (cntR (fun i => (Q.getD i 0).testBit q != (Q'.getD i 0).testBit q) Q.length % 2 = 1)
  | [], [], _, q => by simp [nimSum, cntR_zero]
  | x :: Q, y :: Q', hl, q => by
    have hl' : Q.length = Q'.length := by simpa using hl
    have ih := nimSum_xor_testBit Q Q' hl' q
    have hshift : cntR (fun i => ((x :: Q).getD i 0).testBit q != ((y :: Q').getD i 0).testBit q)
        (Q.length + 1) = (if x.testBit q != y.testBit q then 1 else 0) +
          cntR (fun i => (Q.getD i 0).testBit q != (Q'.getD i 0).testBit q) Q.length := by
      unfold cntR
      rw [List.range_succ_eq_map, List.filter_cons, List.filter_map]
      simp only [List.getD_cons_zero, Function.comp_def, List.getD_cons_succ]
      by_cases hc : (x.testBit q != y.testBit q) = true
      · simp only [hc, if_true, List.length_cons, List.length_map]; omega
      · simp only [hc, Bool.false_eq_true, if_false, List.length_map]; omega
    simp only [List.length_cons]
    simp only [hshift]
    have e : (nimSum (x :: Q) ^^^ nimSum (y :: Q')).testBit q =
        xor (x.testBit q != y.testBit q) ((nimSum Q ^^^ nimSum Q').testBit q) := by
      simp only [nimSum, Nat.testBit_xor]
      cases x.testBit q <;> cases y.testBit q <;> cases (nimSum Q).testBit q <;>
        cases (nimSum Q').testBit q <;> rfl
    rw [e, ih]
    generalize cntR (fun i => (Q.getD i 0).testBit q != (Q'.getD i 0).testBit q) Q.length = c
    cases hxy : (x.testBit q != y.testBit q)
    · simp only [Bool.false_xor, Bool.false_eq_true, if_false, Nat.zero_add]
    · simp only [Bool.true_xor, if_true]
      by_cases hc : c % 2 = 1
      · have : ¬ (1 + c) % 2 = 1 := by omega
        simp [hc, this]
      · have : (1 + c) % 2 = 1 := by omega
        simp [hc, this]
  | [], _ :: _, hl, _ => by simp at hl
  | _ :: _, [], hl, _ => by simp at hl

/-- BOUNDED-CHANGE DIFFERENCES: if at most t heaps changed, the delta circuits compute
    nim(Q) ⊕ nim(Q') exactly. -/
theorem bdC_eval {B N t : Nat} {Q Q' : List Nat} (hQ : Q.length = N) (hQ' : Q'.length = N)
    (hw : Width B Q) (hw' : Width B Q')
    (ht : cntR (fun i => decide (Q.getD i 0 ≠ Q'.getD i 0)) N ≤ t) (q : Nat) :
    eval (tf B N Q Q') (bdC B N t q) = (nimSum Q ^^^ nimSum Q').testBit q := by
  unfold bdC
  by_cases hq : q < B
  · simp only [hq, if_true]
    have hyc : (fun i => eval (tf B N Q Q') (yC B N i (B - 1 - q))) =
        fun i => if i < N then ((Q.getD i 0).testBit q != (Q'.getD i 0).testBit q) else
          eval (tf B N Q Q') (yC B N i (B - 1 - q)) := by
      funext i
      by_cases hi : i < N
      · rw [if_pos hi, yC_eval hQ hQ' hi (by omega), show B - 1 - (B - 1 - q) = q by omega]
      · rw [if_neg hi]
    have hcnt : cntR (fun i => eval (tf B N Q Q') (yC B N i (B - 1 - q))) N =
        cntR (fun i => (Q.getD i 0).testBit q != (Q'.getD i 0).testBit q) N := by
      unfold cntR
      congr 1
      apply List.filter_congr
      intro i hi
      rw [yC_eval hQ hQ' (List.mem_range.mp hi) (by omega), show B - 1 - (B - 1 - q) = q by omega]
    have hle : cntR (fun i => (Q.getD i 0).testBit q != (Q'.getD i 0).testBit q) N ≤ t := by
      refine Nat.le_trans (cntR_mono N (fun i hi h => ?_)) ht
      simp only [bne_iff_ne, ne_eq] at h
      simp only [decide_eq_true_iff]
      intro he; rw [he] at h; exact h rfl
    rw [parC_eval _ _ t N (by rw [hcnt]; exact hle), hcnt,
      nimSum_xor_testBit Q Q' (by rw [hQ, hQ']) q, hQ]
  · simp only [hq, if_false, eval_const]
    rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (Nat.xor_lt_two_pow (nimSum_lt hw) (nimSum_lt hw'))
      (Nat.pow_le_pow_right (by decide) (by omega)))]

theorem bdDelta_eq {B N t : Nat} {Q Q' : List Nat} (hQ : Q.length = N) (hQ' : Q'.length = N)
    (hw : Width B Q) (hw' : Width B Q')
    (ht : cntR (fun i => decide (Q.getD i 0 ≠ Q'.getD i 0)) N ≤ t) :
    ofBits B (fun q => eval (tf B N Q Q') (bdC B N t q)) = nimSum Q ^^^ nimSum Q' :=
  ofBits_testBit_eq (Nat.xor_lt_two_pow (nimSum_lt hw) (nimSum_lt hw')) _
    (fun q _ => bdC_eval hQ hQ' hw hw' ht q)

/-! ## Resources -/

section Res
variable {B N : Nat}

theorem yC_res (i p : Nat) : depth (yC B N i p) ≤ 3 ∧ size (yC B N i p) ≤ 9 := by
  simp [yC, xor2, listMax]

theorem yC_max {i p : Nat} (hi : i < N) (hp : p < B) : maxInput (yC B N i p) ≤ 2 * (B * N) := by
  have := heap_lt (B := B) (N := N) hi hp
  simp [yC, xor2, listMax]; omega

theorem dC_res (q : Nat) : depth (dC B N q) ≤ 4 ∧ size (dC B N q) ≤ 10 * N + 1 ∧
    maxInput (dC B N q) ≤ 2 * (B * N) := by
  unfold dC
  by_cases hq : q < B
  · simp only [hq, if_true]
    refine ⟨?_, ?_, ?_⟩
    · apply depth_or_le; intro c hc; obtain ⟨i, _, rfl⟩ := List.mem_map.mp hc; exact (yC_res _ _).1
    · have := ControllerBits.size_or_le' (S := 9) (cs := (List.range N).map (fun i => yC B N i (B - 1 - q)))
        (by intro c hc; obtain ⟨i, _, rfl⟩ := List.mem_map.mp hc; exact (yC_res _ _).2)
      simp only [List.length_map, List.length_range] at this; omega
    · apply ControllerBits.maxInput_or_le; intro c hc
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hc
      exact yC_max (List.mem_range.mp hi) (by omega)
  · simp [hq]

theorem chgC_res {i : Nat} (hi : i < N) : depth (chgC B N i) ≤ 4 ∧ size (chgC B N i) ≤ 10 * B + 1 ∧
    maxInput (chgC B N i) ≤ 2 * (B * N) := by
  unfold chgC
  refine ⟨?_, ?_, ?_⟩
  · apply depth_or_le; intro c hc; obtain ⟨p, _, rfl⟩ := List.mem_map.mp hc; exact (yC_res _ _).1
  · have := ControllerBits.size_or_le' (S := 9) (cs := (List.range B).map (yC B N i))
      (by intro c hc; obtain ⟨p, _, rfl⟩ := List.mem_map.mp hc; exact (yC_res _ _).2)
    simp only [List.length_map, List.length_range] at this; omega
  · apply ControllerBits.maxInput_or_le; intro c hc
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hc
    exact yC_max hi (List.mem_range.mp hp)

/-- The restoration circuit: depth ≤ 17, polynomial size, reading only the two frames. -/
theorem restC_bound :
    SelBound (restC B N) N B (4 + 9 + 4)
      (12 * ((N + 2) * (B + 2) * (B * (2 * B + 3) + 9 + 2)) ^ 8 * (10 * N + 1 + 1)) (2 * (B * N)) := by
  apply substR_bound (restSubst B N) varSel_bound
  · intro w; unfold restSubst; split
    · simp
    · exact (dC_res _).1
  · intro w; unfold restSubst; split
    · simp
    · exact (dC_res _).2.1
  · intro w; unfold restSubst; split
    · simp; omega
    · exact (dC_res _).2.2

theorem atLeast_res {U dy : Nat} (hU : 2 ≤ U) (y : Nat → Circ) (hy : ∀ i, size (y i) ≤ U ∧ depth (y i) ≤ dy) :
    ∀ k n, n ≤ U → size (atLeastC y k n) ≤ (2 * k + 1) * U ^ (3 * k) ∧ depth (atLeastC y k n) ≤ 2 * k + dy
  | 0, n, _ => by simp [atLeastC]
  | k + 1, n, hn => by
    have hU1 : 1 ≤ U := by omega
    refine ⟨?_, ?_⟩
    · show size (or ((List.range n).map (fun i => and [y i, atLeastC y k i]))) ≤ _
      have e : (2 * (k + 1) + 1) * U ^ (3 * (k + 1)) = ((2 * k + 2) + 1) * U ^ ((3 * k + 2) + 1) := by
        congr 1
      rw [e]
      apply size_or_le hU1 (by simp; omega)
      intro c hc
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hc
      have hi' := List.mem_range.mp hi
      apply size_and_le hU1 (by simp; omega)
      intro c hc
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact lift1 hU1 (show size (y i) ≤ 1 * U ^ 1 by simp; exact (hy i).1) (by omega) (by omega)
      · exact lift1 hU1 (atLeast_res hU y hy k i (by omega)).1 (by omega) (by omega)
    · show depth (or ((List.range n).map (fun i => and [y i, atLeastC y k i]))) ≤ _
      refine Nat.le_trans (depth_or_le (D := 2 * k + dy + 1) ?_) (by omega)
      intro c hc
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hc
      have hi' := List.mem_range.mp hi
      apply depth_and_le
      intro c hc
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · have := (hy i).2; omega
      · have := (atLeast_res hU y hy k i (by omega)).2; omega

theorem atLeast_max (y : Nat → Circ) {M n0 : Nat} (hy : ∀ i < n0, maxInput (y i) ≤ M) :
    ∀ k n, n ≤ n0 → maxInput (atLeastC y k n) ≤ M
  | 0, _, _ => by simp [atLeastC]
  | k + 1, n, hn => by
    show maxInput (or ((List.range n).map (fun i => and [y i, atLeastC y k i]))) ≤ M
    apply ControllerBits.maxInput_or_le; intro c hc
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hc
    have hi' := List.mem_range.mp hi
    apply ControllerBits.maxInput_and_le; intro c hc
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact hy i (by omega)
    · exact atLeast_max y hy k i (by omega)

theorem parC_res {U dy : Nat} (hU : 2 ≤ U) (y : Nat → Circ) (hy : ∀ i, size (y i) ≤ U ∧ depth (y i) ≤ dy)
    (t n : Nat) (hn : n ≤ U) (ht : t + 1 ≤ U) :
    size (parC y t n) ≤ (2 * t + 6) * U ^ (3 * t + 6) ∧ depth (parC y t n) ≤ 2 * t + dy + 5 := by
  have hU1 : 1 ≤ U := by omega
  refine ⟨?_, ?_⟩
  · unfold parC
    have e : (2 * t + 6) * U ^ (3 * t + 6) = ((2 * t + 5) + 1) * U ^ ((3 * t + 5) + 1) := by congr 1
    rw [e]
    apply size_or_le hU1 (by simp; omega)
    intro c hc
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hc
    have hk' := List.mem_range.mp hk
    split
    · apply size_and_le hU1 (by simp; omega)
      intro c hc
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact lift1 hU1 (atLeast_res hU y hy k n hn).1 (by omega) (by omega)
      · exact lift1 hU1 (size_not_le hU1 (atLeast_res hU y hy (k + 1) n hn).1) (by omega) (by omega)
    · exact lift1 hU1 (show size (const false) ≤ 1 * U ^ 0 by simp) (by omega) (by omega)
  · unfold parC
    apply depth_or_le
    intro c hc
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hc
    have hk' := List.mem_range.mp hk
    split
    · apply depth_and_le
      intro c hc
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · have := (atLeast_res hU y hy k n hn).2; omega
      · simp only [depth_not]; have := (atLeast_res hU y hy (k + 1) n hn).2; omega
    · simp

/-- BOUNDED-CHANGE DELTA RESOURCES: depth ≤ 2t + 8 and size ≤ (2t+6)·U^(3t+6) with
    U = N + t + 11; inputs from the two frames only.  Constant depth and polynomial size
    for every fixed t. -/
theorem bdC_res (t q : Nat) :
    depth (bdC B N t q) ≤ 2 * t + 8 ∧ size (bdC B N t q) ≤ (2 * t + 6) * (N + t + 11) ^ (3 * t + 6) ∧
      maxInput (bdC B N t q) ≤ 2 * (B * N) := by
  unfold bdC
  by_cases hq : q < B
  · simp only [hq, if_true]
    have hy : ∀ i, size (yC B N i (B - 1 - q)) ≤ N + t + 11 ∧ depth (yC B N i (B - 1 - q)) ≤ 3 :=
      fun i => ⟨by have := (yC_res (B := B) (N := N) i (B - 1 - q)).2; omega, (yC_res i _).1⟩
    have h := parC_res (by omega) _ hy t N (by omega) (by omega)
    refine ⟨by omega, h.1, ?_⟩
    unfold parC
    apply ControllerBits.maxInput_or_le; intro c hc
    obtain ⟨k, _, rfl⟩ := List.mem_map.mp hc
    split
    · apply ControllerBits.maxInput_and_le; intro c hc
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hc
      have hyM : ∀ i < N, maxInput (yC B N i (B - 1 - q)) ≤ 2 * (B * N) := fun i hi => yC_max hi (by omega)
      rcases hc with rfl | rfl
      · exact atLeast_max _ hyM k N (Nat.le_refl _)
      · simp only [maxInput_not]; exact atLeast_max _ hyM (k + 1) N (Nat.le_refl _)
    · simp
  · simp only [hq, if_false, depth_const, size_const, maxInput_const]
    refine ⟨by omega, ?_, by omega⟩
    have h1 : 1 ≤ (N + t + 11) ^ (3 * t + 6) := Nat.pow_pos (by omega)
    exact Nat.le_trans h1 (Nat.le_mul_of_pos_left _ (by omega))

end Res


/-! ## Axiom audit -/

#print axioms tf_left
#print axioms tf_right
#print axioms tf_heapL
#print axioms tf_heapR
#print axioms yC_eval
#print axioms testBit_ne_iff
#print axioms chgC_eval
#print axioms oneChange_of_move
#print axioms nimSum_split
#print axioms delta_oneChange
#print axioms getD_split
#print axioms dC_eval
#print axioms localDelta_eq
#print axioms rest_inputs
#print axioms restC_eval
#print axioms cancelFirst_eq
#print axioms restore_equiv
#print axioms cntR_zero
#print axioms cntR_succ
#print axioms cntR_mono
#print axioms atLeastC_eval
#print axioms parC_eval
#print axioms nimSum_xor_testBit
#print axioms bdC_eval
#print axioms bdDelta_eq
#print axioms yC_res
#print axioms yC_max
#print axioms dC_res
#print axioms chgC_res
#print axioms restC_bound
#print axioms atLeast_res
#print axioms atLeast_max
#print axioms parC_res
#print axioms bdC_res
end LocalRestore
end NimAudit
