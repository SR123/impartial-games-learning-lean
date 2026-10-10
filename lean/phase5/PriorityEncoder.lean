import LocalRestore
import BinaryReadout

/- Phase 5, task 1: an explicit, resource-bounded priority encoder from selection
   readouts (RCirc: valid flag, N candidate flags, B value bits) to the paper's binary
   move format (BCirc: valid flag, r big-endian index bits, B big-endian value bits).
   Written by Claude (10 October 2026).  Lean 4.26.0, core/Std only.

   Construction (no semantic primitive):
     first_i   = s_i AND (AND_{k<i} NOT s_k)                       (AttainCircuit.firstC)
     index bit q (q < r, weight 2^(r-1-q)) = OR of first_i over i < N with bit r-1-q of i
     valid     = R.valid AND (OR_{i<N} s_i)
     value     = R.val unchanged.
   Correctness holds for EVERY input assignment (several true flags, no true flag,
   invalid readouts, N = 0, N = 1 with zero index width, N not a power of two), under
   the index-width condition N ≤ 2^r.  (The recurrent controller's counter uses the
   stricter N < 2^r, because its counter must also hold the end value N.)
   Resources: depth + 3, every formula of size ≤ 4·U^3 with U = (N+2)(S+2), the same
   input support; total output size ≤ (1 + r + B)·4·U^3. -/

namespace NimAudit
namespace PriorityEncoder

open Game Rollout Prob Attain Recurrent AC0 AC0.Circ CorrBridge AttainCircuit Bridge SelectCircuit
  BinReadout

/-- first_i over the flag list. -/
def firstF (sel : List Circ) (i : Nat) : Circ := firstC (getC sel) i

/-- Big-endian index bit q: OR of first_i over the indices i < N whose bit r-1-q is 1. -/
def idxBit (sel : List Circ) (N r q : Nat) : Circ :=
  or (((List.range N).filter (fun i => i.testBit (r - 1 - q))).map (firstF sel))

/-- THE PRIORITY ENCODER. -/
def encode (R : RCirc) (N r : Nat) : BCirc :=
  ⟨and [R.valid, or ((List.range N).map (getC R.sel))],
   (List.range r).map (idxBit R.sel N r),
   R.val⟩

/-- Binary-format semantics on an arbitrary input vector (an index ≥ N is invalid);
    on boards this is exactly `BinReadout.binReadoutOf`. -/
def binSem (S : BCirc) (N : Nat) (z : Nat → Bool) : Option (Nat × Nat) :=
  if eval z S.valid then
    if toNatBE (S.idx.map (eval z)) < N then
      some (toNatBE (S.idx.map (eval z)), toNatBE (S.val.map (eval z)))
    else none
  else none

theorem binReadoutOf_eq (B N : Nat) (R : Bool → BCirc) (P : List Nat) (b : Bool) :
    binReadoutOf B N R P b = binSem (R b) N (boardBits B P) := rfl

theorem flags_eq (sel : List Circ) (N : Nat) (hlen : sel.length = N) (z : Nat → Bool) :
    (List.range N).map (fun i => eval z (getC sel i)) = sel.map (eval z) := by
  apply List.ext_getElem
  · simp [hlen]
  · intro n h1 h2
    simp only [List.getElem_map, List.getElem_range, eval_getC]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
    rw [List.getElem?_eq_getElem (by simp at h2; omega)]
    rfl

theorem firstF_eval (sel : List Circ) {N : Nat} (hlen : sel.length = N) (z : Nat → Bool) {i : Nat}
    (hi : i < N) : eval z (firstF sel i) = decide (firstTrue (sel.map (eval z)) = some i) := by
  unfold firstF
  rw [firstC_eval (N := N) z (getC sel) hi, flags_eq sel N hlen z]

/-- PRIORITY-ENCODER CORRECTNESS, for every input assignment: the binary output decodes
    to exactly the selection readout (first true flag, value bits), and to `none` when
    the readout is invalid or no flag is true. -/
theorem encode_correct (R : RCirc) (N r : Nat) (hlen : R.sel.length = N) (hr : N ≤ 2 ^ r)
    (z : Nat → Bool) : binSem (encode R N r) N z = selReadout R z := by
  unfold binSem selReadout encode
  simp only
  by_cases hv : eval z R.valid = true
  · cases hft : firstTrue (R.sel.map (eval z)) with
    | none =>
      have hany : (R.sel.map (eval z)).any id = false := by
        have := firstTrue_isSome (R.sel.map (eval z)); rw [hft] at this; simpa using this.symm
      have hor : eval z (or ((List.range N).map (getC R.sel))) = false := by
        rw [eval_or, List.any_map]
        have e : ((List.range N).any (eval z ∘ getC R.sel)) = (R.sel.map (eval z)).any id := by
          rw [← flags_eq R.sel N hlen z, List.any_map]; rfl
        rw [e, hany]
      simp [hv, hor]
    | some i =>
      have hiN : i < N := by have := firstTrue_lt hft; simpa [hlen] using this
      have hflag : (R.sel.map (eval z)).getD i false = true := ((firstTrue_some_iff _ i).1 hft).2.1
      have hor : eval z (or ((List.range N).map (getC R.sel))) = true := by
        rw [eval_or, List.any_map]
        apply List.any_eq_true.mpr
        exact ⟨i, List.mem_range.mpr hiN, by simp only [Function.comp_apply, eval_getC]; exact hflag⟩
      have hidx : toNatBE (((List.range r).map (idxBit R.sel N r)).map (eval z)) = i := by
        rw [List.map_map]
        apply toNatBE_of_bits (Nat.lt_of_lt_of_le hiN hr)
        intro q _
        simp only [Function.comp_apply]
        apply Bool.eq_iff_iff.mpr
        simp only [idxBit, eval_or, List.any_map, List.any_eq_true, List.mem_filter, List.mem_range,
          Function.comp_apply]
        constructor
        · rintro ⟨i', ⟨hi', hb⟩, he⟩
          rw [firstF_eval R.sel hlen z hi', hft, decide_eq_true_iff] at he
          cases he; exact hb
        · intro hb
          exact ⟨i, ⟨hiN, hb⟩, by rw [firstF_eval R.sel hlen z hiN, hft]; simp⟩
      simp only [eval_and, List.all_cons, List.all_nil, hv, hor, Bool.and_true, if_true, hidx, hiN]
  · simp [hv]

/-! ## Resources -/

/-- Resource bounds for binary readout formulas on an arbitrary input support M. -/
structure BinBound (S : BCirc) (N B r D Sz M : Nat) : Prop where
  idx_len : S.idx.length = r
  val_len : S.val.length = B
  width : N ≤ 2 ^ r
  all : ∀ c ∈ S.valid :: (S.idx ++ S.val), depth c ≤ D ∧ size c ≤ Sz ∧ maxInput c ≤ M

/-- Total formula size of a binary readout (no sharing between output formulas). -/
def totalSize (S : BCirc) : Nat := size S.valid + (S.idx.map size).sum + (S.val.map size).sum

theorem totalSize_le {S : BCirc} {N B r D Sz M : Nat} (h : BinBound S N B r D Sz M) :
    totalSize S ≤ (1 + r + B) * Sz := by
  unfold totalSize
  have h1 := (h.all S.valid (by simp)).2.1
  have h2 := sum_le_len_mul (cs := S.idx) (S := Sz) (fun c hc => (h.all c (by simp [hc])).2.1)
  have h3 := sum_le_len_mul (cs := S.val) (S := Sz) (fun c hc => (h.all c (by simp [hc])).2.1)
  rw [h.idx_len] at h2; rw [h.val_len] at h3
  rw [Nat.add_mul, Nat.add_mul, Nat.one_mul]
  omega

/-- ENCODER RESOURCES: from source formulas of depth ≤ D, size ≤ S on inputs below M,
    every output formula has depth ≤ D + 3, size ≤ 4·((N+2)(S+2))^3 and inputs below M. -/
theorem encode_bound (R : RCirc) {N B r D S M : Nat} (hlen : R.sel.length = N) (hvl : R.val.length = B)
    (hr : N ≤ 2 ^ r)
    (hall : ∀ c ∈ R.valid :: (R.sel ++ R.val), depth c ≤ D ∧ size c ≤ S ∧ maxInput c ≤ M) :
    BinBound (encode R N r) N B r (D + 3) (4 * ((N + 2) * (S + 2)) ^ 3) M := by
  generalize hU : (N + 2) * (S + 2) = U
  have hNU : N + 2 ≤ U := by
    rw [← hU]; exact Nat.le_mul_of_pos_right (N + 2) (by omega)
  have hSU : S + 2 ≤ U := by
    rw [← hU]; exact Nat.le_mul_of_pos_left (S + 2) (by omega)
  have hU1 : 1 ≤ U := by omega
  have hsel : ∀ i < N, depth (getC R.sel i) ≤ D ∧ size (getC R.sel i) ≤ S ∧ maxInput (getC R.sel i) ≤ M :=
    fun i hi => hall _ (by simp [getC_mem (show i < R.sel.length by omega)])
  have hsel1 : ∀ i < N, size (getC R.sel i) ≤ 1 * U ^ 1 := fun i hi => by
    have := (hsel i hi).2.1; simp; omega
  have hF : ∀ i < N, depth (firstF R.sel i) ≤ D + 2 ∧ size (firstF R.sel i) ≤ 3 * U ^ 2 ∧
      maxInput (firstF R.sel i) ≤ M := by
    intro i hi
    refine ⟨dp_firstC (fun i' hi' => (hsel i' (by omega)).1),
      sz_firstC hU1 (by omega) (fun i' hi' => hsel1 i' (by omega)),
      mx_firstC (fun i' hi' => (hsel i' (by omega)).2.2)⟩
  refine ⟨by simp [encode], by simp [encode, hvl], hr, ?_⟩
  intro c hc
  simp only [encode, List.mem_cons, List.mem_append, List.mem_map, List.mem_range] at hc
  rcases hc with rfl | ⟨q, _, rfl⟩ | hcv
  · -- validity
    have hv := hall R.valid (by simp)
    refine ⟨?_, ?_, ?_⟩
    · apply depth_and_le; intro c hc
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · omega
      · apply depth_or_le; intro c hc
        obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hc
        have := (hsel i (List.mem_range.mp hi)).1; omega
    · apply size_and_le hU1 (by simp; omega)
      intro c hc
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact lift1 hU1 (show size R.valid ≤ 1 * U ^ 1 by simp; omega) (by omega) (by omega)
      · exact lift1 hU1 (size_or_le hU1 (by simp; omega) (fun c hc => by
          obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hc; exact hsel1 i (List.mem_range.mp hi)))
          (by omega) (by omega)
    · apply ControllerBits.maxInput_and_le; intro c hc
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact hv.2.2
      · apply ControllerBits.maxInput_or_le; intro c hc
        obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hc
        exact (hsel i (List.mem_range.mp hi)).2.2
  · -- index bit q
    refine ⟨?_, ?_, ?_⟩
    · unfold idxBit; apply depth_or_le; intro c hc
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hc
      exact (hF i (List.mem_range.mp (List.mem_filter.mp hi).1)).1
    · unfold idxBit
      apply size_or_le hU1 (by
        have := List.length_filter_le (fun i => i.testBit (r - 1 - q)) (List.range N)
        simp only [List.length_map, List.length_range] at this ⊢; omega)
      intro c hc
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hc
      exact (hF i (List.mem_range.mp (List.mem_filter.mp hi).1)).2.1
    · unfold idxBit; apply ControllerBits.maxInput_or_le; intro c hc
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hc
      exact (hF i (List.mem_range.mp (List.mem_filter.mp hi).1)).2.2
  · -- value bit (unchanged)
    have h := hall c (by simp [hcv])
    refine ⟨by omega, ?_, h.2.2⟩
    exact lift1 hU1 (show size c ≤ 1 * U ^ 1 by simp; omega) (by omega) (by omega)

/-- From the phase-4 selector bound. -/
theorem encode_bound_sel {R : RCirc} {N B D S M r : Nat} (h : SelBound R N B D S M) (hr : N ≤ 2 ^ r) :
    BinBound (encode R N r) N B r (D + 3) (4 * ((N + 2) * (S + 2)) ^ 3) M :=
  encode_bound R h.1 h.2.1 hr h.2.2

/-- From the phase-3 readout bound (inputs = the B·N board bits). -/
theorem encode_bound_R {R : RCirc} {N B d s r : Nat} (h : RBound R N B d s) (hr : N ≤ 2 ^ r) :
    BinBound (encode R N r) N B r (d + 3) (4 * ((N + 2) * (s + 2)) ^ 3) (B * N) := by
  apply encode_bound R h.sel_len h.val_len hr
  intro c hc
  simp only [List.mem_cons, List.mem_append] at hc
  rcases hc with rfl | hc | hc
  · exact ⟨h.depth_valid, h.size_valid, h.max_valid⟩
  · exact ⟨h.depth_sel c hc, h.size_sel c hc, h.max_sel c hc⟩
  · exact ⟨h.depth_val c hc, h.size_val c hc, h.max_val c hc⟩

/-- A board-input binary bound is a `BinReadout.BBound`. -/
theorem bbound_of_bin {S : BCirc} {N B r D Sz : Nat} (h : BinBound S N B r D Sz (B * N)) :
    BBound S N B r D Sz := by
  refine ⟨h.idx_len, h.val_len, h.width, (h.all _ (by simp)).1, fun c hc => (h.all c (by simp [hc])).1,
    fun c hc => (h.all c (by simp [hc])).1, (h.all _ (by simp)).2.1,
    fun c hc => (h.all c (by simp [hc])).2.1, fun c hc => (h.all c (by simp [hc])).2.1,
    (h.all _ (by simp)).2.2, fun c hc => (h.all c (by simp [hc])).2.2, fun c hc => (h.all c (by simp [hc])).2.2⟩

/-- Every N has an adequate index width: r = log₂N + 1 gives N ≤ 2^r (r = 0 suffices
    for N ≤ 1). -/
theorem width_log (N : Nat) : N ≤ 2 ^ (N.log2 + 1) := Nat.le_of_lt Nat.lt_log2_self

theorem width_small {N : Nat} (h : N ≤ 1) : N ≤ 2 ^ 0 := by simpa using h

/-! ## Instances -/

/-- (a) Attainability: the binary readout circuits of the fibre-guess selector. -/
def attainBin (B N r a0 a1 : Nat) : Bool → BCirc := fun b => encode (attR B N a0 a1 b) N r

theorem attainBin_correct {B N r a0 a1 : Nat} (h0 : a0 ≠ 0) (h1 : a1 ≠ 0) (hl0 : a0 < 2 ^ B)
    (hl1 : a1 < 2 ^ B) (hr : N ≤ 2 ^ r) {P : List Nat} (hP : P.length = N) (hw : Width B P) (b : Bool) :
    binReadoutOf B N (attainBin B N r a0 a1) P b = attainF a0 a1 P b := by
  rw [binReadoutOf_eq, attainBin, encode_correct _ N r (by simp [attR, attRC]) hr, ← readoutOf_eq,
    attR_correct h0 h1 hl0 hl1 hP hw]

theorem attainBin_bound {B N r a0 a1 : Nat} (h0 : a0 ≠ 0) (h1 : a1 ≠ 0) (hl0 : a0 < 2 ^ B)
    (hl1 : a1 < 2 ^ B) (hr : N ≤ 2 ^ r) (b : Bool) :
    BBound (attainBin B N r a0 a1 b) N B r (9 + 3) (4 * ((N + 2) * (10 * Ua N B ^ 8 + 2)) ^ 3) := by
  apply bbound_of_bin
  apply encode_bound_R _ hr
  unfold attR
  cases b
  · exact attRC_RBound h0 hl0
  · exact attRC_RBound h1 hl1

theorem succCountRO_boards {B N j : Nat} {F G : Readout}
    (h : ∀ P, P.length = N → Width B P → ∀ b, F P b = G P b) :
    succCountRO B N F j = succCountRO B N G j := by
  unfold succCountRO successB
  apply rsum_congr; intro P hP
  obtain ⟨hlen, hw⟩ := mem_boards hP
  rw [h P hlen hw]

/-- EXACT ATTAINABILITY IN THE BINARY FORMAT: the explicit binary circuits for the least
    fibre representatives, fed the executed rollout outcome RO_{π_j}, succeed with
    conditional probability exactly 2/(2^B − 1). -/
theorem attainBin_exact {B N j r : Nat} (hB : 2 ≤ B) (hj : j < B) (hr : N + 1 ≤ 2 ^ r) :
    succCountRO B (N + 1)
        (binReadoutOf B (N + 1) (attainBin B (N + 1) r (fibreRep B (headVec j) false)
          (fibreRep B (headVec j) true))) j / nonzeroCount B (N + 1) =
      2 / (((2 ^ B : Nat) : Rat) - 1) := by
  have hw0 := headVec_ne_zero j
  have hwl := headVec_lt hj
  obtain ⟨n0, l0, _, _⟩ := fibreRep_spec hB hw0 hwl false
  obtain ⟨n1, l1, _, _⟩ := fibreRep_spec hB hw0 hwl true
  rw [succCountRO_boards (fun P hP hw b => attainBin_correct n0 n1 l0 l1 hr hP hw b)]
  exact attain_exact_head hB hj

/-- (b) Local two-frame restoration in binary format. -/
def restBin (B N r : Nat) : BCirc := encode (LocalRestore.restC B N) N r

theorem restBin_correct {B N r : Nat} (hr : N ≤ 2 ^ r) {Q Q' : List Nat} (hQ : Q.length = N)
    (hQ' : Q'.length = N) (hw : Width B Q) (hw' : Width B Q') (h0 : nimSum Q = 0) (hm : Move Q Q') :
    ∃ i v, binSem (restBin B N r) N (LocalRestore.tf B N Q Q') = some (i, v) ∧
      restore Q Q' = some (Q'.set i v) ∧ Move Q' (Q'.set i v) ∧ nimSum (Q'.set i v) = 0 := by
  obtain ⟨i, v, h1, h2, h3, h4⟩ := LocalRestore.restore_equiv hQ hQ' hw hw' h0 hm
  refine ⟨i, v, ?_, h2, h3, h4⟩
  rw [restBin, encode_correct _ N r LocalRestore.restC_bound.1 hr, h1]

theorem restBin_bound {B N r : Nat} (hr : N ≤ 2 ^ r) :
    BinBound (restBin B N r) N B r (4 + 9 + 4 + 3)
      (4 * ((N + 2) * (12 * ((N + 2) * (B + 2) * (B * (2 * B + 3) + 9 + 2)) ^ 8 * (10 * N + 1 + 1) + 2)) ^ 3)
      (2 * (B * N)) :=
  encode_bound_sel LocalRestore.restC_bound hr

/-- (c) The structured rollout policy π_j in binary format. -/
def polBin (B N j r : Nat) : BCirc := encode (polSel B N j) N r

theorem polBin_correct {B N j r : Nat} (hr : N ≤ 2 ^ r) {P : List Nat} (hP : P.length = N) (hw : Width B P) :
    binSem (polBin B N j r) N (boardBits B P) = policyIdx j P ∧
      applyM P (binSem (polBin B N j r) N (boardBits B P)) = policyStep j P := by
  have e : binSem (polBin B N j r) N (boardBits B P) = selReadout (polSel B N j) (boardBits B P) :=
    encode_correct _ N r (polSel_bound (B := B) (N := N) j).1 hr _
  rw [e]
  exact polSel_correct hP hw

theorem polBin_bound {B N j r : Nat} (hr : N ≤ 2 ^ r) :
    BinBound (polBin B N j r) N B r (5 + 9 + 3)
      (4 * ((N + 2) * (12 * ((N + 2) * (B + 2) * (4 * B + 9 + 2)) ^ 8 + 2)) ^ 3) (B * N) :=
  encode_bound_sel (polSel_bound j) hr

/-- (d) The multi-head selector in binary format. -/
def mhBin (B N r : Nat) : BCirc := encode (mhSel B N) N r

theorem mhBin_correct {B N r : Nat} (hr : N ≤ 2 ^ r) {P : List Nat} (hP : P.length = N) (hw : Width B P)
    (o : Nat → Bool) :
    binSem (mhBin B N r) N (obsIn B N P o) = attainT (reconstruct B o) P := by
  rw [mhBin, encode_correct _ N r (mhSel_bound (B := B) (N := N)).1 hr, mhSel_correct hP hw]

theorem mhBin_outcomes {B N r : Nat} (hr : N ≤ 2 ^ r) {P : List Nat} (hP : P.length = N) (hw : Width B P) :
    binSem (mhBin B N r) N (obsIn B N P (outcomes P)) = Controller.decisionMove P := by
  rw [mhBin, encode_correct _ N r (mhSel_bound (B := B) (N := N)).1 hr, mhSel_outcomes hP hw]

theorem mhBin_bound {B N r : Nat} (hr : N ≤ 2 ^ r) :
    BinBound (mhBin B N r) N B r (4 + 9 + 3 + 3)
      (4 * ((N + 2) * (12 * ((N + 2) * (B + 2) * (B * (2 * B + 3) + 9 + 2)) ^ 8 * (9 + 1) + 2)) ^ 3)
      (B * N + B) :=
  encode_bound_sel mhSel_bound hr

/-- The variable-target selector in binary format (σ on wires B·N …). -/
def varBin (B N r : Nat) : BCirc := encode (varSel B N) N r

theorem varBin_correct {B N r : Nat} (hr : N ≤ 2 ^ r) {P : List Nat} (hP : P.length = N) (hw : Width B P)
    {σ : Nat} (hσ : σ < 2 ^ B) :
    binSem (varBin B N r) N (selIn B N P σ) = attainT σ P := by
  rw [varBin, encode_correct _ N r (varSel_bound (B := B) (N := N)).1 hr, varSel_correct hP hw hσ]

/-! ## Edge cases (all instances of `encode_correct`) -/

/-- Invalid source readout: no move. -/
theorem encode_invalid (R : RCirc) (N r : Nat) (z : Nat → Bool) (hv : eval z R.valid = false) :
    binSem (encode R N r) N z = none := by
  simp [binSem, encode, hv]

/-- No true candidate flag: no move (even if the source valid flag is true). -/
theorem encode_noflag (R : RCirc) (N r : Nat) (hlen : R.sel.length = N) (z : Nat → Bool)
    (hno : ∀ i < N, eval z (getC R.sel i) = false) : binSem (encode R N r) N z = none := by
  have hor : eval z (or ((List.range N).map (getC R.sel))) = false := by
    rw [eval_or, List.any_map]; apply List.any_eq_false.mpr
    intro i hi; simpa using hno i (List.mem_range.mp hi)
  simp [binSem, encode, hor]

/-- Several true flags: the encoded index is the least true one. -/
theorem encode_least (R : RCirc) (N r : Nat) (hlen : R.sel.length = N) (hr : N ≤ 2 ^ r) (z : Nat → Bool)
    (hv : eval z R.valid = true) {i : Nat} (hi : i < N) (hti : eval z (getC R.sel i) = true)
    (hlow : ∀ k < i, eval z (getC R.sel k) = false) :
    binSem (encode R N r) N z = some (i, toNatBE (R.val.map (eval z))) := by
  rw [encode_correct R N r hlen hr z]
  have hft : firstTrue (R.sel.map (eval z)) = some i := by
    rw [firstTrue_some_iff]
    refine ⟨by simp [hlen, hi], ?_, ?_⟩
    · rw [← eval_getC]; exact hti
    · intro k hk; rw [← eval_getC]; exact hlow k hk
  simp [selReadout, hv, hft]

/-- N = 0: never a move, for any index width. -/
theorem encode_zero (R : RCirc) (r : Nat) (hlen : R.sel.length = 0) (z : Nat → Bool) :
    binSem (encode R 0 r) 0 z = none :=
  encode_noflag R 0 r hlen z (fun i hi => absurd hi (by omega))

/-- N = 1 with zero index width (r = 0): the index list is empty and decodes to 0. -/
theorem encode_one (R : RCirc) (hlen : R.sel.length = 1) (z : Nat → Bool) :
    (encode R 1 0).idx = [] ∧ binSem (encode R 1 0) 1 z = selReadout R z :=
  ⟨rfl, encode_correct R 1 0 hlen (by decide) z⟩

/-- BINARY SHARPNESS: the explicit binary circuits for the least fibre representatives
    succeed with exactly 2/(2^B − 1), satisfy BBound (depth 12, size
    4((N+3)(10·Ua(N+1) B^8 + 2))^3, r index bits), and under the parity-correlation
    premise every binary readout with the same bounds succeeds with at most
    2/(2^B − 1) + (2^B − 1)ε. -/
theorem attainBin_sharp {B N j r : Nat} (hB : 2 ≤ B) (hj : j < B) (hr : N + 1 ≤ 2 ^ r) {ε : Rat}
    (hprem : ∀ m, N + 1 ≤ m → m ≤ B * (N + 1) →
      ParityCorrPremise (9 + 3 + 2 + 11)
        (12 * Upar (N + 1) B ((r + 1) * (4 * ((N + 1 + 2) * (10 * Ua (N + 1) B ^ 8 + 2)) ^ 3 + 1)) ^ 10) m ε) :
    (∀ b, BBound (attainBin B (N + 1) r (fibreRep B (headVec j) false) (fibreRep B (headVec j) true) b)
      (N + 1) B r (9 + 3) (4 * ((N + 1 + 2) * (10 * Ua (N + 1) B ^ 8 + 2)) ^ 3)) ∧
    succCountRO B (N + 1)
        (binReadoutOf B (N + 1) (attainBin B (N + 1) r (fibreRep B (headVec j) false)
          (fibreRep B (headVec j) true))) j / nonzeroCount B (N + 1) = 2 / (((2 ^ B : Nat) : Rat) - 1) ∧
    (∀ R : Bool → BCirc, (∀ b, BBound (R b) (N + 1) B r (9 + 3) (4 * ((N + 1 + 2) * (10 * Ua (N + 1) B ^ 8 + 2)) ^ 3)) →
      succCountRO B (N + 1) (binReadoutOf B (N + 1) R) j / nonzeroCount B (N + 1) ≤
        2 / (((2 ^ B : Nat) : Rat) - 1) + (((2 ^ B : Nat) : Rat) - 1) * ε) := by
  have hw0 := headVec_ne_zero j
  have hwl := headVec_lt hj
  obtain ⟨n0, l0, _, _⟩ := fibreRep_spec hB hw0 hwl false
  obtain ⟨n1, l1, _, _⟩ := fibreRep_spec hB hw0 hwl true
  exact ⟨fun b => attainBin_bound n0 n1 l0 l1 hr b, attainBin_exact hB hj hr,
    fun R hR => binary_readout_bound hj R hR hprem⟩


/-! ## Axiom audit -/

#print axioms binReadoutOf_eq
#print axioms flags_eq
#print axioms firstF_eval
#print axioms encode_correct
#print axioms totalSize_le
#print axioms encode_bound
#print axioms encode_bound_sel
#print axioms encode_bound_R
#print axioms bbound_of_bin
#print axioms width_log
#print axioms width_small
#print axioms attainBin_correct
#print axioms attainBin_bound
#print axioms succCountRO_boards
#print axioms attainBin_exact
#print axioms restBin_correct
#print axioms restBin_bound
#print axioms polBin_correct
#print axioms polBin_bound
#print axioms mhBin_correct
#print axioms mhBin_outcomes
#print axioms mhBin_bound
#print axioms varBin_correct
#print axioms encode_invalid
#print axioms encode_noflag
#print axioms encode_least
#print axioms encode_zero
#print axioms encode_one
#print axioms attainBin_sharp
end PriorityEncoder
end NimAudit
