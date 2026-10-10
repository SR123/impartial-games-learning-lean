import FiniteNet
import NimCorrBridge

/- Phase 4, Priority 2a: binary-index readouts.  Written by Claude (10 October 2026).
   Lean 4.26.0, core/Std only.

   The paper's readout outputs a move as (valid bit, binary heap index, binary new
   value).  `BCirc` packages formulas for these bits; `binReadoutOf` is the induced
   phase-2 Readout (an index ≥ N is an invalid move).  An equality decoder turns the
   r index bits into N selection formulas; we prove agreement with the binary
   semantics for every encoding (valid indices, out-of-range indices, N = 0, N = 1),
   given only that the index width suffices (N ≤ 2^r).  Resources propagate to the
   phase-3 `RBound`, so `circuit_readout_bound` applies.  Finally, readouts computed
   by threshold networks are compiled with the repaired finite-input compiler
   (FiniteNet.netFormula) and the conditional success bound is stated for them. -/

namespace NimAudit
namespace BinReadout

open Prob AC0 AC0.Circ Game Bridge Rollout CorrBridge FiniteNet

attribute [local simp] Rat.add_zero Rat.zero_add

/-- Binary readout formulas for one observed bit. -/
structure BCirc where
  valid : Circ
  idx : List Circ
  val : List Circ

/-- The readout defined by binary readout formulas (index ≥ N is invalid). -/
def binReadoutOf (B N : Nat) (R : Bool → BCirc) : Readout := fun P b =>
  if eval (boardBits B P) (R b).valid then
    if toNatBE ((R b).idx.map (eval (boardBits B P))) < N then
      some (toNatBE ((R b).idx.map (eval (boardBits B P))),
        toNatBE ((R b).val.map (eval (boardBits B P))))
    else none
  else none

def litEq (c : Circ) (bit : Bool) : Circ := if bit then c else not c

/-- Equality decoder: the r index bits encode i (big-endian). -/
def decodeC (idx : List Circ) (i : Nat) : Circ :=
  and ((List.range idx.length).map (fun q => litEq (getC idx q) (i.testBit (idx.length - 1 - q))))

/-- Adapter to the phase-3 selection-formula interface. -/
def toRCirc (N : Nat) (R : BCirc) : RCirc := ⟨R.valid, (List.range N).map (decodeC R.idx), R.val⟩

theorem toNatBE_eq_iff (v : List Bool) {i : Nat} (hi : i < 2 ^ v.length) :
    toNatBE v = i ↔ ∀ q < v.length, v.getD q false = i.testBit (v.length - 1 - q) := by
  constructor
  · intro h q hq
    rw [← h, testBit_toNatBE v q hq]
  · intro h
    apply Nat.eq_of_testBit_eq
    intro k
    rcases Nat.lt_or_ge k v.length with hk | hk
    · have := testBit_toNatBE v (v.length - 1 - k) (by omega)
      rw [show v.length - 1 - (v.length - 1 - k) = k by omega] at this
      rw [this, h _ (by omega), show v.length - 1 - (v.length - 1 - k) = k by omega]
    · rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (toNatBE_lt v) (Nat.pow_le_pow_right (by decide) hk)),
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hi (Nat.pow_le_pow_right (by decide) hk))]

/-- DECODER SEMANTICS: for i < 2^r the decoder fires iff the index bits encode i. -/
theorem decodeC_eval (z : Nat → Bool) (idx : List Circ) {i : Nat} (hi : i < 2 ^ idx.length) :
    eval z (decodeC idx i) = decide (toNatBE (idx.map (eval z)) = i) := by
  have hl : (idx.map (eval z)).length = idx.length := by simp
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_iff, toNatBE_eq_iff _ (by rw [hl]; exact hi), hl]
  unfold decodeC
  simp only [eval_and, List.all_map, List.all_eq_true, List.mem_range, Function.comp]
  have hg : ∀ q, q < idx.length → eval z (getC idx q) = (idx.map (eval z)).getD q false := by
    intro q _; rw [eval_getC]
  constructor
  · intro h q hq
    have := h q hq
    rw [← hg q hq]
    unfold litEq at this
    split at this
    · next hb => rw [hb]; exact this
    · next hb => simp only [eval_not, Bool.not_eq_true'] at this; rw [this]; simpa using hb
  · intro h q hq
    have := h q hq
    rw [← hg q hq] at this
    unfold litEq
    split
    · next hb => rw [this, hb]
    · next hb => simp only [eval_not, Bool.not_eq_true']; rw [this]; simpa using hb

theorem firstTrue_eqs (N v : Nat) :
    firstTrue ((List.range N).map (fun i => decide (v = i))) = if v < N then some v else none := by
  by_cases hv : v < N
  · simp only [hv, if_true]
    rw [firstTrue_some_iff]
    simp only [List.length_map, List.length_range]
    refine ⟨hv, ?_, ?_⟩
    · simp [List.getD_eq_getElem?_getD, List.getElem?_range hv]
    · intro i hi
      simp [List.getD_eq_getElem?_getD, List.getElem?_range (show i < N by omega)]; omega
  · simp only [hv, if_false]
    cases hf : firstTrue ((List.range N).map (fun i => decide (v = i))) with
    | none => rfl
    | some i =>
      exfalso
      obtain ⟨hl, hb, _⟩ := (firstTrue_some_iff _ i).1 hf
      simp only [List.length_map, List.length_range] at hl
      simp [List.getD_eq_getElem?_getD, List.getElem?_range hl] at hb
      omega

/-- ADAPTER CORRECTNESS: with index width N ≤ 2^r, the selection-formula readout of
    the decoded circuits equals the binary readout on every board (all encodings,
    including out-of-range indices and N = 0, 1). -/
theorem toRCirc_correct (B N : Nat) (R : Bool → BCirc) (hN : ∀ b, N ≤ 2 ^ (R b).idx.length)
    (P : List Nat) (b : Bool) :
    readoutOf B (fun b => toRCirc N (R b)) P b = binReadoutOf B N R P b := by
  unfold readoutOf binReadoutOf toRCirc
  simp only
  have hsel : ((List.range N).map (decodeC (R b).idx)).map (eval (boardBits B P)) =
      (List.range N).map (fun i => decide (toNatBE ((R b).idx.map (eval (boardBits B P))) = i)) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro i hi
    exact decodeC_eval _ _ (Nat.lt_of_lt_of_le (List.mem_range.mp hi) (hN b))
  rw [hsel, firstTrue_eqs]
  by_cases hv : eval (boardBits B P) (R b).valid = true
  · simp only [hv, if_true]
    by_cases hlt : toNatBE ((R b).idx.map (eval (boardBits B P))) < N
    · simp [hlt]
    · simp [hlt]
  · simp [hv]

/-- Resource bounds for binary readout formulas. -/
structure BBound (R : BCirc) (N B r d s : Nat) : Prop where
  idx_len : R.idx.length = r
  val_len : R.val.length = B
  width : N ≤ 2 ^ r
  depth_valid : depth R.valid ≤ d
  depth_idx : ∀ c ∈ R.idx, depth c ≤ d
  depth_val : ∀ c ∈ R.val, depth c ≤ d
  size_valid : size R.valid ≤ s
  size_idx : ∀ c ∈ R.idx, size c ≤ s
  size_val : ∀ c ∈ R.val, size c ≤ s
  max_valid : maxInput R.valid ≤ B * N
  max_idx : ∀ c ∈ R.idx, maxInput c ≤ B * N
  max_val : ∀ c ∈ R.val, maxInput c ≤ B * N

theorem getC_mem {cs : List Circ} {q : Nat} (hq : q < cs.length) : getC cs q ∈ cs := by
  unfold getC
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hq]
  simp

/-- DECODER RESOURCES: depth ≤ d + 2, size ≤ r (s+1) + 1, inputs as the index formulas. -/
theorem decodeC_resources {R : BCirc} {N B r d s : Nat} (hb : BBound R N B r d s) (i : Nat) :
    depth (decodeC R.idx i) ≤ d + 2 ∧ size (decodeC R.idx i) ≤ r * (s + 1) + 1 ∧
    maxInput (decodeC R.idx i) ≤ B * N := by
  have hlit : ∀ q, q < R.idx.length → ∀ bit,
      depth (litEq (getC R.idx q) bit) ≤ d + 1 ∧ size (litEq (getC R.idx q) bit) ≤ s + 1 ∧
      maxInput (litEq (getC R.idx q) bit) ≤ B * N := by
    intro q hq bit
    have hm := getC_mem hq
    unfold litEq
    split
    · exact ⟨by have := hb.depth_idx _ hm; omega, by have := hb.size_idx _ hm; omega, hb.max_idx _ hm⟩
    · simp only [depth_not, size_not, maxInput_not]
      exact ⟨by have := hb.depth_idx _ hm; omega, by have := hb.size_idx _ hm; omega, hb.max_idx _ hm⟩
  unfold decodeC
  refine ⟨?_, ?_, ?_⟩
  · apply depth_and_le
    intro c hc
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hc
    exact (hlit q (List.mem_range.mp hq) _).1
  · simp only [size_and]
    have h := sum_le_len_mul (cs := (List.range R.idx.length).map
      (fun q => litEq (getC R.idx q) (i.testBit (R.idx.length - 1 - q)))) (S := s + 1) (by
        intro c hc
        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hc
        exact (hlit q (List.mem_range.mp hq) _).2.1)
    simp only [List.length_map, List.length_range] at h
    rw [hb.idx_len] at h ⊢
    omega
  · simp only [maxInput_and]
    apply listMax_le
    intro a ha
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ha
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hc
    exact (hlit q (List.mem_range.mp hq) _).2.2

/-- The adapted circuits satisfy the phase-3 resource bounds with
    d' = d + 2 and s' = (r+1)(s+1). -/
theorem toRCirc_RBound {R : BCirc} {N B r d s : Nat} (hb : BBound R N B r d s) :
    RBound (toRCirc N R) N B (d + 2) ((r + 1) * (s + 1)) := by
  have hs : s ≤ (r + 1) * (s + 1) := by
    have := Nat.le_mul_of_pos_left (s + 1) (show 0 < r + 1 by omega); omega
  have hd : r * (s + 1) + 1 ≤ (r + 1) * (s + 1) := by rw [Nat.add_mul, Nat.one_mul]; omega
  refine ⟨by simp [toRCirc], hb.val_len, by have := hb.depth_valid; simp [toRCirc]; omega, ?_, ?_,
    Nat.le_trans hb.size_valid hs, ?_, ?_, hb.max_valid, ?_, hb.max_val⟩
  · intro c hc; simp only [toRCirc, List.mem_map, List.mem_range] at hc
    obtain ⟨i, _, rfl⟩ := hc; exact (decodeC_resources hb i).1
  · intro c hc; have := hb.depth_val c hc; simp only [toRCirc] at hc; omega
  · intro c hc; simp only [toRCirc, List.mem_map, List.mem_range] at hc
    obtain ⟨i, _, rfl⟩ := hc; exact Nat.le_trans (decodeC_resources hb i).2.1 hd
  · intro c hc; exact Nat.le_trans (hb.size_val c hc) hs
  · intro c hc; simp only [toRCirc, List.mem_map, List.mem_range] at hc
    obtain ⟨i, _, rfl⟩ := hc; exact (decodeC_resources hb i).2.2

/-- The phase-2 success count only depends on the readout function. -/
theorem succCountRO_congr {B N j : Nat} {F G : Readout} (h : ∀ P b, F P b = G P b) :
    succCountRO B N F j = succCountRO B N G j := by
  unfold succCountRO successB
  apply rsum_congr; intro P _
  rw [h]

/-- CONDITIONAL BOUND FOR BINARY READOUTS: binary readout formulas with BBound
    (depth ≤ d, size ≤ s, r index bits, N+1 ≤ 2^r) fed RO_{pi_j} succeed with
    conditional probability ≤ 2/(q-1) + (q-1) ε, under the parity-correlation
    premise for depth d + 13 and size 12 U^10, U = (N+3)(B+2)((r+1)(s+1)+2). -/
theorem binary_readout_bound {B N j r d s : Nat} (hj : j < B) (R : Bool → BCirc)
    (hb : ∀ b, BBound (R b) (N + 1) B r d s) {ε : Rat}
    (hprem : ∀ m, N + 1 ≤ m → m ≤ B * (N + 1) →
      ParityCorrPremise (d + 2 + 11) (12 * Upar (N + 1) B ((r + 1) * (s + 1)) ^ 10) m ε) :
    succCountRO B (N + 1) (binReadoutOf B (N + 1) R) j / nonzeroCount B (N + 1) ≤
      2 / (((2 ^ B : Nat) : Rat) - 1) + (((2 ^ B : Nat) : Rat) - 1) * ε := by
  have hN : ∀ b, N + 1 ≤ 2 ^ (R b).idx.length := fun b => by rw [(hb b).idx_len]; exact (hb b).width
  rw [← succCountRO_congr (fun P b => toRCirc_correct B (N + 1) R hN P b)]
  exact circuit_readout_bound hj _ (fun b => toRCirc_RBound (hb b)) hprem

/-! ## Readouts computed by threshold networks -/

/-- Output layout of a readout network: output 0 = valid, outputs 1..r = index bits,
    outputs r+1..r+B = value bits; compiled with the finite-input compiler on the
    B·N board bits. -/
def netBCirc (W B N r : Nat) (ls : List Layer) : BCirc :=
  ⟨netFormula W (B * N) ls 0, (List.range r).map (fun q => netFormula W (B * N) ls (1 + q)),
   (List.range B).map (fun p => netFormula W (B * N) ls (1 + r + p))⟩

/-- boardBits vanishes beyond B·|P|, so zero-extension at B·N is invisible. -/
theorem pad_boardBits {B N : Nat} {P : List Nat} (hP : P.length = N) :
    pad (B * N) (boardBits B P) = boardBits B P := by
  funext j
  unfold pad
  by_cases hj : j < B * N
  · simp [hj]
  · simp only [hj, if_false]
    unfold boardBits
    rw [hP]; simp [hj]

/-- On boards of N heaps the compiled formulas compute the network on the board bits. -/
theorem netBCirc_eval {W B N : Nat} (ls : List Layer) (hv : NetValid W ls) {P : List Nat}
    (hP : P.length = N) (o : Nat) :
    eval (boardBits B P) (netFormula W (B * N) ls o) = evalNet ls (boardBits B P) o := by
  unfold netFormula
  rw [eval_compileNet ls hv]
  have : (fun j => eval (boardBits B P) (clip (B * N) j)) = boardBits B P := by
    funext j; rw [eval_clip, pad_boardBits (B := B) hP]
  rw [this]

/-- Semantics of a network readout on boards of N heaps. -/
theorem netReadout_eq {W B N r : Nat} (nets : Bool → List Layer) (hv : ∀ b, NetValid W (nets b))
    {P : List Nat} (hP : P.length = N) (b : Bool) :
    binReadoutOf B N (fun b => netBCirc W B N r (nets b)) P b =
      if evalNet (nets b) (boardBits B P) 0 then
        if toNatBE ((List.range r).map (fun q => evalNet (nets b) (boardBits B P) (1 + q))) < N then
          some (toNatBE ((List.range r).map (fun q => evalNet (nets b) (boardBits B P) (1 + q))),
            toNatBE ((List.range B).map (fun p => evalNet (nets b) (boardBits B P) (1 + r + p))))
        else none
      else none := by
  unfold binReadoutOf netBCirc
  simp only [List.map_map, Function.comp_def]
  rw [netBCirc_eval _ (hv b) hP]
  have e1 : (fun q => eval (boardBits B P) (netFormula W (B * N) (nets b) (1 + q))) =
      (fun q => evalNet (nets b) (boardBits B P) (1 + q)) := by
    funext q; exact netBCirc_eval _ (hv b) hP _
  have e2 : (fun p => eval (boardBits B P) (netFormula W (B * N) (nets b) (1 + r + p))) =
      (fun p => evalNet (nets b) (boardBits B P) (1 + r + p)) := by
    funext p; exact netBCirc_eval _ (hv b) hP _
  rw [e1, e2]

/-- Network readouts satisfy BBound with depth 3L and size 2 (2W+3)^L (M+1)^(WL). -/
theorem netBCirc_BBound {W M B N r : Nat} (ls : List Layer) (hv : NetValid W ls)
    (hb : NetBounded M ls) (hr : N ≤ 2 ^ r) :
    BBound (netBCirc W B N r ls) N B r (3 * ls.length)
      (2 * ((2 * W + 3) ^ ls.length * (M + 1) ^ (W * ls.length))) := by
  have sp := fun o => netFormula_spec (B * N) ls hv hb o
  refine ⟨by simp [netBCirc], by simp [netBCirc], hr, (sp 0).2.1, ?_, ?_, (sp 0).2.2.1, ?_, ?_,
    (sp 0).2.2.2, ?_, ?_⟩ <;>
  · intro c hc
    simp only [netBCirc, List.mem_map, List.mem_range] at hc
    obtain ⟨q, _, rfl⟩ := hc
    first
      | exact (sp _).2.1
      | exact (sp _).2.2.1
      | exact (sp _).2.2.2

/-- CONDITIONAL BOUND FOR NETWORK READOUTS.  Two valid L-layer threshold networks
    (one per observed bit) with fan-ins/widths ≤ M, compiled with the finite-input
    compiler on the B·(N+1) board bits and read through the binary decoder
    (r index bits, N+1 ≤ 2^r), succeed when fed RO_{pi_j} with conditional
    probability ≤ 2/(q-1) + (q-1) ε, under the parity-correlation premise for depth
    3L + 13 and size 12 U^10 with U = (N+3)(B+2)((r+1)(s+1)+2),
    s = 2 (2W+3)^L (M+1)^(WL). -/
theorem network_readout_bound {W M B N j r L : Nat} (hj : j < B) (nets : Bool → List Layer)
    (hlen : ∀ b, (nets b).length = L) (hv : ∀ b, NetValid W (nets b))
    (hb : ∀ b, NetBounded M (nets b)) (hr : N + 1 ≤ 2 ^ r) {ε : Rat}
    (hprem : ∀ m, N + 1 ≤ m → m ≤ B * (N + 1) →
      ParityCorrPremise (3 * L + 2 + 11)
        (12 * Upar (N + 1) B ((r + 1) * (2 * ((2 * W + 3) ^ L * (M + 1) ^ (W * L)) + 1)) ^ 10) m ε) :
    succCountRO B (N + 1) (binReadoutOf B (N + 1) (fun b => netBCirc W B (N + 1) r (nets b))) j /
        nonzeroCount B (N + 1) ≤
      2 / (((2 ^ B : Nat) : Rat) - 1) + (((2 ^ B : Nat) : Rat) - 1) * ε := by
  apply binary_readout_bound hj _ _ hprem
  intro b
  have := netBCirc_BBound (B := B) (N := N + 1) (r := r) (nets b) (hv b) (hb b) hr
  rw [hlen] at this
  exact this


/-! ## Axiom audit -/

#print axioms toNatBE_eq_iff
#print axioms decodeC_eval
#print axioms firstTrue_eqs
#print axioms toRCirc_correct
#print axioms getC_mem
#print axioms decodeC_resources
#print axioms toRCirc_RBound
#print axioms succCountRO_congr
#print axioms binary_readout_bound
#print axioms pad_boardBits
#print axioms netBCirc_eval
#print axioms netReadout_eq
#print axioms netBCirc_BBound
#print axioms network_readout_bound
end BinReadout
end NimAudit
