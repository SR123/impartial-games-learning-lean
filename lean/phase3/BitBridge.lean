import Circuit

/- Phase 3, target D (generic part).  Written by Claude (10 October 2026).
   Lean 4.26.0, core/Std only.

   * Bit vectors, big-endian heap encoding, and transfer of uniform sums from
     boards (N heaps < 2^B) to bit vectors of length B·N (heap-major).
   * <u, sigma(P)> equals the parity of the input bits selected by the mask
     consisting of N copies of u's bits; the mask has N·|u| ≥ N ones for u ≠ 0.
   * Restriction: fixing the coordinates outside a mask is a leaf substitution,
     so circuit size and depth are unchanged and the restricted circuit reads only
     the mask coordinates; averaging over the fixed coordinates turns a premise on
     full-parity correlation into a bound on masked-parity correlation.
   The classical AC0 parity-correlation theorem is NOT proved: it enters only as
   the explicit hypothesis `ParityCorrPremise`. -/

namespace NimAudit
namespace Bridge

open Prob AC0 AC0.Circ Game

attribute [local simp] Rat.add_zero Rat.zero_add Rat.zero_mul Rat.mul_zero Rat.one_mul
  Rat.mul_one Rat.neg_mul Rat.mul_neg

/-! ## Bit vectors -/

def bitvecs : Nat → List (List Bool)
  | 0 => [[]]
  | n + 1 => (bitvecs n).map (false :: ·) ++ (bitvecs n).map (true :: ·)

theorem mem_bitvecs_length {n : Nat} {x : List Bool} (h : x ∈ bitvecs n) : x.length = n := by
  induction n generalizing x with
  | zero => simp [bitvecs] at h; subst h; rfl
  | succ n ih =>
    simp only [bitvecs, List.mem_append, List.mem_map] at h
    rcases h with ⟨v, hv, rfl⟩ | ⟨v, hv, rfl⟩ <;> simp [ih hv]

theorem rsum_bitvecs_succ (n : Nat) (f : List Bool → Rat) :
    rsum (bitvecs (n + 1)) f =
      rsum (bitvecs n) (fun v => f (false :: v)) + rsum (bitvecs n) (fun v => f (true :: v)) := by
  simp only [bitvecs, rsum_append, rsum_map]

theorem rsum_bitvecs_add (m n : Nat) (f : List Bool → Rat) :
    rsum (bitvecs (m + n)) f =
      rsum (bitvecs m) (fun v => rsum (bitvecs n) (fun w => f (v ++ w))) := by
  induction m generalizing f with
  | zero => simp [bitvecs]
  | succ m ih =>
    rw [show m + 1 + n = (m + n) + 1 by omega, rsum_bitvecs_succ, rsum_bitvecs_succ, ih, ih]
    rfl

theorem count_bitvecs (n : Nat) : rsum (bitvecs n) (fun _ => 1) = (2 : Rat) ^ n := by
  induction n with
  | zero => simp [bitvecs]
  | succ n ih => rw [rsum_bitvecs_succ, ih, Rat.pow_succ]; grind

/-- Big-endian value of a bit list. -/
def toNatBE : List Bool → Nat
  | [] => 0
  | b :: v => (if b then 2 ^ v.length else 0) + toNatBE v

theorem toNatBE_lt (v : List Bool) : toNatBE v < 2 ^ v.length := by
  induction v with
  | nil => simp [toNatBE]
  | cons b v ih =>
    simp only [toNatBE, List.length_cons, Nat.pow_succ]
    split <;> omega

theorem rsum_range_bitvecs (B : Nat) (g : Nat → Rat) :
    rsum (List.range (2 ^ B)) g = rsum (bitvecs B) (fun v => g (toNatBE v)) := by
  induction B generalizing g with
  | zero => simp [bitvecs, toNatBE]
  | succ B ih =>
    rw [show 2 ^ (B + 1) = 2 ^ B + 2 ^ B by rw [Nat.pow_succ]; omega, List.range_add,
      rsum_append, rsum_map, ih, ih, rsum_bitvecs_succ]
    congr 1
    · apply rsum_congr; intro v _; simp [toNatBE]
    · apply rsum_congr; intro v hv; simp [toNatBE, mem_bitvecs_length hv]

/-- (toNatBE v).testBit (|v| - 1 - p) = v_p for p < |v|. -/
theorem testBit_toNatBE (v : List Bool) (p : Nat) (hp : p < v.length) :
    (toNatBE v).testBit (v.length - 1 - p) = v.getD p false := by
  induction v generalizing p with
  | nil => simp at hp
  | cons b v ih =>
    simp only [toNatBE, List.length_cons]
    have hlt := toNatBE_lt v
    cases p with
    | zero =>
      simp only [Nat.add_sub_cancel, Nat.sub_zero, List.getD_cons_zero]
      cases b
      · simp; exact Nat.testBit_lt_two_pow hlt
      · simp only [if_true]; rw [Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hlt]; rfl
    | succ p =>
      simp only [List.getD_cons_succ]
      have hp' : p < v.length := by simp at hp; omega
      have e : v.length + 1 - 1 - (p + 1) = v.length - 1 - p := by omega
      rw [e]
      cases b
      · simp; exact ih p hp'
      · simp only [if_true]
        rw [Nat.testBit_two_pow_add_gt (by omega)]
        exact ih p hp'

/-! ## Boards as bit vectors -/

/-- Decode a heap-major big-endian bit vector into N heaps. -/
def decodeBoard (B : Nat) : Nat → List Bool → List Nat
  | 0, _ => []
  | N + 1, x => toNatBE (x.take B) :: decodeBoard B N (x.drop B)

theorem rsum_boards_bitvecs (B N : Nat) (f : List Nat → Rat) :
    rsum (boards (2 ^ B) N) f = rsum (bitvecs (B * N)) (fun x => f (decodeBoard B N x)) := by
  induction N generalizing f with
  | zero => simp [boards, bitvecs, decodeBoard]
  | succ N ih =>
    rw [rsum_boards_succ, rsum_range_bitvecs, show B * (N + 1) = B + B * N by
      rw [Nat.mul_succ, Nat.add_comm], rsum_bitvecs_add]
    apply rsum_congr; intro v hv
    rw [ih]
    apply rsum_congr; intro w _
    have hl := mem_bitvecs_length hv
    simp only [decodeBoard]
    rw [List.take_left' hl, List.drop_left' hl]

theorem length_decodeBoard (B N : Nat) (x : List Bool) : (decodeBoard B N x).length = N := by
  induction N generalizing x with
  | zero => rfl
  | succ N ih => simp [decodeBoard, ih]

theorem decodeBoard_width {B N : Nat} {x : List Bool} (hx : x ∈ bitvecs (B * N)) :
    Width B (decodeBoard B N x) := by
  induction N generalizing x with
  | zero => intro y hy; simp [decodeBoard] at hy
  | succ N ih =>
    intro y hy
    simp only [decodeBoard, List.mem_cons] at hy
    have hl := mem_bitvecs_length hx
    rcases hy with rfl | hy
    · have := toNatBE_lt (x.take B)
      have hB : B ≤ x.length := by rw [hl, Nat.mul_succ]; omega
      rw [List.length_take, Nat.min_eq_left hB] at this
      exact this
    · -- x.drop B ∈ bitvecs (B * N): rebuild via the length characterisation
      have hmem : x.drop B ∈ bitvecs (B * N) := by
        have key : ∀ n (z : List Bool), z.length = n → z ∈ bitvecs n := by
          intro n
          induction n with
          | zero => intro z hz; rw [List.length_eq_zero_iff] at hz; subst hz; simp [bitvecs]
          | succ n ihn =>
            intro z hz
            cases z with
            | nil => simp at hz
            | cons b z =>
              simp only [bitvecs, List.mem_append, List.mem_map]
              cases b
              · exact Or.inl ⟨z, ihn z (by simpa using hz), rfl⟩
              · exact Or.inr ⟨z, ihn z (by simpa using hz), rfl⟩
        apply key
        rw [List.length_drop, hl, Nat.mul_succ]; omega
      exact ih hmem y hy

theorem mem_bitvecs_of_length {n : Nat} {z : List Bool} (hz : z.length = n) : z ∈ bitvecs n := by
  induction n generalizing z with
  | zero => rw [List.length_eq_zero_iff] at hz; subst hz; simp [bitvecs]
  | succ n ihn =>
    cases z with
    | nil => simp at hz
    | cons b z =>
      simp only [bitvecs, List.mem_append, List.mem_map]
      cases b
      · exact Or.inl ⟨z, ihn (by simpa using hz), rfl⟩
      · exact Or.inr ⟨z, ihn (by simpa using hz), rfl⟩

/-! ## Masked parity and <u, sigma> -/

/-- Big-endian B-bit expansion. -/
def toBitsBE : Nat → Nat → List Bool
  | 0, _ => []
  | B + 1, h => h.testBit B :: toBitsBE B h

theorem length_toBitsBE (B h : Nat) : (toBitsBE B h).length = B := by
  induction B with
  | zero => rfl
  | succ B ih => simp [toBitsBE, ih]

/-- Parity of the coordinates of x selected by the mask. -/
def pm : List Bool → List Bool → Bool
  | [], _ => false
  | _ :: _, [] => false
  | m :: ms, b :: bs => xor (m && b) (pm ms bs)

theorem pm_append {ms1 ms2 v w : List Bool} (h : ms1.length = v.length) :
    pm (ms1 ++ ms2) (v ++ w) = xor (pm ms1 v) (pm ms2 w) := by
  induction ms1 generalizing v with
  | nil => cases v with
    | nil => simp [pm]
    | cons _ _ => simp at h
  | cons m ms ih =>
    cases v with
    | nil => simp at h
    | cons b v =>
      simp only [List.cons_append, pm]
      rw [ih (by simpa using h)]
      cases (m && b) <;> cases pm ms v <;> cases pm ms2 w <;> rfl

/-- Mask for the character chi_u on N heaps: N copies of u's B bits. -/
def maskU (B : Nat) : Nat → Nat → List Bool
  | 0, _ => []
  | N + 1, u => toBitsBE B u ++ maskU B N u

theorem length_maskU (B N u : Nat) : (maskU B N u).length = B * N := by
  induction N with
  | zero => rfl
  | succ N ih => simp [maskU, length_toBitsBE, ih, Nat.mul_succ, Nat.add_comm]

theorem dotB_zero_right (B u : Nat) : dotB B u 0 = false := by
  induction B with
  | zero => rfl
  | succ B ih => simp [dotB, ih]

theorem length_bitvecs (n : Nat) : (bitvecs n).length = 2 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [bitvecs, ih, Nat.pow_succ]; omega

theorem dotB_congr_right {B v v' : Nat} (u : Nat) (h : ∀ k < B, v.testBit k = v'.testBit k) :
    dotB B u v = dotB B u v' := by
  induction B with
  | zero => rfl
  | succ B ih =>
    simp only [dotB]
    rw [ih (fun k hk => h k (by omega)), h B (by omega)]

/-- <u, value of a big-endian block> = masked parity of the block. -/
theorem dot_toNatBE (u : Nat) : ∀ (v : List Bool),
    dotB v.length u (toNatBE v) = pm (toBitsBE v.length u) v
  | [] => rfl
  | b :: v => by
    simp only [List.length_cons, dotB, toBitsBE, pm, toNatBE]
    have hlt := toNatBE_lt v
    have hcong : dotB v.length u ((if b then 2 ^ v.length else 0) + toNatBE v) =
        dotB v.length u (toNatBE v) := by
      apply dotB_congr_right
      intro k hk
      cases b
      · simp
      · simp only [if_true]; exact Nat.testBit_two_pow_add_gt hk _
    have htop : ((if b then 2 ^ v.length else 0) + toNatBE v).testBit v.length = b := by
      cases b
      · simp; exact Nat.testBit_lt_two_pow hlt
      · simp only [if_true]; rw [Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hlt]; rfl
    rw [hcong, htop, dot_toNatBE u v]
    cases (u.testBit v.length && b) <;> cases pm (toBitsBE v.length u) v <;> rfl

/-- PARITY IDENTITY: on encoded boards, <u, sigma(P)> is the masked parity of the
    input bits. -/
theorem chi_parity (B N u : Nat) {x : List Bool} (hx : x ∈ bitvecs (B * N)) :
    dotB B u (nimSum (decodeBoard B N x)) = pm (maskU B N u) x := by
  induction N generalizing x with
  | zero => simp [decodeBoard, nimSum, maskU, pm, dotB_zero_right]
  | succ N ih =>
    have hl := mem_bitvecs_length hx
    have hdrop : x.drop B ∈ bitvecs (B * N) := mem_bitvecs_of_length (by
      rw [List.length_drop, hl, Nat.mul_succ]; omega)
    have htake : (x.take B).length = B := by rw [List.length_take]; rw [hl, Nat.mul_succ]; omega
    simp only [decodeBoard, nimSum, maskU]
    rw [dotB_xor_right, ih hdrop]
    conv => rhs; rw [← List.take_append_drop B x]
    rw [pm_append (by rw [length_toBitsBE, htake])]
    have := dot_toNatBE u (x.take B)
    rw [htake] at this
    rw [this]

/-- Number of ones in a bit list. -/
def ones (l : List Bool) : Nat := (l.filter id).length

theorem ones_append (l m : List Bool) : ones (l ++ m) = ones l + ones m := by
  simp [ones, List.filter_append]

theorem true_mem_toBitsBE {B u i : Nat} (hi : i < B) (hb : u.testBit i = true) :
    true ∈ toBitsBE B u := by
  induction B with
  | zero => omega
  | succ B ih =>
    simp only [toBitsBE, List.mem_cons]
    by_cases h : i = B
    · subst h; left; exact hb.symm
    · right; exact ih (by omega)

theorem ones_pos_of_mem {l : List Bool} (h : true ∈ l) : 1 ≤ ones l := by
  unfold ones
  exact List.length_pos_of_mem (a := true) (by simp [List.mem_filter, h])

theorem ones_toBitsBE_pos {B u : Nat} (hu0 : u ≠ 0) (hu : u < 2 ^ B) : 1 ≤ ones (toBitsBE B u) := by
  obtain ⟨i, hi⟩ := Nat.exists_testBit_of_ne_zero hu0
  have hiB : i < B := by
    rcases Nat.lt_or_ge i B with h | h
    · exact h
    · exfalso
      rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hu (Nat.pow_le_pow_right (by decide) h))] at hi
      cases hi
  exact ones_pos_of_mem (true_mem_toBitsBE hiB hi)

theorem ones_le_length (l : List Bool) : ones l ≤ l.length := List.length_filter_le _ _

theorem ones_maskU (B N u : Nat) : ones (maskU B N u) = N * ones (toBitsBE B u) := by
  induction N with
  | zero => simp [maskU, ones]
  | succ N ih => simp [maskU, ones_append, ih, Nat.succ_mul, Nat.add_comm]

/-! ## Restriction to the mask coordinates -/

/-- Number of zeros. -/
def zeros (l : List Bool) : Nat := (l.filter (fun b => !b)).length

theorem ones_add_zeros (l : List Bool) : ones l + zeros l = l.length := by
  induction l with
  | nil => rfl
  | cons b l ih => cases b <;> simp [ones, zeros, List.filter_cons] at * <;> omega

/-- Interleave y (mask coordinates) and ρ (other coordinates) according to the mask. -/
def merge : List Bool → List Bool → List Bool → List Bool
  | [], _, _ => []
  | true :: ms, ys, rs => ys.headD false :: merge ms ys.tail rs
  | false :: ms, ys, rs => rs.headD false :: merge ms ys rs.tail

/-- SPLITTING THE UNIFORM SUM over the mask / non-mask coordinates. -/
theorem rsum_bitvecs_merge : ∀ (mask : List Bool) (f : List Bool → Rat),
    rsum (bitvecs mask.length) f =
      rsum (bitvecs (zeros mask)) (fun ρ => rsum (bitvecs (ones mask)) (fun y => f (merge mask y ρ)))
  | [], f => by simp [bitvecs, merge, zeros, ones]
  | true :: ms, f => by
    have hz : zeros (true :: ms) = zeros ms := by simp [zeros]
    have ho : ones (true :: ms) = ones ms + 1 := by simp [ones]
    rw [hz, ho, List.length_cons, rsum_bitvecs_succ, rsum_bitvecs_merge ms, rsum_bitvecs_merge ms,
      ← rsum_add]
    apply rsum_congr; intro ρ _
    rw [rsum_bitvecs_succ]
    simp [merge]
  | false :: ms, f => by
    have hz : zeros (false :: ms) = zeros ms + 1 := by simp [zeros]
    have ho : ones (false :: ms) = ones ms := by simp [ones]
    rw [hz, ho, List.length_cons, rsum_bitvecs_succ, rsum_bitvecs_succ,
      rsum_bitvecs_merge ms, rsum_bitvecs_merge ms]
    simp [merge]

/-- Parity of all bits. -/
def par : List Bool → Bool
  | [] => false
  | b :: bs => xor b (par bs)

theorem pm_merge : ∀ (mask y ρ : List Bool), y.length = ones mask →
    pm mask (merge mask y ρ) = par y
  | [], y, _, hy => by
    simp [ones] at hy; subst hy; rfl
  | true :: ms, y, ρ, hy => by
    cases y with
    | nil => simp [ones] at hy
    | cons b y =>
      simp only [merge, List.headD_cons, List.tail_cons, pm, Bool.true_and, par]
      rw [pm_merge ms y ρ (by simpa [ones] using hy)]
  | false :: ms, y, ρ, hy => by
    simp only [merge, pm, Bool.false_and, Bool.false_xor]
    exact pm_merge ms y ρ.tail (by simpa [ones] using hy)

theorem length_merge : ∀ (mask y ρ : List Bool), (merge mask y ρ).length = mask.length
  | [], _, _ => rfl
  | true :: ms, y, ρ => by simp [merge, length_merge ms]
  | false :: ms, y, ρ => by simp [merge, length_merge ms]

/-- Rank of position j among the ones (resp. zeros) of the mask. -/
def rankT (mask : List Bool) (j : Nat) : Nat := ones (mask.take j)
def rankF (mask : List Bool) (j : Nat) : Nat := zeros (mask.take j)

theorem merge_getD : ∀ (mask y ρ : List Bool) (j : Nat), j < mask.length →
    (merge mask y ρ).getD j false =
      if mask.getD j false then y.getD (rankT mask j) false else ρ.getD (rankF mask j) false
  | [], _, _, j, hj => by simp at hj
  | true :: ms, y, ρ, 0, _ => by
    cases y <;> simp [merge, rankT, ones]
  | true :: ms, y, ρ, j + 1, hj => by
    simp only [merge, List.getD_cons_succ, List.getD_cons_succ]
    rw [merge_getD ms y.tail ρ j (by simpa using hj)]
    simp only [rankT, rankF, List.take_succ_cons, ones, zeros, List.filter_cons, id,
      if_true, Bool.not_true, Bool.false_eq_true, if_false, List.length_cons]
    cases y <;> cases ms.getD j false <;> simp
  | false :: ms, y, ρ, 0, _ => by
    cases ρ <;> simp [merge, rankF, zeros]
  | false :: ms, y, ρ, j + 1, hj => by
    simp only [merge, List.getD_cons_succ]
    rw [merge_getD ms y ρ.tail j (by simpa using hj)]
    simp only [rankT, rankF, List.take_succ_cons, ones, zeros, List.filter_cons, id,
      Bool.false_eq_true, if_false, Bool.not_false, if_true, List.length_cons]
    cases ρ <;> cases ms.getD j false <;> simp

theorem rankT_lt : ∀ (mask : List Bool) (j : Nat), mask.getD j false = true →
    rankT mask j < ones mask
  | [], j, h => by simp at h
  | true :: ms, 0, _ => by simp [rankT, ones]
  | false :: ms, 0, h => by simp at h
  | b :: ms, j + 1, h => by
    have := rankT_lt ms j (by simpa using h)
    simp only [rankT, ones, List.take_succ_cons, List.filter_cons] at this ⊢
    cases b <;> simp <;> omega

/-- Bit vector as an input assignment. -/
def vfun (x : List Bool) : Nat → Bool := fun j => x.getD j false

/-- The circuit with non-mask coordinates fixed to ρ and mask coordinates renamed
    to 0, 1, ..., ones mask - 1. -/
def restrictC (mask ρ : List Bool) (C : Circ) : Circ :=
  subst (fun j => if mask.getD j false then input (rankT mask j)
    else const (ρ.getD (rankF mask j) false)) C

theorem restrict_leaf (mask ρ : List Bool) (j : Nat) :
    IsLeaf (if mask.getD j false then input (rankT mask j)
      else const (ρ.getD (rankF mask j) false)) := by
  split <;> simp [IsLeaf]

/-- RESTRICTION PRESERVES SIZE AND DEPTH, and the result reads only the mask
    coordinates. -/
theorem restrictC_resources (mask ρ : List Bool) (C : Circ) :
    size (restrictC mask ρ C) = size C ∧ depth (restrictC mask ρ C) = depth C ∧
    maxInput (restrictC mask ρ C) ≤ ones mask := by
  refine ⟨size_subst_leaf _ (restrict_leaf mask ρ) C, depth_subst_leaf _ (restrict_leaf mask ρ) C, ?_⟩
  apply maxInput_subst_le
  intro j
  by_cases h : mask.getD j false = true
  · simp only [h, if_true, maxInput_input]; have := rankT_lt mask j h; omega
  · rw [if_neg h]; simp

theorem eval_restrictC {mask y ρ : List Bool} {C : Circ} (hC : maxInput C ≤ mask.length) :
    eval (vfun y) (restrictC mask ρ C) = eval (vfun (merge mask y ρ)) C := by
  unfold restrictC
  rw [eval_subst]
  apply eval_congr_below
  intro j hj
  have hjm : j < mask.length := Nat.lt_of_lt_of_le hj hC
  unfold vfun
  rw [merge_getD mask y ρ j hjm]
  split <;> simp

/-! ## The conditional bridge -/

def ind (b : Bool) : Rat := if b then 1 else 0
def sgn (b : Bool) : Rat := if b then -1 else 1

/-- THE CLASSICAL PARITY-CORRELATION PREMISE (explicit hypothesis, not proved):
    every formula of depth ≤ d and size ≤ s reading only m inputs has correlation
    at most ε with parity of those m bits under the uniform distribution. -/
def ParityCorrPremise (d s m : Nat) (ε : Rat) : Prop :=
  ∀ C : Circ, depth C ≤ d → size C ≤ s → maxInput C ≤ m →
    -ε ≤ rsum (bitvecs m) (fun y => ind (eval (vfun y) C) * sgn (par y)) / (2 : Rat) ^ m ∧
    rsum (bitvecs m) (fun y => ind (eval (vfun y) C) * sgn (par y)) / (2 : Rat) ^ m ≤ ε

theorem two_pow_pos' (n : Nat) : (0 : Rat) < (2 : Rat) ^ n := by
  have : ((2 ^ n : Nat) : Rat) = (2 : Rat) ^ n := by simp
  rw [← this]; exact Rat.natCast_pos.mpr (Nat.two_pow_pos n)

/-- RESTRICTION/AVERAGING BRIDGE: under the premise at m = ones mask, the
    correlation of any circuit (depth ≤ d, size ≤ s, reading only the |mask|
    coordinates) with the MASKED parity is at most ε. -/
theorem masked_correlation (mask : List Bool) (C : Circ) {d s : Nat} {ε : Rat}
    (hC : maxInput C ≤ mask.length) (hd : depth C ≤ d) (hs : size C ≤ s)
    (hprem : ParityCorrPremise d s (ones mask) ε) :
    -ε ≤ rsum (bitvecs mask.length) (fun x => ind (eval (vfun x) C) * sgn (pm mask x)) /
        (2 : Rat) ^ mask.length ∧
    rsum (bitvecs mask.length) (fun x => ind (eval (vfun x) C) * sgn (pm mask x)) /
        (2 : Rat) ^ mask.length ≤ ε := by
  rw [rsum_bitvecs_merge]
  have inner : ∀ ρ ∈ bitvecs (zeros mask),
      rsum (bitvecs (ones mask)) (fun y => ind (eval (vfun (merge mask y ρ)) C) *
        sgn (pm mask (merge mask y ρ))) =
      rsum (bitvecs (ones mask)) (fun y => ind (eval (vfun y) (restrictC mask ρ C)) * sgn (par y)) := by
    intro ρ _
    apply rsum_congr; intro y hy
    rw [eval_restrictC hC, pm_merge mask y ρ (mem_bitvecs_length hy)]
  rw [rsum_congr inner]
  have hres := fun ρ => restrictC_resources mask ρ C
  have hT := two_pow_pos' (ones mask)
  have hb : ∀ ρ ∈ bitvecs (zeros mask),
      -(ε * (2 : Rat) ^ ones mask) ≤
        rsum (bitvecs (ones mask)) (fun y => ind (eval (vfun y) (restrictC mask ρ C)) * sgn (par y)) ∧
      rsum (bitvecs (ones mask)) (fun y => ind (eval (vfun y) (restrictC mask ρ C)) * sgn (par y)) ≤
        ε * (2 : Rat) ^ ones mask := by
    intro ρ _
    obtain ⟨k1, k2⟩ := hprem (restrictC mask ρ C) (by rw [(hres ρ).2.1]; exact hd)
      (by rw [(hres ρ).1]; exact hs) (hres ρ).2.2
    generalize rsum (bitvecs (ones mask))
      (fun y => ind (eval (vfun y) (restrictC mask ρ C)) * sgn (par y)) = X at k1 k2 ⊢
    have hT' : (2 : Rat) ^ ones mask ≠ 0 := Rat.ne_of_gt hT
    have e : X / (2 : Rat) ^ ones mask * (2 : Rat) ^ ones mask = X := by grind
    have m1 := Rat.mul_le_mul_of_nonneg_right k1 (Rat.le_of_lt hT)
    have m2 := Rat.mul_le_mul_of_nonneg_right k2 (Rat.le_of_lt hT)
    rw [e] at m1 m2
    constructor <;> grind
  obtain ⟨b1, b2⟩ := rsum_bound hb
  rw [length_bitvecs] at b1 b2
  have hsplit : (2 : Rat) ^ mask.length = (2 : Rat) ^ zeros mask * (2 : Rat) ^ ones mask := by
    have h := ones_add_zeros mask
    have e : ∀ n : Nat, (2 : Rat) ^ n = ((2 ^ n : Nat) : Rat) := by intro n; simp
    rw [e, e, e, ← Rat.natCast_mul, ← Nat.pow_add, ← h, Nat.add_comm]
  have hN := two_pow_pos' mask.length
  have hN' : (2 : Rat) ^ mask.length ≠ 0 := Rat.ne_of_gt hN
  generalize rsum (bitvecs (zeros mask)) (fun ρ => rsum (bitvecs (ones mask))
    (fun y => ind (eval (vfun y) (restrictC mask ρ C)) * sgn (par y))) = S at b1 b2 ⊢
  have c1 : (((2 ^ zeros mask : Nat) : Rat)) = (2 : Rat) ^ zeros mask := by simp
  rw [c1] at b1 b2
  rw [hsplit] at hN' ⊢
  have hZ := two_pow_pos' (zeros mask)
  constructor
  · apply Rat.le_of_mul_le_mul_right _ (Rat.mul_pos hZ hT)
    have e : S / ((2 : Rat) ^ zeros mask * (2 : Rat) ^ ones mask) *
        ((2 : Rat) ^ zeros mask * (2 : Rat) ^ ones mask) = S := by grind
    rw [e]; grind
  · apply Rat.le_of_mul_le_mul_right _ (Rat.mul_pos hZ hT)
    have e : S / ((2 : Rat) ^ zeros mask * (2 : Rat) ^ ones mask) *
        ((2 : Rat) ^ zeros mask * (2 : Rat) ^ ones mask) = S := by grind
    rw [e]; grind

#print axioms mem_bitvecs_length
#print axioms rsum_bitvecs_succ
#print axioms rsum_bitvecs_add
#print axioms count_bitvecs
#print axioms toNatBE_lt
#print axioms rsum_range_bitvecs
#print axioms testBit_toNatBE
#print axioms rsum_boards_bitvecs
#print axioms length_decodeBoard
#print axioms decodeBoard_width
#print axioms mem_bitvecs_of_length
#print axioms length_toBitsBE
#print axioms pm_append
#print axioms length_maskU
#print axioms dotB_zero_right
#print axioms length_bitvecs
#print axioms dotB_congr_right
#print axioms dot_toNatBE
#print axioms chi_parity
#print axioms ones_append
#print axioms true_mem_toBitsBE
#print axioms ones_pos_of_mem
#print axioms ones_toBitsBE_pos
#print axioms ones_le_length
#print axioms ones_maskU
#print axioms ones_add_zeros
#print axioms rsum_bitvecs_merge
#print axioms pm_merge
#print axioms length_merge
#print axioms merge_getD
#print axioms rankT_lt
#print axioms restrict_leaf
#print axioms restrictC_resources
#print axioms eval_restrictC
#print axioms two_pow_pos'
#print axioms masked_correlation

end Bridge
end NimAudit
