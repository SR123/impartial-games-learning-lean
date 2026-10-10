import NoiseModel

/- Phase 8, part B: Fourier analysis on the Boolean cube, tails, the parity spectrum, and the
   unknown-index delta.  Written by Claude (10 October 2026).  Lean 4.26.0, core/Std only.

   Paper target: Section sec:spectral-view (Walsh–Hadamard characters, Fourier coefficients,
   inversion, the Fourier tail and (k, ε)-band-limited functions, parity as a pure
   character, nim-sum bits and delta bits).  Everything is proved for an arbitrary linearly
   ordered field R (Lean core's interface, as in NoiseModel); RealFourier.lean instantiates
   the results at Mathlib's ℝ.

   B1  The cube {0,1}^n is `bitvecs n` (no duplicates, exactly the lists of length n,
       2^n elements); characters are indexed by masks S ∈ bitvecs n (S ↔ the subset
       {i : S_i = 1}, a bijection, `mask_ext`/`ofPred_mem`).  χ_S(x) = (−1)^{|S ∩ x|}.
       Normalised inner product ⟨f,g⟩ = 2^{−n} Σ_x f(x)g(x) (uniform distribution),
       coefficients f̂(S) = ⟨f, χ_S⟩.  Orthonormality, inversion f = Σ_S f̂(S)χ_S for EVERY
       f on the cube, uniqueness of the expansion, Parseval, all n including n = 0;
       agreement with Misc.char_orth at ℚ.
   B2  |S| = number of ones; Tail_{>k}(f) = Σ_{|S|>k} f̂(S)²; (k, ε)-band-limited;
       exact degree.  χ_S has coefficient 1 at S and 0 elsewhere, exact degree |S|, tail
       1 below |S| and 0 from |S| on.  Nim-sum bit j is the character of a mask with N ones;
       the fixed-heap delta bit is a two-coordinate character.  Coefficient-versus-tail and
       sign-versus-indicator conventions; the classical spectral-tail theorem enters only
       as the named premise `TailPremise` (not proved, not assumed anywhere else).
   B3  The unknown-index delta, via the implemented total circuit LocalRestore.dC B N q
       on the FULL 2BN-bit cube: it agrees with the delta bit on every single-change
       transition, equals the two-coordinate character of heap i on transitions that
       change heap i, and for N ≥ 2, q < B its sign encoding is NOT ±(any character) and
       has at least two nonzero Fourier coefficients.  N = 1: it IS the two-coordinate
       character; N = 0 or q ≥ B: it is the constant character.  No claim is made about
       other total extensions of the promised-domain map. -/

namespace NimAudit
namespace Fourier

set_option linter.unusedSectionVars false

open Lean.Grind Std Bridge Noise AC0 AC0.Circ

/-! ## Boolean facts about masked parity (no field needed) -/

theorem pm_comm : ∀ (S x : List Bool), S.length = x.length → pm S x = pm x S
  | [], [], _ => rfl
  | s :: S, b :: x, h => by
    simp only [pm]; rw [pm_comm S x (by simpa using h), Bool.and_comm]
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

theorem pm_xor_right : ∀ (S x y : List Bool), x.length = y.length →
    pm S (List.zipWith xor x y) = xor (pm S x) (pm S y)
  | [], _, _, _ => by simp [pm]
  | _ :: _, [], [], _ => by simp [pm]
  | s :: S, b :: x, c :: y, h => by
    simp only [List.zipWith_cons_cons, pm]
    rw [pm_xor_right S x y (by simpa using h)]
    cases s <;> cases b <;> cases c <;> cases pm S x <;> cases pm S y <;> rfl
  | _ :: _, [], _ :: _, h => by simp at h
  | _ :: _, _ :: _, [], h => by simp at h

theorem pm_of_false : ∀ (S x : List Bool), (∀ s ∈ S, s = false) → pm S x = false
  | [], _, _ => rfl
  | _ :: _, [], _ => rfl
  | s :: S, b :: x, h => by
    simp only [pm]
    rw [h s (by simp), pm_of_false S x (fun t ht => h t (by simp [ht]))]; rfl

theorem pm_zeros_right : ∀ (S : List Bool) (n : Nat), pm S (List.replicate n false) = false
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | s :: S, n + 1 => by
    simp only [List.replicate_succ, pm, Bool.and_false, Bool.false_xor]; exact pm_zeros_right S n

/-- Number of coordinates selected by S at which x is 1, i.e. |S ∩ supp x|. -/
def selCount : List Bool → List Bool → Nat
  | m :: ms, b :: bs => (if m && b then 1 else 0) + selCount ms bs
  | _, _ => 0

theorem pm_selCount : ∀ (S x : List Bool), pm S x = decide (selCount S x % 2 = 1)
  | [], _ => by simp [pm, selCount]
  | _ :: _, [] => by simp [pm, selCount]
  | m :: ms, b :: bs => by
    simp only [pm, selCount]
    rw [pm_selCount ms bs]
    cases m <;> cases b <;> by_cases h : selCount ms bs % 2 = 1 <;> simp [h] <;> omega

/-! ### Masks as subsets: the character index set -/

theorem cube_mem {n : Nat} {x : List Bool} : x ∈ bitvecs n ↔ x.length = n :=
  ⟨mem_bitvecs_length, mem_bitvecs_of_length⟩

theorem nodup_map_cons (b : Bool) : ∀ l : List (List Bool), l.Nodup → (l.map (b :: ·)).Nodup
  | [], _ => by simp
  | a :: l, h => by
    rw [List.nodup_cons] at h
    rw [List.map_cons, List.nodup_cons]
    refine ⟨fun hm => ?_, nodup_map_cons b l h.2⟩
    obtain ⟨x, hx, e⟩ := List.mem_map.1 hm
    injection e with _ e2
    exact h.1 (e2 ▸ hx)

theorem cube_nodup : ∀ n, (bitvecs n).Nodup
  | 0 => by simp [bitvecs]
  | n + 1 => by
    simp only [bitvecs]
    rw [List.nodup_append]
    refine ⟨?_, ?_, ?_⟩
    · exact nodup_map_cons false _ (cube_nodup n)
    · exact nodup_map_cons true _ (cube_nodup n)
    · intro a ha b hb hab
      simp only [List.mem_map] at ha hb
      obtain ⟨u, _, rfl⟩ := ha
      obtain ⟨v, _, rfl⟩ := hb
      simp at hab

theorem cube_card (n : Nat) : (bitvecs n).length = 2 ^ n := length_bitvecs n

/-- The mask of a subset given by its characteristic predicate on [n]. -/
def ofPred (n : Nat) (A : Nat → Bool) : List Bool := (List.range n).map A

theorem ofPred_mem (n : Nat) (A : Nat → Bool) : ofPred n A ∈ bitvecs n :=
  cube_mem.2 (by simp [ofPred])

theorem ofPred_getD (n : Nat) (A : Nat → Bool) (j : Nat) :
    (ofPred n A).getD j false = (decide (j < n) && A j) := by
  simp only [ofPred, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range]
  by_cases h : j < n <;> simp [h]

/-- Masks are determined by their membership predicate (no duplicate indices). -/
theorem mask_ext {n : Nat} {S T : List Bool} (hS : S ∈ bitvecs n) (hT : T ∈ bitvecs n)
    (h : ∀ j, j < n → S.getD j false = T.getD j false) : S = T := by
  have hl1 := mem_bitvecs_length hS
  have hl2 := mem_bitvecs_length hT
  apply List.ext_getElem (by omega)
  intro j h1 h2
  have := h j (by omega)
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1, List.getElem?_eq_getElem h2,
    Option.getD_some] at this
  exact this

/-- Every subset of [n] has its mask (no missing indices). -/
theorem mask_of_subset (n : Nat) (A : Nat → Bool) :
    ∃ S ∈ bitvecs n, ∀ j, j < n → S.getD j false = A j :=
  ⟨ofPred n A, ofPred_mem n A, fun j hj => by rw [ofPred_getD]; simp [hj]⟩

section Generic

variable {R : Type} [Field R] [LE R] [LT R] [LawfulOrderLT R] [IsLinearOrder R] [OrderedRing R]

attribute [local instance] Semiring.natCast

/-! ## Elementary field facts -/

theorem two_pos' : (0 : R) < 2 := by
  have := OrderedRing.zero_lt_one (R := R); grind

theorem two_pow_pos'' : ∀ n : Nat, (0 : R) < 2 ^ n
  | 0 => by rw [Semiring.pow_zero]; exact OrderedRing.zero_lt_one
  | n + 1 => by rw [Semiring.pow_succ]; exact OrderedRing.mul_pos (two_pow_pos'' n) two_pos'

theorem two_pow_ne (n : Nat) : (2 : R) ^ n ≠ 0 := fun h => by
  have := two_pow_pos'' (R := R) n; rw [h] at this; exact Preorder.lt_irrefl _ this

theorem pow_mul_inv (n : Nat) : (2 : R) ^ n * ((2 : R) ^ n)⁻¹ = 1 := Field.mul_inv_cancel (two_pow_ne n)

theorem one_ne_neg_one : (1 : R) ≠ -1 := by
  intro h; have := two_pos' (R := R); grind

theorem sg_xor (a b : Bool) : (sg (xor a b) : R) = sg a * sg b := by
  cases a <;> cases b <;> simp only [sg, Bool.xor_false, Bool.xor_true, Bool.not_false, Bool.not_true,
    Bool.false_eq_true, if_true, if_false] <;> grind

theorem sg_mul_self (b : Bool) : (sg b : R) * sg b = 1 := by
  cases b <;> simp only [sg, Bool.false_eq_true, if_true, if_false] <;> grind

theorem gs_mul_right {α : Type} (l : List α) (c : R) (f : α → R) :
    gs l (fun a => f a * c) = gs l f * c := by
  rw [show (fun a => f a * c) = (fun a => c * f a) by funext a; grind, gs_mul_left]; grind

theorem gs_count (n : Nat) : gs (bitvecs n) (fun _ => (1 : R)) = 2 ^ n := by
  induction n with
  | zero => simp only [bitvecs, gs_cons, gs_nil, Semiring.pow_zero]; grind
  | succ n ih => rw [gs_bitvecs_succ, ih, Semiring.pow_succ]; grind

theorem gs_single_le {α : Type} {l : List α} {g : α → R} (h : ∀ a ∈ l, 0 ≤ g a) {x : α} (hx : x ∈ l) :
    g x ≤ gs l g := by
  induction l with
  | nil => simp at hx
  | cons a l ih =>
    simp only [gs_cons]
    have hrest : 0 ≤ gs l g := gs_nonneg (fun b hb => h b (by simp [hb]))
    rcases List.mem_cons.mp hx with rfl | hx
    · grind
    · have := ih (fun b hb => h b (by simp [hb])) hx
      have := h a (by simp); grind

/-! ## B1. Characters, inner product, coefficients -/

/-- The Walsh–Hadamard character χ_S(x) = (−1)^{⟨S,x⟩}. -/
def chi (S x : List Bool) : R := sg (pm S x)

/-- χ_S(x) = (−1)^{Σ_{i∈S} x_i} (the paper's formula). -/
theorem chi_pow (S x : List Bool) : (chi S x : R) = (-1) ^ selCount S x := by
  unfold chi; rw [pm_selCount]
  generalize selCount S x = k
  induction k with
  | zero => simp [sg, Semiring.pow_zero]
  | succ k ih =>
    rw [Semiring.pow_succ, ← ih]
    by_cases h : k % 2 = 1
    · have : ¬ ((k + 1) % 2 = 1) := by omega
      simp only [sg, decide_eq_true_eq, h, this, if_true, if_false]; grind
    · have : (k + 1) % 2 = 1 := by omega
      simp only [sg, decide_eq_true_eq, h, this, if_true, if_false]; grind

/-- Normalised inner product under the uniform distribution on {0,1}^n. -/
def ip (n : Nat) (f g : List Bool → R) : R := gs (bitvecs n) (fun x => f x * g x) * ((2 : R) ^ n)⁻¹

/-- Fourier coefficient f̂(S) = E_x[f(x) χ_S(x)]. -/
def coef (n : Nat) (f : List Bool → R) (S : List Bool) : R := ip n f (chi S)

theorem coef_congr {n : Nat} {f g : List Bool → R} (h : ∀ x ∈ bitvecs n, f x = g x) (S : List Bool) :
    coef n f S = coef n g S := by
  unfold coef ip; rw [gs_congr (fun x hx => by rw [h x hx])]

theorem chi_mul_left {S T : List Bool} (h : S.length = T.length) (x : List Bool) :
    (chi S x : R) * chi T x = chi (List.zipWith xor S T) x := by
  unfold chi; rw [Misc.pm_zipWith S T x h, sg_xor]

theorem chi_mul_right (S : List Bool) {x y : List Bool} (h : x.length = y.length) :
    (chi S x : R) * chi S y = chi S (List.zipWith xor x y) := by
  unfold chi; rw [pm_xor_right S x y h, sg_xor]

theorem chi_zeros (S : List Bool) (n : Nat) : (chi S (List.replicate n false) : R) = 1 := by
  unfold chi; rw [pm_zeros_right]; simp [sg]

/-- Character sums: Σ_x χ_U(x) = 2^n if U = 0 and 0 otherwise. -/
theorem char_sum_gen : ∀ U : List Bool,
    gs (bitvecs U.length) (fun x => (chi U x : R)) = if U.all (fun b => b == false) then (2 : R) ^ U.length else 0
  | [] => by simp only [List.length_nil, bitvecs, gs_cons, gs_nil, chi, pm, sg, List.all_nil,
      Bool.false_eq_true, if_false, if_true, Semiring.pow_zero]; grind
  | u :: U => by
    simp only [List.length_cons]
    rw [gs_bitvecs_succ]
    have ih := char_sum_gen U
    cases u
    · have e1 : ∀ v, (chi (false :: U) (false :: v) : R) = chi U v := by intro v; simp [chi, pm]
      have e2 : ∀ v, (chi (false :: U) (true :: v) : R) = chi U v := by intro v; simp [chi, pm]
      rw [gs_congr (fun v _ => e1 v), gs_congr (fun v _ => e2 v), ih]
      simp only [List.all_cons, beq_self_eq_true, Bool.true_and]
      split
      · rw [Semiring.pow_succ]; grind
      · grind
    · have e1 : ∀ v, (chi (true :: U) (false :: v) : R) = chi U v := by intro v; simp [chi, pm]
      have e2 : ∀ v, (chi (true :: U) (true :: v) : R) = (-1) * chi U v := by
        intro v; simp only [chi, pm, Bool.true_and]; rw [sg_xor]; simp only [sg, if_true]
      rw [gs_congr (fun v _ => e1 v), gs_congr (fun v _ => e2 v), gs_mul_left, ih]
      simp only [List.all_cons]
      simp only [show ((true == false) && U.all (fun b => b == false)) = false by rfl, Bool.false_eq_true, if_false]
      split <;> grind

theorem zipWith_length_eq {S T : List Bool} (h : S.length = T.length) : (List.zipWith xor S T).length = S.length := by
  simp [h]

/-- Unnormalised orthogonality. -/
theorem orth_sum {n : Nat} {S T : List Bool} (hS : S ∈ bitvecs n) (hT : T ∈ bitvecs n) :
    gs (bitvecs n) (fun x => (chi S x : R) * chi T x) = if S = T then (2 : R) ^ n else 0 := by
  have h1 := mem_bitvecs_length hS
  have h2 := mem_bitvecs_length hT
  have hl : S.length = T.length := by omega
  rw [gs_congr (fun x _ => chi_mul_left hl x)]
  have hs := char_sum_gen (R := R) (List.zipWith xor S T)
  rw [zipWith_length_eq hl, h1] at hs
  rw [hs]
  by_cases hST : S = T
  · rw [if_pos ((Misc.zipWith_xor_all_false S T hl).2 hST), if_pos hST]
  · rw [if_neg (fun h' => hST ((Misc.zipWith_xor_all_false S T hl).1 h')), if_neg hST]

/-- B1. ORTHONORMALITY of the characters under the uniform distribution. -/
theorem orthonormal {n : Nat} {S T : List Bool} (hS : S ∈ bitvecs n) (hT : T ∈ bitvecs n) :
    ip n (chi S) (chi T) = (if S = T then 1 else 0 : R) := by
  unfold ip; rw [orth_sum hS hT]
  split
  · exact pow_mul_inv n
  · grind

/-- Dual orthogonality: Σ_S χ_S(x) χ_S(y) = 2^n [x = y]. -/
theorem dual_sum {n : Nat} {x y : List Bool} (hx : x ∈ bitvecs n) (hy : y ∈ bitvecs n) :
    gs (bitvecs n) (fun S => (chi S x : R) * chi S y) = if x = y then (2 : R) ^ n else 0 := by
  have h1 := mem_bitvecs_length hx
  have h2 := mem_bitvecs_length hy
  have hl : x.length = y.length := by omega
  have e : ∀ S ∈ bitvecs n, (chi S x : R) * chi S y = chi (List.zipWith xor x y) S := by
    intro S hS
    have hS' := mem_bitvecs_length hS
    rw [chi_mul_right S hl]; unfold chi
    rw [pm_comm S _ (by rw [zipWith_length_eq hl]; omega)]
  rw [gs_congr e]
  have hs := char_sum_gen (R := R) (List.zipWith xor x y)
  rw [zipWith_length_eq hl, h1] at hs
  rw [hs]
  by_cases hxy : x = y
  · rw [if_pos ((Misc.zipWith_xor_all_false x y hl).2 hxy), if_pos hxy]
  · rw [if_neg (fun h' => hxy ((Misc.zipWith_xor_all_false x y hl).1 h')), if_neg hxy]

/-- B1. FOURIER INVERSION (completeness): every f on the cube is the sum of its Fourier
    series, f(x) = Σ_S f̂(S) χ_S(x). -/
theorem inversion (n : Nat) (f : List Bool → R) {x : List Bool} (hx : x ∈ bitvecs n) :
    gs (bitvecs n) (fun S => coef n f S * chi S x) = f x := by
  have hlx := mem_bitvecs_length hx
  have e1 : ∀ S, coef n f S * chi S x =
      gs (bitvecs n) (fun y => (((2 : R) ^ n)⁻¹ * f y) * (chi S y * chi S x)) := by
    intro S
    unfold coef ip
    rw [show (fun y => (((2 : R) ^ n)⁻¹ * f y) * (chi S y * chi S x)) =
      (fun y => (f y * chi S y) * (((2 : R) ^ n)⁻¹ * chi S x)) by funext y; grind, gs_mul_right]
    grind
  rw [gs_congr (fun S _ => e1 S), gs_comm]
  have e2 : ∀ y ∈ bitvecs n, gs (bitvecs n) (fun S => (((2 : R) ^ n)⁻¹ * f y) * (chi S y * chi S x)) =
      Noise.ind (decide (x = y)) * (((2 : R) ^ n)⁻¹ * f y * 2 ^ n) := by
    intro y hy
    rw [gs_mul_left, dual_sum hy hx]
    by_cases hxy : x = y
    · subst hxy; simp only [if_true, decide_true, Noise.ind]; grind
    · rw [if_neg (fun h => hxy h.symm)]; simp only [decide_eq_true_eq, hxy, decide_false, Noise.ind,
        Bool.false_eq_true, if_false]; grind
  rw [gs_congr e2, gs_point n x hlx (fun y => ((2 : R) ^ n)⁻¹ * f y * 2 ^ n)]
  have := pow_mul_inv (R := R) n
  grind

/-- B1. UNIQUENESS of the expansion: any coefficient family representing f on the cube is
    the family of Fourier coefficients. -/
theorem uniqueness (n : Nat) (f : List Bool → R) (c : List Bool → R)
    (h : ∀ x ∈ bitvecs n, f x = gs (bitvecs n) (fun T => c T * chi T x)) :
    ∀ S ∈ bitvecs n, coef n f S = c S := by
  intro S hS
  have hlS := mem_bitvecs_length hS
  unfold coef ip
  rw [gs_congr (fun x hx => by rw [h x hx])]
  have e1 : ∀ x, gs (bitvecs n) (fun T => c T * chi T x) * chi S x =
      gs (bitvecs n) (fun T => c T * (chi T x * chi S x)) := by
    intro x; rw [← gs_mul_right]; apply gs_congr; intro T _; grind
  rw [gs_congr (fun x _ => e1 x), gs_comm]
  have e2 : ∀ T ∈ bitvecs n, gs (bitvecs n) (fun x => c T * (chi T x * chi S x)) =
      Noise.ind (decide (S = T)) * (c T * 2 ^ n) := by
    intro T hT
    rw [gs_mul_left, orth_sum hT hS]
    by_cases hST : S = T
    · subst hST; simp only [if_true, decide_true, Noise.ind]; grind
    · rw [if_neg (fun h => hST h.symm)]; simp only [decide_eq_true_eq, hST, decide_false, Noise.ind,
        Bool.false_eq_true, if_false]; grind
  rw [gs_congr e2, gs_point n S hlS (fun T => c T * 2 ^ n)]
  have := pow_mul_inv (R := R) n
  grind

/-- B1. PARSEVAL: ⟨f, g⟩ = Σ_S f̂(S) ĝ(S). -/
theorem parseval (n : Nat) (f g : List Bool → R) :
    ip n f g = gs (bitvecs n) (fun S => coef n f S * coef n g S) := by
  unfold ip
  rw [gs_congr (fun x hx => by rw [← inversion n g hx])]
  have e1 : ∀ x, f x * gs (bitvecs n) (fun S => coef n g S * chi S x) =
      gs (bitvecs n) (fun S => coef n g S * (f x * chi S x)) := by
    intro x; rw [← gs_mul_left]; apply gs_congr; intro S _; grind
  rw [gs_congr (fun x _ => e1 x), gs_comm, ← gs_mul_right]
  apply gs_congr; intro S _
  rw [gs_mul_left]; unfold coef ip; grind

theorem plancherel (n : Nat) (f : List Bool → R) :
    ip n f f = gs (bitvecs n) (fun S => coef n f S ^ 2) := by
  rw [parseval]; apply gs_congr; intro S _; grind

/-- n = 0: the cube is {[]}, χ_[] = 1 and f̂([]) = f([]). -/
theorem dim_zero (f : List Bool → R) : bitvecs 0 = [[]] ∧ coef 0 f [] = f [] := by
  refine ⟨rfl, ?_⟩
  simp only [coef, ip, bitvecs, gs_cons, gs_nil, chi, pm, sg, Bool.false_eq_true, if_false, Semiring.pow_zero]
  have := pow_mul_inv (R := R) 0
  rw [Semiring.pow_zero] at this; grind

/-! ## B2. Degrees, tails, band-limited functions -/

/-- Degree-> k Fourier tail Tail_{>k}(f) = Σ_{|S| > k} f̂(S)². -/
def tail (n : Nat) (f : List Bool → R) (k : Nat) : R :=
  gs (bitvecs n) (fun S => if k < ones S then coef n f S ^ 2 else 0)

/-- (k, ε)-spectrally band-limited. -/
def BandLimited (n : Nat) (f : List Bool → R) (k : Nat) (ε : R) : Prop := tail n f k ≤ ε

/-- Fourier degree at most k. -/
def DegLe (n : Nat) (f : List Bool → R) (k : Nat) : Prop := ∀ T ∈ bitvecs n, k < ones T → coef n f T = 0

/-- Exact Fourier degree d. -/
def ExactDeg (n : Nat) (f : List Bool → R) (d : Nat) : Prop :=
  DegLe n f d ∧ ∃ T ∈ bitvecs n, ones T = d ∧ coef n f T ≠ 0

theorem tail_nonneg (n : Nat) (f : List Bool → R) (k : Nat) : 0 ≤ tail n f k :=
  gs_nonneg (fun S _ => by split; exact OrderedRing.sq_nonneg; exact Std.le_refl _)

theorem tail_congr {n : Nat} {f g : List Bool → R} (h : ∀ x ∈ bitvecs n, f x = g x) (k : Nat) :
    tail n f k = tail n g k := by
  unfold tail; apply gs_congr; intro S _; rw [coef_congr h]

theorem exactDeg_unique {n : Nat} {f : List Bool → R} {d d' : Nat} (h : ExactDeg n f d) (h' : ExactDeg n f d') :
    d = d' := by
  obtain ⟨hd, T, hT, hTd, hne⟩ := h
  obtain ⟨hd', T', hT', hTd', hne'⟩ := h'
  have a : ¬ d < d' := fun hlt => hne' (hd T' hT' (by omega))
  have b : ¬ d' < d := fun hlt => hne (hd' T hT (by omega))
  omega

theorem tail_of_degLe {n : Nat} {f : List Bool → R} {k : Nat} (h : DegLe n f k) : tail n f k = 0 := by
  unfold tail
  rw [gs_congr (fun S hS => by
    show (if k < ones S then coef n f S ^ 2 else 0) = (fun _ => (0 : R)) S
    split
    · next hk => rw [h S hS hk]; grind
    · rfl), gs_zero]

/-- COEFFICIENT VERSUS TAIL: every coefficient above degree k is bounded by the tail. -/
theorem coef_sq_le_tail {n : Nat} (f : List Bool → R) {k : Nat} {S : List Bool} (hS : S ∈ bitvecs n)
    (hk : k < ones S) : coef n f S ^ 2 ≤ tail n f k := by
  have := gs_single_le (l := bitvecs n) (g := fun T => if k < ones T then coef n f T ^ 2 else 0)
    (fun T _ => by dsimp only; split; exact OrderedRing.sq_nonneg; exact Std.le_refl _) hS
  simp only [hk, if_true] at this
  exact this

/-- A (k, ε)-band-limited function has squared correlation ≤ ε with every character of
    degree > k. -/
theorem bandLimited_corr {n : Nat} {f : List Bool → R} {k : Nat} {ε : R} (hb : BandLimited n f k ε)
    {S : List Bool} (hS : S ∈ bitvecs n) (hk : k < ones S) : ip n f (chi S) ^ 2 ≤ ε :=
  Std.le_trans (coef_sq_le_tail f hS hk) hb

/-- ±1-valued functions have total Fourier mass 1. -/
theorem sign_mass (n : Nat) (f : List Bool → R) (h : ∀ x ∈ bitvecs n, f x * f x = 1) :
    gs (bitvecs n) (fun S => coef n f S ^ 2) = 1 := by
  rw [← plancherel]; unfold ip
  rw [gs_congr h, gs_count, pow_mul_inv]

theorem tail_le_one (n : Nat) (f : List Bool → R) (h : ∀ x ∈ bitvecs n, f x * f x = 1) (k : Nat) :
    tail n f k ≤ 1 := by
  rw [← sign_mass n f h]
  apply gs_le; intro S _
  split
  · exact Std.le_refl _
  · exact OrderedRing.sq_nonneg

/-- PARITY IS A PURE CHARACTER: the coefficient of χ_S is 1 at S and 0 elsewhere. -/
theorem coef_chi {n : Nat} {S T : List Bool} (hS : S ∈ bitvecs n) (hT : T ∈ bitvecs n) :
    coef n (chi S) T = (if T = S then 1 else 0 : R) := by
  unfold coef; rw [orthonormal hS hT]
  by_cases h : S = T
  · subst h; simp
  · rw [if_neg h, if_neg (fun e => h e.symm)]

/-- … hence its tail is 1 below degree |S| and 0 from |S| on. -/
theorem tail_chi {n : Nat} {S : List Bool} (hS : S ∈ bitvecs n) (k : Nat) :
    tail n (chi S) k = (if k < ones S then 1 else 0 : R) := by
  unfold tail
  have hl := mem_bitvecs_length hS
  rw [gs_congr (fun T hT => by
    show (if k < ones T then coef n (chi S) T ^ 2 else 0) =
      Noise.ind (decide (S = T)) * (if k < ones T then (1 : R) else 0)
    rw [coef_chi hS hT]
    by_cases hTS : T = S
    · subst hTS; simp only [if_true, decide_true, Noise.ind]; split <;> grind
    · simp only [hTS, if_false, show decide (S = T) = false from decide_eq_false (fun e => hTS e.symm), Noise.ind,
        Bool.false_eq_true]; split <;> grind)]
  rw [gs_point n S hl (fun T => if k < ones T then (1 : R) else 0)]

/-- … and its exact degree is |S|. -/
theorem chi_exactDeg {n : Nat} {S : List Bool} (hS : S ∈ bitvecs n) : ExactDeg n (chi (R := R) S) (ones S) := by
  refine ⟨fun T hT hk => ?_, S, hS, rfl, ?_⟩
  · rw [coef_chi hS hT, if_neg (fun e => by subst e; omega)]
  · rw [coef_chi hS hS, if_pos rfl]
    intro h; have := OrderedRing.zero_lt_one (R := R); rw [h] at this; exact Preorder.lt_irrefl _ this

theorem bandLimited_chi {n : Nat} {S : List Bool} (hS : S ∈ bitvecs n) (k : Nat) (ε : R) :
    BandLimited n (chi S) k ε ↔ (if k < ones S then 1 else 0 : R) ≤ ε := by
  unfold BandLimited; rw [tail_chi hS]

/-! ### Signed versus indicator conventions -/

theorem sg_eq_ind (b : Bool) : (sg b : R) = 1 - 2 * Noise.ind b := by
  cases b <;> simp only [sg, Noise.ind, Bool.false_eq_true, if_true, if_false] <;> grind

theorem coef_one {n : Nat} {S : List Bool} (hS : S ∈ bitvecs n) :
    coef n (fun _ => (1 : R)) S = if S.all (fun b => b == false) then 1 else 0 := by
  have hl := mem_bitvecs_length hS
  unfold coef ip
  rw [show (fun x => (1 : R) * chi S x) = (fun x => chi S x) by funext x; grind]
  have := char_sum_gen (R := R) S
  rw [hl] at this; rw [this]
  split
  · exact pow_mul_inv n
  · grind

/-- SIGNED VERSUS INDICATOR: for a Boolean function g, the sign encoding (−1)^g and the
    0/1 indicator have coefficients related by f̂_sign(S) = [S = 0] − 2·f̂_ind(S); in
    particular f̂_sign(S) = −2·f̂_ind(S) for every nonempty S. -/
theorem sign_indicator (n : Nat) (g : List Bool → Bool) {S : List Bool} (hS : S ∈ bitvecs n) :
    coef n (fun x => (sg (g x) : R)) S =
      (if S.all (fun b => b == false) then 1 else 0) - 2 * coef n (fun x => (Noise.ind (g x) : R)) S := by
  rw [← coef_one hS]
  unfold coef ip
  rw [← gs_mul_right, ← gs_mul_right, ← gs_mul_right]
  rw [show (2 : R) * gs (bitvecs n) (fun x => Noise.ind (g x) * chi S x * ((2 : R) ^ n)⁻¹) =
      gs (bitvecs n) (fun x => 2 * (Noise.ind (g x) * chi S x * ((2 : R) ^ n)⁻¹)) by rw [gs_mul_left], ← gs_sub]
  apply gs_congr; intro x _; dsimp only; rw [sg_eq_ind]; grind

theorem par_eq_pm : ∀ y : List Bool, par y = pm (List.replicate y.length true) y
  | [] => rfl
  | b :: y => by simp only [par, List.length_cons, List.replicate_succ, pm, Bool.true_and]; rw [par_eq_pm y]

/-! ### The named external spectral-tail input (LMN / Tal type), as a premise only -/

/-- NAMED EXTERNAL PREMISE (not proved here, not assumed by any other theorem): every
    formula of depth ≤ d and size ≤ M reading only inputs below n has degree-> k tail of its
    sign encoding at most η.  Classical results of Linial–Mansour–Nisan and Tal give such η. -/
def TailPremise (n d M k : Nat) (η : R) : Prop :=
  ∀ C : Circ, depth C ≤ d → size C ≤ M → maxInput C ≤ n → tail n (fun x => sg (eval (vfun x) C)) k ≤ η

/-! ## B2. Nim-sum bits and delta bits as characters -/

/-- Sign encoding of bit j of the nim-sum of the decoded board. -/
def nimBitSign (B N j : Nat) (x : List Bool) : R := sg ((nimSum (decodeBoard B N x)).testBit j)

theorem maskU_mem (B N u : Nat) : maskU B N u ∈ bitvecs (B * N) :=
  mem_bitvecs_of_length (length_maskU B N u)

theorem nimBitSign_chi {B N j : Nat} (hj : j < B) {x : List Bool} (hx : x ∈ bitvecs (B * N)) :
    (nimBitSign B N j x : R) = chi (maskU B N (2 ^ j)) x := by
  unfold nimBitSign chi; rw [(Misc.nimsum_bit_character hj hx).1]

/-- NIM-SUM BIT j: Fourier coefficient 1 at the mask with exactly N ones (one per heap) and 0
    elsewhere; exact degree N; tail 1 below N and 0 from N on. -/
theorem nimBit_spectrum {B N j : Nat} (hj : j < B) :
    (∀ T ∈ bitvecs (B * N), coef (B * N) (nimBitSign (R := R) B N j) T = if T = maskU B N (2 ^ j) then 1 else 0) ∧
    ones (maskU B N (2 ^ j)) = N ∧
    ExactDeg (B * N) (nimBitSign (R := R) B N j) N ∧
    ∀ k, tail (B * N) (nimBitSign (R := R) B N j) k = if k < N then 1 else 0 := by
  have hc : ∀ x ∈ bitvecs (B * N), (nimBitSign B N j x : R) = chi (maskU B N (2 ^ j)) x :=
    fun x hx => nimBitSign_chi hj hx
  have hones : ones (maskU B N (2 ^ j)) = N := (Misc.nimsum_bit_character hj (x := maskU B N (2 ^ j))
    (maskU_mem B N _)).2
  refine ⟨fun T hT => by rw [coef_congr hc, coef_chi (maskU_mem B N _) hT], hones, ?_, fun k => ?_⟩
  · have h := chi_exactDeg (R := R) (maskU_mem B N (2 ^ j))
    rw [hones] at h
    exact ⟨fun T hT hk => by rw [coef_congr hc]; exact h.1 T hT hk,
      let ⟨T, hT, h1, h2⟩ := h.2; ⟨T, hT, h1, by rw [coef_congr hc]; exact h2⟩⟩
  · rw [tail_congr hc, tail_chi (maskU_mem B N _), hones]

/-- A paper-specific application of the named tail premise, with the actual support size: a
    formula of depth ≤ d and size ≤ M reading the B·N board bits has squared correlation at
    most η with nim-sum bit j (a character of degree N), provided the premise holds at some
    k < N. -/
theorem nimBit_corr_of_tail {B N j d M k : Nat} {η : R} (hj : j < B) (hk : k < N)
    (hT : TailPremise (B * N) d M k η) (C : Circ) (hd : depth C ≤ d) (hs : size C ≤ M) (hm : maxInput C ≤ B * N) :
    ip (B * N) (fun x => sg (eval (vfun x) C)) (nimBitSign B N j) ^ 2 ≤ η := by
  have hc : ∀ x ∈ bitvecs (B * N), (nimBitSign B N j x : R) = chi (maskU B N (2 ^ j)) x :=
    fun x hx => nimBitSign_chi hj hx
  have e : ip (B * N) (fun x => sg (eval (vfun x) C)) (nimBitSign B N j) =
      coef (R := R) (B * N) (fun x => sg (eval (vfun x) C)) (maskU B N (2 ^ j)) := by
    unfold coef ip; apply congrArg (· * _); apply gs_congr; intro x hx; rw [hc x hx]
  rw [e]
  have hones := (Misc.nimsum_bit_character hj (x := maskU B N (2 ^ j)) (maskU_mem B N _)).2
  exact Std.le_trans (coef_sq_le_tail _ (maskU_mem B N _) (by rw [hones]; exact hk)) (hT C hd hs hm)

/-- Sign of bit j of a ⊕ b, as a function of the two B-bit blocks (u, v) of a = old and
    b = new value of one heap. -/
def deltaSign (B j : Nat) (w : List Bool) : R := sg ((toNatBE (w.take B) ^^^ toNatBE (w.drop B)).testBit j)

theorem decode_two (B : Nat) {w : List Bool} (hw : w ∈ bitvecs (B * 2)) :
    nimSum (decodeBoard B 2 w) = toNatBE (w.take B) ^^^ toNatBE (w.drop B) := by
  have hl := mem_bitvecs_length hw
  have : (w.drop B).take B = w.drop B := List.take_of_length_le (by rw [List.length_drop]; omega)
  simp only [decodeBoard, nimSum, this, Nat.xor_zero]

/-- FIXED-HEAP DELTA BITS ARE TWO-COORDINATE CHARACTERS: on the 2B-bit cube of the changed
    heap's old and new blocks, the sign of delta bit j is χ of a mask with exactly two ones;
    its exact degree is 2.  With Misc.delta_bit_local this is the delta of every legal move
    that changes that heap. -/
theorem delta_spectrum {B j : Nat} (hj : j < B) :
    (∀ w ∈ bitvecs (B * 2), (deltaSign B j w : R) = chi (maskU B 2 (2 ^ j)) w) ∧
    ones (maskU B 2 (2 ^ j)) = 2 ∧ ExactDeg (B * 2) (deltaSign (R := R) B j) 2 := by
  have hc : ∀ w ∈ bitvecs (B * 2), (deltaSign B j w : R) = chi (maskU B 2 (2 ^ j)) w := by
    intro w hw
    have := nimBitSign_chi (R := R) (N := 2) hj hw
    unfold nimBitSign at this; unfold deltaSign; rw [← decode_two B hw]; exact this
  have hones := (Misc.nimsum_bit_character hj (N := 2) (x := maskU B 2 (2 ^ j)) (maskU_mem B 2 _)).2
  refine ⟨hc, hones, ?_⟩
  have h := chi_exactDeg (R := R) (maskU_mem B 2 (2 ^ j))
  rw [hones] at h
  exact ⟨fun T hT hk => by rw [coef_congr hc]; exact h.1 T hT hk,
    let ⟨T, hT, h1, h2⟩ := h.2; ⟨T, hT, h1, by rw [coef_congr hc]; exact h2⟩⟩

theorem delta_move_chi {B j : Nat} (hj : j < B) {u v : List Bool} (hu : u ∈ bitvecs B) (hv : v ∈ bitvecs B)
    {pre post : List Nat} :
    (sg ((nimSum (pre ++ toNatBE u :: post) ^^^ nimSum (pre ++ toNatBE v :: post)).testBit j) : R) =
      chi (maskU B 2 (2 ^ j)) (u ++ v) := by
  have hlu := mem_bitvecs_length hu
  have huv : u ++ v ∈ bitvecs (B * 2) := mem_bitvecs_of_length (by simp [hlu, mem_bitvecs_length hv]; omega)
  rw [← (delta_spectrum (R := R) hj).1 _ huv]
  unfold deltaSign
  rw [LocalRestore.delta_oneChange, List.take_left' hlu, List.drop_left' hlu]

/-! ## B3. The unknown-index delta: the total circuit LocalRestore.dC on the full cube -/

/-- Single-point mask. -/
def pt (n a : Nat) : List Bool := (List.range n).map (fun i => decide (i = a))

theorem pt_mem (n a : Nat) : pt n a ∈ bitvecs n := mem_bitvecs_of_length (by simp [pt])

theorem pt_getD (n a j : Nat) : (pt n a).getD j false = (decide (j = a) && decide (j < n)) := by
  simp only [pt, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range]
  by_cases h : j < n <;> simp [h]

theorem pm_pt : ∀ (z : List Bool) (n a : Nat), z.length = n → a < n → pm (pt n a) z = z.getD a false
  | [], n, a, hz, ha => by simp at hz; omega
  | b :: z, n, a, hz, ha => by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp at hz; omega⟩
    have hz' : z.length = m := by simpa using hz
    have hsplit : pt (m + 1) a = decide (0 = a) :: (List.range m).map (fun i => decide (i + 1 = a)) := by
      simp [pt, List.range_succ_eq_map, List.map_map, Function.comp_def]
    rw [hsplit]
    cases a with
    | zero =>
      simp only [pm, decide_true, Bool.true_and, List.getD_cons_zero]
      rw [pm_of_false _ _ (fun s hs => by simp only [List.mem_map] at hs; obtain ⟨i, _, rfl⟩ := hs; simp)]
      simp
    | succ a =>
      have e : (List.range m).map (fun i => decide (i + 1 = a + 1)) = pt m a := by
        simp [pt]
      simp only [pm, show decide (0 = a + 1) = false by simp, Bool.false_and, Bool.false_xor, e,
        List.getD_cons_succ]
      exact pm_pt z m a hz' (by omega)

/-- Two-point mask. -/
def twoMask (n a b : Nat) : List Bool := List.zipWith xor (pt n a) (pt n b)

theorem twoMask_mem (n a b : Nat) : twoMask n a b ∈ bitvecs n := mem_bitvecs_of_length (by simp [twoMask, pt])

theorem pm_twoMask {z : List Bool} {n a b : Nat} (hz : z.length = n) (ha : a < n) (hb : b < n) :
    pm (twoMask n a b) z = xor (z.getD a false) (z.getD b false) := by
  unfold twoMask
  rw [Misc.pm_zipWith _ _ z (by simp [pt]), pm_pt z n a hz ha, pm_pt z n b hz hb]

theorem twoMask_eq_map (n a b : Nat) :
    twoMask n a b = (List.range n).map (fun i => xor (decide (i = a)) (decide (i = b))) := by
  apply List.ext_getElem (by simp [twoMask, pt])
  intro i h1 h2
  simp [twoMask, pt, List.getElem_zipWith]

theorem ones_map_range (n : Nat) (p : Nat → Bool) : ones ((List.range n).map p) = ((List.range n).filter p).length := by
  unfold ones
  rw [List.filter_map, List.length_map]
  rfl

theorem ite_lt_succ (a n : Nat) :
    (if a < n + 1 then 1 else 0) = (if a < n then 1 else 0) + (if n = a then 1 else 0) := by
  by_cases h1 : a < n
  · have : ¬ n = a := by omega
    simp [h1, this, show a < n + 1 by omega]
  · by_cases h2 : n = a
    · subst h2; simp
    · simp [h1, h2, show ¬ a < n + 1 by omega]

theorem count_two {a b : Nat} (hab : a ≠ b) : ∀ n : Nat,
    ((List.range n).filter (fun i => xor (decide (i = a)) (decide (i = b)))).length =
      (if a < n then 1 else 0) + (if b < n then 1 else 0)
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.filter_append, List.length_append, count_two hab n, ite_lt_succ a n, ite_lt_succ b n]
    have e : ([n].filter (fun i => xor (decide (i = a)) (decide (i = b)))).length =
        (if n = a then 1 else 0) + (if n = b then 1 else 0) := by
      by_cases h1 : n = a
      · subst h1; simp [hab]
      · by_cases h2 : n = b
        · subst h2; simp [h1, Ne.symm h1]
        · simp [h1, h2]
    rw [e]; omega

theorem ones_twoMask {n a b : Nat} (hab : a ≠ b) (ha : a < n) (hb : b < n) : ones (twoMask n a b) = 2 := by
  rw [twoMask_eq_map, ones_map_range, count_two hab, if_pos ha, if_pos hb]

theorem twoMask_getD (n a b j : Nat) :
    (twoMask n a b).getD j false = xor (decide (j = a) && decide (j < n)) (decide (j = b) && decide (j < n)) := by
  rw [twoMask_eq_map]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range]
  by_cases h : j < n <;> simp [h]

/-- The sign encoding of the total single-change delta circuit, on the full cube. -/
def dSign (B N q : Nat) (z : List Bool) : R := sg (eval (vfun z) (LocalRestore.dC B N q))

theorem eval_yC (B N i p : Nat) (z : Nat → Bool) :
    eval z (LocalRestore.yC B N i p) = xor (z (B * i + p)) (z (B * N + (B * i + p))) := by
  simp only [LocalRestore.yC, CorrBridge.eval_xor2, eval_input]

/-- THE PER-HEAP XOR IS A TWO-COORDINATE CHARACTER on the full 2BN-bit cube. -/
theorem yC_chi {B N i p : Nat} (hi : i < N) (hp : p < B) {z : List Bool} (hz : z ∈ bitvecs (2 * (B * N))) :
    (sg (eval (vfun z) (LocalRestore.yC B N i p)) : R) =
      chi (twoMask (2 * (B * N)) (B * i + p) (B * N + (B * i + p))) z := by
  have hl := mem_bitvecs_length hz
  have h1 : B * i + p < B * N := SelectCircuit.heap_lt hi hp
  rw [eval_yC]; unfold chi
  rw [pm_twoMask hl (by omega) (by omega)]; rfl

theorem eval_dC_any {B N q p : Nat} (hq : q < B) (hp : p = B - 1 - q) (z : Nat → Bool) :
    eval z (LocalRestore.dC B N q) =
      (List.range N).any (fun i => xor (z (B * i + p)) (z (B * N + (B * i + p)))) := by
  subst hp
  simp only [LocalRestore.dC, hq, if_true, eval_or, List.any_map]
  congr 1; funext i; simp only [Function.comp_apply, eval_yC]

theorem getD_replicate_false (n j : Nat) : (List.replicate n false).getD j false = false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_replicate]; split <;> rfl

theorem dSign_true {B N q p : Nat} (hq : q < B) (hp : p = B - 1 - q) {z : List Bool} {i : Nat} (hi : i < N)
    (h : xor (z.getD (B * i + p) false) (z.getD (B * N + (B * i + p)) false) = true) : (dSign B N q z : R) = -1 := by
  unfold dSign
  rw [eval_dC_any hq hp]
  have : (List.range N).any (fun i => xor (vfun z (B * i + p)) (vfun z (B * N + (B * i + p)))) = true :=
    List.any_eq_true.2 ⟨i, List.mem_range.2 hi, h⟩
  rw [this]; rfl

/-- B3 (MAIN): for N ≥ 2 and q < B the sign encoding of dC B N q on the FULL 2BN-bit cube is
    not ±χ_S for ANY mask S (of any degree). -/
theorem dC_not_character {B N q : Nat} (hN : 2 ≤ N) (hq : q < B) :
    ¬ ∃ (S : List Bool) (c : R), c * c = 1 ∧ ∀ z ∈ bitvecs (2 * (B * N)), dSign B N q z = c * chi S z := by
  rintro ⟨S, c, hc, hf⟩
  obtain ⟨p, hp⟩ : ∃ p, p = B - 1 - q := ⟨_, rfl⟩
  have hBN : 2 * B ≤ B * N := by
    have := Nat.mul_le_mul_left B hN; rw [Nat.mul_comm B 2] at this; exact this
  have hB : 1 ≤ B := by omega
  have hpB : p < B := by omega
  have ha : p < 2 * (B * N) := by omega
  have hb : B + p < 2 * (B * N) := by omega
  have m0 : List.replicate (2 * (B * N)) false ∈ bitvecs (2 * (B * N)) := mem_bitvecs_of_length (by simp)
  have m1 := pt_mem (2 * (B * N)) p
  have m2 := pt_mem (2 * (B * N)) (B + p)
  have m12 := twoMask_mem (2 * (B * N)) p (B + p)
  -- values of dSign at the four points
  have v0 : (dSign B N q (List.replicate (2 * (B * N)) false) : R) = 1 := by
    unfold dSign
    rw [eval_dC_any hq hp]
    have : (List.range N).any (fun i => xor (vfun (List.replicate (2 * (B * N)) false) (B * i + p))
        (vfun (List.replicate (2 * (B * N)) false) (B * N + (B * i + p)))) = false := by
      simp only [vfun, getD_replicate_false, Bool.xor_false, List.any_eq_false]; simp
    rw [this]; rfl
  have v1 : (dSign B N q (pt (2 * (B * N)) p) : R) = -1 := by
    apply dSign_true hq hp (i := 0) (by omega)
    rw [pt_getD, pt_getD]
    have e1 : decide (B * 0 + p = p) = true := by simp
    have e2 : decide (B * 0 + p < 2 * (B * N)) = true := by simp; omega
    have e3 : decide (B * N + (B * 0 + p) = p) = false := by simp; omega
    rw [e1, e2, e3]; rfl
  have v2 : (dSign B N q (pt (2 * (B * N)) (B + p)) : R) = -1 := by
    apply dSign_true hq hp (i := 1) (by omega)
    rw [pt_getD, pt_getD]
    have e1 : decide (B * 1 + p = B + p) = true := by simp
    have e2 : decide (B * 1 + p < 2 * (B * N)) = true := by simp; omega
    have e3 : decide (B * N + (B * 1 + p) = B + p) = false := by simp; omega
    rw [e1, e2, e3]; rfl
  have v12 : (dSign B N q (twoMask (2 * (B * N)) p (B + p)) : R) = -1 := by
    apply dSign_true hq hp (i := 0) (by omega)
    rw [twoMask_getD, twoMask_getD]
    have e1 : decide (B * 0 + p = p) = true := by simp
    have e2 : decide (B * 0 + p < 2 * (B * N)) = true := by simp; omega
    have e3 : decide (B * 0 + p = B + p) = false := by simp; omega
    have e4 : decide (B * N + (B * 0 + p) = p) = false := by simp; omega
    have e5 : decide (B * N + (B * 0 + p) = B + p) = false := by simp; omega
    rw [e1, e2, e3, e4, e5]; rfl
  have c0 := hf _ m0
  have c1 := hf _ m1
  have c2 := hf _ m2
  have c12 := hf _ m12
  have hmul : (chi S (twoMask (2 * (B * N)) p (B + p)) : R) = chi S (pt (2 * (B * N)) p) * chi S (pt (2 * (B * N)) (B + p)) :=
    (chi_mul_right S (by simp [pt])).symm
  rw [chi_zeros, v0] at c0
  rw [v1] at c1; rw [v2] at c2; rw [v12, hmul] at c12
  -- 1 = c, −1 = c χ₁, −1 = c χ₂, −1 = c χ₁ χ₂  ⇒  −1 = 1
  have hc1 : c = 1 := by grind
  subst hc1
  have : (-1 : R) = 1 := by grind
  exact one_ne_neg_one this.symm

/-- … hence its Fourier expansion has at least two nonzero coefficients. -/
theorem dC_two_coefs {B N q : Nat} (hN : 2 ≤ N) (hq : q < B) :
    ∃ S ∈ bitvecs (2 * (B * N)), ∃ T ∈ bitvecs (2 * (B * N)), S ≠ T ∧
      coef (2 * (B * N)) (dSign (R := R) B N q) S ≠ 0 ∧ coef (2 * (B * N)) (dSign (R := R) B N q) T ≠ 0 := by
  let n := 2 * (B * N)
  let f := dSign (R := R) B N q
  have hsq : ∀ z ∈ bitvecs n, f z * f z = 1 := fun z _ => sg_mul_self _
  apply Classical.byContradiction; intro hno
  -- some coefficient is nonzero
  have hex : ∃ S ∈ bitvecs n, coef n f S ≠ 0 := by
    apply Classical.byContradiction; intro hall
    have h0 : gs (bitvecs n) (fun S => coef n f S ^ 2) = 0 := by
      rw [gs_congr (fun S hS => by
        show coef n f S ^ 2 = (fun _ => (0 : R)) S
        have : coef n f S = 0 := Classical.byContradiction (fun h => hall ⟨S, hS, h⟩)
        rw [this]; grind), gs_zero]
    rw [sign_mass n f hsq] at h0
    have := OrderedRing.zero_lt_one (R := R); rw [h0] at this; exact Preorder.lt_irrefl _ this
  obtain ⟨S, hS, hSne⟩ := hex
  have honly : ∀ T ∈ bitvecs n, T ≠ S → coef n f T = 0 := by
    intro T hT hTS
    apply Classical.byContradiction; intro h
    exact hno ⟨S, hS, T, hT, fun e => hTS e.symm, hSne, h⟩
  -- then f = coef(S) χ_S on the cube, with coef(S)² = 1
  have hrep : ∀ z ∈ bitvecs n, f z = coef n f S * chi S z := by
    intro z hz
    rw [← inversion n f hz]
    have hl := mem_bitvecs_length hS
    rw [gs_congr (fun T hT => by
      show coef n f T * chi T z = Noise.ind (decide (S = T)) * (coef n f T * chi T z)
      by_cases hTS : T = S
      · subst hTS; simp only [decide_true, Noise.ind, if_true]; grind
      · rw [honly T hT hTS]; grind), gs_point n S hl (fun T => coef n f T * chi T z)]
  have hmass := sign_mass n f hsq
  rw [gs_congr (fun T hT => by
    show coef n f T ^ 2 = Noise.ind (decide (S = T)) * coef n f T ^ 2
    by_cases hTS : T = S
    · subst hTS; simp only [decide_true, Noise.ind, if_true]; grind
    · rw [honly T hT hTS]; grind), gs_point n S (mem_bitvecs_length hS) (fun T => coef n f T ^ 2)] at hmass
  exact dC_not_character hN hq ⟨S, coef n f S, by grind, hrep⟩

/-- N = 1: dC IS the two-coordinate character (old and new value of the only heap). -/
theorem dC_one {B q : Nat} (hq : q < B) {z : List Bool} (hz : z ∈ bitvecs (2 * (B * 1))) :
    (dSign B 1 q z : R) = chi (twoMask (2 * (B * 1)) (B * 0 + (B - 1 - q)) (B * 1 + (B * 0 + (B - 1 - q)))) z := by
  unfold dSign
  rw [← yC_chi (by omega) (by omega) hz]
  have : eval (vfun z) (LocalRestore.dC B 1 q) = eval (vfun z) (LocalRestore.yC B 1 0 (B - 1 - q)) := by
    simp [LocalRestore.dC, hq]
  rw [this]

theorem dC_one_exactDeg {B q : Nat} (hq : q < B) : ExactDeg (2 * (B * 1)) (dSign (R := R) B 1 q) 2 := by
  have hc : ∀ z ∈ bitvecs (2 * (B * 1)), (dSign B 1 q z : R) =
      chi (twoMask (2 * (B * 1)) (B * 0 + (B - 1 - q)) (B * 1 + (B * 0 + (B - 1 - q)))) z := fun z hz => dC_one hq hz
  have hm := twoMask_mem (2 * (B * 1)) (B * 0 + (B - 1 - q)) (B * 1 + (B * 0 + (B - 1 - q)))
  have hones : ones (twoMask (2 * (B * 1)) (B * 0 + (B - 1 - q)) (B * 1 + (B * 0 + (B - 1 - q)))) = 2 :=
    ones_twoMask (by omega) (by omega) (by omega)
  have h := chi_exactDeg (R := R) hm
  rw [hones] at h
  exact ⟨fun T hT hk => by rw [coef_congr hc]; exact h.1 T hT hk,
    let ⟨T, hT, h1, h2⟩ := h.2; ⟨T, hT, h1, by rw [coef_congr hc]; exact h2⟩⟩

/-- N = 0 or q ≥ B: dC is constant false, i.e. the constant character χ_0. -/
theorem dC_trivial {B N q : Nat} (h : N = 0 ∨ B ≤ q) (z : List Bool) :
    (dSign B N q z : R) = chi (List.replicate (2 * (B * N)) false) z := by
  have hz : (chi (List.replicate (2 * (B * N)) false) z : R) = 1 := by
    unfold chi; rw [pm_of_false _ _ (fun s hs => (List.eq_of_mem_replicate hs))]; rfl
  rw [hz]; unfold dSign
  rcases h with rfl | hq
  · by_cases hq : q < B
    · simp [LocalRestore.dC, hq, sg]
    · simp [LocalRestore.dC, hq, sg]
  · simp [LocalRestore.dC, show ¬ q < B by omega, sg]

/-! ### Agreement on the promised domain -/

/-- The two frames as a point of the full cube. -/
def enc (B N : Nat) (Q Q' : List Nat) : List Bool := (List.range (2 * (B * N))).map (LocalRestore.tf B N Q Q')

theorem enc_mem (B N : Nat) (Q Q' : List Nat) : enc B N Q Q' ∈ bitvecs (2 * (B * N)) :=
  mem_bitvecs_of_length (by simp [enc])

theorem vfun_enc {B N : Nat} {Q Q' : List Nat} {j : Nat} (hj : j < 2 * (B * N)) :
    vfun (enc B N Q Q') j = LocalRestore.tf B N Q Q' j := by
  simp [vfun, enc, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range, hj]

theorem eval_enc {B N : Nat} {Q Q' : List Nat} (C : Circ) (hC : maxInput C ≤ 2 * (B * N)) :
    eval (vfun (enc B N Q Q')) C = eval (LocalRestore.tf B N Q Q') C :=
  eval_congr_below _ _ C (fun i hi => vfun_enc (by omega))

/-- AGREEMENT WITH THE DELTA on every single-change transition (in particular on every legal
    move): the sign of dC at the encoded pair is the sign of delta bit q. -/
theorem dSign_enc {B N q : Nat} {Q Q' : List Nat} (hQ : Q.length = N) (hQ' : Q'.length = N)
    (hw : Game.Width B Q) (hw' : Game.Width B Q') (h1 : LocalRestore.OneChange Q Q') :
    (dSign B N q (enc B N Q Q') : R) = sg ((nimSum Q ^^^ nimSum Q').testBit q) := by
  unfold dSign
  rw [eval_enc _ (LocalRestore.dC_res (B := B) (N := N) q).2.2, LocalRestore.dC_eval hQ hQ',
    LocalRestore.localDelta_eq hQ hQ' hw hw' h1]

theorem set_split (Q : List Nat) {i : Nat} (hi : i < Q.length) (y : Nat) :
    Q = Q.take i ++ Q[i] :: Q.drop (i + 1) ∧ Q.set i y = Q.take i ++ y :: Q.drop (i + 1) := by
  constructor
  · simp
  · rw [List.set_eq_take_append_cons_drop]; simp [hi]

/-- KNOWN CHANGED HEAP: on transitions that change only heap i (Q' = Q.set i y), the sign of
    dC equals the two-coordinate character of heap i (old and new bit q).  So, conditional on
    the changed index, the delta bit is a degree-two character, as the paper states. -/
theorem dSign_known_heap {B N q i : Nat} (hq : q < B) (hi : i < N) {Q : List Nat} (hQ : Q.length = N)
    (y : Nat) :
    (dSign B N q (enc B N Q (Q.set i y)) : R) =
      chi (twoMask (2 * (B * N)) (B * i + (B - 1 - q)) (B * N + (B * i + (B - 1 - q)))) (enc B N Q (Q.set i y)) := by
  have hQ' : (Q.set i y).length = N := by simp [hQ]
  rw [← yC_chi hi (by omega) (enc_mem B N Q (Q.set i y))]
  unfold dSign
  rw [eval_enc _ (LocalRestore.dC_res (B := B) (N := N) q).2.2,
    eval_enc _ (LocalRestore.yC_max (B := B) (N := N) hi (by omega))]
  congr 1
  rw [LocalRestore.dC_eval hQ hQ', LocalRestore.yC_eval hQ hQ' hi (by omega),
    show B - 1 - (B - 1 - q) = q by omega]
  unfold LocalRestore.localDelta
  rw [Game.testBit_ofBits]
  simp only [hq, decide_true, Bool.true_and]
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true, List.mem_range]
  constructor
  · rintro ⟨k, hk, h⟩
    by_cases hki : k = i
    · subst hki; exact h
    · rw [Misc.getD_set_ne' Q y hki] at h; simp at h
  · intro h; exact ⟨i, hi, h⟩

/-! ### The characters that agree with the delta bit on the single-change domain -/

/-- The bit list of one frame. -/
def frame (B N : Nat) (Q : List Nat) : List Bool := (List.range (B * N)).map (CorrBridge.boardBits B Q)

theorem frame_length (B N : Nat) (Q : List Nat) : (frame B N Q).length = B * N := by simp [frame]

theorem frame_mem (B N : Nat) (Q : List Nat) : frame B N Q ∈ bitvecs (B * N) :=
  mem_bitvecs_of_length (frame_length B N Q)

theorem frame_getD {B N : Nat} {Q : List Nat} {j : Nat} (hj : j < B * N) :
    (frame B N Q).getD j false = CorrBridge.boardBits B Q j := by
  simp [frame, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range, hj]

theorem enc_split (B N : Nat) (Q Q' : List Nat) : enc B N Q Q' = frame B N Q ++ frame B N Q' := by
  unfold enc frame
  rw [show 2 * (B * N) = B * N + B * N by omega, List.range_add, List.map_append, List.map_map]
  congr 1
  · apply List.map_congr_left; intro j hj; exact LocalRestore.tf_left (List.mem_range.1 hj)
  · apply List.map_congr_left; intro j _; simp only [Function.comp_apply]; exact LocalRestore.tf_right j

/-- Decoding a board's frame returns the board. -/
theorem decode_frame {B N : Nat} {Q : List Nat} (hQ : Q.length = N) (hw : Game.Width B Q) :
    decodeBoard B N (frame B N Q) = Q := by
  have key : ∀ i, i < N → (decodeBoard B N (frame B N Q)).getD i 0 = Q.getD i 0 := by
    intro i hi
    rw [CorrBridge.decodeBoard_getD B N _ i hi]
    have hlen : ((frame B N Q).drop (B * i)).take B = ((frame B N Q).drop (B * i)).take B := rfl
    have hl : (((frame B N Q).drop (B * i)).take B).length = B := by
      simp only [List.length_take, List.length_drop, frame_length]
      have := Nat.mul_le_mul_left B (show i + 1 ≤ N by omega)
      rw [Nat.mul_succ] at this; omega
    apply Nat.eq_of_testBit_eq; intro k
    by_cases hk : k < B
    · have := testBit_toNatBE (((frame B N Q).drop (B * i)).take B) (B - 1 - k) (by omega)
      rw [hl, show B - 1 - (B - 1 - k) = k by omega] at this
      rw [this, CorrBridge.getD_take_drop _ _ _ _ (by omega), frame_getD (SelectCircuit.heap_lt hi (by omega)),
        CorrBridge.boardBits_heap hQ hi (by omega), show B - 1 - (B - 1 - k) = k by omega]
    · have h1 := toNatBE_lt (((frame B N Q).drop (B * i)).take B)
      rw [hl] at h1
      have h2 := SelectCircuit.getD_lt_of_width hQ hw hi
      rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by decide) (by omega))),
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le h2 (Nat.pow_le_pow_right (by decide) (by omega)))]
  apply List.ext_getElem (by rw [length_decodeBoard, hQ])
  intro i h1 h2
  have h1' := h1
  rw [length_decodeBoard] at h1'
  have := key i h1'
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1, List.getElem?_eq_getElem h2,
    Option.getD_some] at this
  exact this

/-- The global mask: bit q of every heap, in both frames (2N coordinates). -/
def gMask (B N q : Nat) : List Bool := maskU B N (2 ^ q) ++ maskU B N (2 ^ q)

theorem gMask_mem (B N q : Nat) : gMask B N q ∈ bitvecs (2 * (B * N)) :=
  mem_bitvecs_of_length (by simp [gMask, length_maskU]; omega)

theorem ones_gMask {B N q : Nat} (hq : q < B) : ones (gMask B N q) = 2 * N := by
  have h := (Misc.nimsum_bit_character hq (x := maskU B N (2 ^ q)) (maskU_mem B N _)).2
  unfold gMask; rw [ones_append, h]; omega

/-- EXISTENCE: the global parity character (degree 2N) agrees with the delta bit on EVERY
    encoded pair of B-bit boards (no promise needed). -/
theorem gMask_delta {B N q : Nat} (hq : q < B) {Q Q' : List Nat} (hQ : Q.length = N) (hQ' : Q'.length = N)
    (hw : Game.Width B Q) (hw' : Game.Width B Q') :
    (chi (gMask B N q) (enc B N Q Q') : R) = sg ((nimSum Q ^^^ nimSum Q').testBit q) := by
  unfold chi gMask
  rw [enc_split, pm_append (by rw [length_maskU, frame_length]),
    ← (Misc.nimsum_bit_character hq (frame_mem B N Q)).1, ← (Misc.nimsum_bit_character hq (frame_mem B N Q')).1,
    decode_frame hQ hw, decode_frame hQ' hw', Nat.testBit_xor]

theorem toBitsBE_getD : ∀ (B : Nat) (u p : Nat), p < B → (toBitsBE B u).getD p false = u.testBit (B - 1 - p)
  | 0, _, _, hp => by omega
  | B + 1, u, 0, _ => by simp [toBitsBE]
  | B + 1, u, p + 1, hp => by
    simp only [toBitsBE, List.getD_cons_succ]
    rw [toBitsBE_getD B u p (by omega)]; congr 1; omega

theorem maskU_getD {B : Nat} (u : Nat) {p : Nat} (hp : p < B) : ∀ (N i : Nat), i < N →
    (maskU B N u).getD (B * i + p) false = u.testBit (B - 1 - p)
  | 0, _, hi => by omega
  | N + 1, 0, _ => by
    simp only [maskU, Nat.mul_zero, Nat.zero_add, List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_left (by rw [length_toBitsBE]; exact hp)]
    have := toBitsBE_getD B u p hp
    rwa [List.getD_eq_getElem?_getD] at this
  | N + 1, i + 1, hi => by
    simp only [maskU, List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (by rw [length_toBitsBE]; rw [Nat.mul_succ]; omega), length_toBitsBE,
      show B * (i + 1) + p - B = B * i + p by rw [Nat.mul_succ]; omega]
    have := maskU_getD u hp N i (by omega)
    rwa [List.getD_eq_getElem?_getD] at this

/-- The board with heap i equal to 2^r and all other heaps empty. -/
def unitBoard (N i r : Nat) : List Nat := (List.replicate N 0).set i (2 ^ r)

theorem unitBoard_length (N i r : Nat) : (unitBoard N i r).length = N := by simp [unitBoard]

theorem zero_width (B N : Nat) : Game.Width B (List.replicate N 0) := by
  intro x hx; rw [List.eq_of_mem_replicate hx]; exact Nat.two_pow_pos B

theorem unitBoard_width {B N i r : Nat} (hr : r < B) : Game.Width B (unitBoard N i r) := by
  intro x hx
  unfold unitBoard at hx
  rcases List.mem_or_eq_of_mem_set hx with h | h
  · rw [List.eq_of_mem_replicate h]; exact Nat.two_pow_pos B
  · rw [h]; exact Nat.pow_lt_pow_right (by decide) hr

theorem unitBoard_split {N i : Nat} (hi : i < N) (r : Nat) :
    ∃ pre post, List.replicate N 0 = pre ++ 0 :: post ∧ unitBoard N i r = pre ++ 2 ^ r :: post := by
  have h := set_split (List.replicate N 0) (i := i) (by simp; exact hi) (2 ^ r)
  refine ⟨(List.replicate N 0).take i, (List.replicate N 0).drop (i + 1), ?_, h.2⟩
  have e : (List.replicate N 0)[i]'(by simp; exact hi) = 0 := by simp
  have h1 := h.1
  rw [e] at h1; exact h1

theorem boardBits_zero (B N j : Nat) : CorrBridge.boardBits B (List.replicate N 0) j = false := by
  unfold CorrBridge.boardBits
  split
  · simp [List.getD_eq_getElem?_getD, List.getElem?_replicate]; split <;> simp
  · rfl

theorem boardBits_unit {B N i r : Nat} (hi : i < N) (hr : r < B) {j : Nat} (hj : j < B * N) :
    CorrBridge.boardBits B (unitBoard N i r) j = decide (j = B * i + (B - 1 - r)) := by
  have hB : 0 < B := by omega
  have hjB : j / B < N := by rw [Nat.div_lt_iff_lt_mul hB, Nat.mul_comm]; exact hj
  have hm : j % B < B := Nat.mod_lt _ hB
  have e := CorrBridge.boardBits_heap (B := B) (unitBoard_length N i r) hjB hm
  rw [show B * (j / B) + j % B = j from Nat.div_add_mod j B] at e
  rw [e]
  have hget : (unitBoard N i r).getD (j / B) 0 = if j / B = i then 2 ^ r else 0 := by
    unfold unitBoard
    by_cases h : j / B = i
    · subst h; rw [if_pos rfl, Misc.getD_set_eq' _ _ (by simp; exact hi)]
    · rw [if_neg h, Misc.getD_set_ne' _ _ h]
      simp only [List.getD_eq_getElem?_getD, List.getElem?_replicate]; split <;> rfl
  rw [hget]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  constructor
  · intro h
    by_cases h1 : j / B = i
    · rw [if_pos h1, Nat.testBit_two_pow] at h
      simp only [decide_eq_true_eq] at h
      have := Nat.div_add_mod j B
      rw [h1] at this; omega
    · rw [if_neg h1] at h; simp at h
  · intro h
    have h1 : j / B = i := by
      rw [h, Nat.mul_comm, Nat.add_comm, Nat.add_mul_div_right _ _ hB, Nat.div_eq_of_lt (by omega)]; omega
    have h2 : j % B = B - 1 - r := by
      rw [h, Nat.mul_comm, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
    rw [if_pos h1, Nat.testBit_two_pow]; simp only [decide_eq_true_eq]; omega

theorem enc_unit_left {B N i r : Nat} (hi : i < N) (hr : r < B) :
    enc B N (unitBoard N i r) (List.replicate N 0) = pt (2 * (B * N)) (B * i + (B - 1 - r)) := by
  have ha : B * i + (B - 1 - r) < B * N := SelectCircuit.heap_lt hi (by omega)
  apply mask_ext (enc_mem _ _ _ _) (pt_mem _ _)
  intro j hj
  have e := vfun_enc (B := B) (N := N) (Q := unitBoard N i r) (Q' := List.replicate N 0) hj
  unfold vfun at e
  rw [e, pt_getD]
  by_cases hj1 : j < B * N
  · rw [LocalRestore.tf_left hj1, boardBits_unit hi hr hj1]; simp [hj]
  · have e2 : LocalRestore.tf B N (unitBoard N i r) (List.replicate N 0) j =
        CorrBridge.boardBits B (List.replicate N 0) (j - B * N) := by
      have := LocalRestore.tf_right (B := B) (N := N) (Q := unitBoard N i r) (Q' := List.replicate N 0) (j - B * N)
      rwa [show B * N + (j - B * N) = j by omega] at this
    rw [e2, boardBits_zero]
    have : ¬ j = B * i + (B - 1 - r) := by omega
    simp [this]

theorem enc_unit_right {B N i r : Nat} (hi : i < N) (hr : r < B) :
    enc B N (List.replicate N 0) (unitBoard N i r) = pt (2 * (B * N)) (B * N + (B * i + (B - 1 - r))) := by
  have ha : B * i + (B - 1 - r) < B * N := SelectCircuit.heap_lt hi (by omega)
  apply mask_ext (enc_mem _ _ _ _) (pt_mem _ _)
  intro j hj
  have e := vfun_enc (B := B) (N := N) (Q := List.replicate N 0) (Q' := unitBoard N i r) hj
  unfold vfun at e
  rw [e, pt_getD]
  by_cases hj1 : j < B * N
  · rw [LocalRestore.tf_left hj1, boardBits_zero]
    have : ¬ j = B * N + (B * i + (B - 1 - r)) := by omega
    simp [this]
  · have e2 : LocalRestore.tf B N (List.replicate N 0) (unitBoard N i r) j =
        CorrBridge.boardBits B (unitBoard N i r) (j - B * N) := by
      have := LocalRestore.tf_right (B := B) (N := N) (Q := List.replicate N 0) (Q' := unitBoard N i r) (j - B * N)
      rwa [show B * N + (j - B * N) = j by omega] at this
    rw [e2, boardBits_unit hi hr (by omega)]
    by_cases hja : j = B * N + (B * i + (B - 1 - r))
    · have : j - B * N = B * i + (B - 1 - r) := by omega
      simp [this, hja]; omega
    · have : ¬ (j - B * N = B * i + (B - 1 - r)) := by omega
      simp [this, hja]

theorem pm_pt_left {S : List Bool} {n a : Nat} (hS : S.length = n) (ha : a < n) : pm S (pt n a) = S.getD a false := by
  rw [pm_comm S (pt n a) (by simp [pt, hS]), pm_pt S n a hS ha]

theorem sg_inj {b c : Bool} (h : (sg b : R) = sg c) : b = c := by
  cases b <;> cases c <;> simp only [sg, Bool.false_eq_true, if_true, if_false] at h
  · rfl
  · exact absurd h one_ne_neg_one
  · exact absurd h.symm one_ne_neg_one
  · rfl

/-- UNIQUENESS: a character that agrees with the delta bit q on every single-change pair of
    B-bit boards is the global parity character.  So, for N ≥ 2, no character of degree
    less than 2N (in particular no degree-two character) agrees with the delta map on the
    promised single-change domain; the local circuit dC is a different total extension,
    and is not a character at all (dC_not_character). -/
theorem char_unique {B N q : Nat} (hq : q < B) {S : List Bool} (hS : S ∈ bitvecs (2 * (B * N)))
    (h : ∀ Q Q', Q.length = N → Q'.length = N → Game.Width B Q → Game.Width B Q' → LocalRestore.OneChange Q Q' →
      (chi S (enc B N Q Q') : R) = sg ((nimSum Q ^^^ nimSum Q').testBit q)) :
    S = gMask B N q := by
  have hSl := mem_bitvecs_length hS
  have hB : 0 < B := by omega
  apply mask_ext hS (gMask_mem B N q)
  intro a ha
  by_cases ha1 : a < B * N
  · -- first frame: the pair (unit board, empty board)
    have hi : a / B < N := by rw [Nat.div_lt_iff_lt_mul hB, Nat.mul_comm]; exact ha1
    have hm : a % B < B := Nat.mod_lt _ hB
    have hr : B - 1 - a % B < B := by omega
    have hpos : a = B * (a / B) + (B - 1 - (B - 1 - a % B)) := by
      have := Nat.div_add_mod a B; omega
    obtain ⟨pre, post, h0, h1⟩ := unitBoard_split hi (B - 1 - a % B)
    have hc := h (unitBoard N (a / B) (B - 1 - a % B)) (List.replicate N 0) (unitBoard_length _ _ _) (by simp)
      (unitBoard_width hr) (zero_width B N) (Or.inr ⟨pre, 2 ^ (B - 1 - a % B), post, 0, h1, h0⟩)
    rw [enc_unit_left hi hr, h1, h0, LocalRestore.delta_oneChange, ← hpos] at hc
    unfold chi at hc
    rw [pm_pt_left hSl ha] at hc
    have e1 := sg_inj hc
    rw [e1, Nat.xor_zero, Nat.testBit_two_pow]
    unfold gMask
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by rw [length_maskU]; exact ha1),
      ← List.getD_eq_getElem?_getD]
    conv => rhs; rw [show a = B * (a / B) + a % B from (Nat.div_add_mod a B).symm]
    rw [maskU_getD (2 ^ q) hm N (a / B) hi, Nat.testBit_two_pow]
    simp only [decide_eq_decide]; omega
  · -- second frame: the pair (empty board, unit board)
    have hb : a - B * N < B * N := by omega
    have hi : (a - B * N) / B < N := by rw [Nat.div_lt_iff_lt_mul hB, Nat.mul_comm N B]; exact hb
    have hm : (a - B * N) % B < B := Nat.mod_lt _ hB
    have hr : B - 1 - (a - B * N) % B < B := by omega
    have hpos : a = B * N + (B * ((a - B * N) / B) + (B - 1 - (B - 1 - (a - B * N) % B))) := by
      have := Nat.div_add_mod (a - B * N) B; omega
    obtain ⟨pre, post, h0, h1⟩ := unitBoard_split hi (B - 1 - (a - B * N) % B)
    have hc := h (List.replicate N 0) (unitBoard N ((a - B * N) / B) (B - 1 - (a - B * N) % B)) (by simp)
      (unitBoard_length _ _ _) (zero_width B N) (unitBoard_width hr) (Or.inr ⟨pre, 0, post, _, h0, h1⟩)
    rw [enc_unit_right hi hr, h1, h0, LocalRestore.delta_oneChange, ← hpos] at hc
    unfold chi at hc
    rw [pm_pt_left hSl ha] at hc
    have e1 := sg_inj hc
    rw [e1, Nat.zero_xor, Nat.testBit_two_pow]
    unfold gMask
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [length_maskU]; omega), length_maskU,
      ← List.getD_eq_getElem?_getD]
    conv => rhs; rw [show a - B * N = B * ((a - B * N) / B) + (a - B * N) % B from (Nat.div_add_mod _ B).symm]
    rw [maskU_getD (2 ^ q) hm N _ hi, Nat.testBit_two_pow]
    simp only [decide_eq_decide]; omega

theorem nimSum_zeros : ∀ N : Nat, nimSum (List.replicate N 0) = 0
  | 0 => rfl
  | N + 1 => by simp only [List.replicate_succ, nimSum, nimSum_zeros N, Nat.zero_xor]

theorem enc_zeros (B N : Nat) :
    enc B N (List.replicate N 0) (List.replicate N 0) = List.replicate (2 * (B * N)) false := by
  apply mask_ext (enc_mem _ _ _ _) (mem_bitvecs_of_length (by simp))
  intro j hj
  have e := vfun_enc (B := B) (N := N) (Q := List.replicate N 0) (Q' := List.replicate N 0) hj
  unfold vfun at e
  rw [e, getD_replicate_false]
  by_cases hj1 : j < B * N
  · rw [LocalRestore.tf_left hj1, boardBits_zero]
  · have := LocalRestore.tf_right (B := B) (N := N) (Q := List.replicate N 0) (Q' := List.replicate N 0) (j - B * N)
    rw [show B * N + (j - B * N) = j by omega, boardBits_zero] at this
    exact this

/-- SIGNED VERSION: if c·χ_S (c = ±1) agrees with the sign of the delta bit on the
    single-change domain, then c = 1 (test pair Q = Q′ = 0) and S is the global mask. -/
theorem char_unique_signed {B N q : Nat} (hq : q < B) {S : List Bool} (hS : S ∈ bitvecs (2 * (B * N)))
    {c : R} (h : ∀ Q Q', Q.length = N → Q'.length = N → Game.Width B Q → Game.Width B Q' → LocalRestore.OneChange Q Q' →
      c * chi S (enc B N Q Q') = sg ((nimSum Q ^^^ nimSum Q').testBit q)) :
    c = 1 ∧ S = gMask B N q := by
  have h0 := h (List.replicate N 0) (List.replicate N 0) (by simp) (by simp) (zero_width B N) (zero_width B N) (Or.inl rfl)
  rw [enc_zeros, chi_zeros, nimSum_zeros, Nat.xor_zero, Nat.zero_testBit] at h0
  have hc : c = 1 := by simp only [sg, Bool.false_eq_true, if_false] at h0; grind
  subst hc
  refine ⟨rfl, char_unique (R := R) hq hS (fun Q Q' a b c' d e => ?_)⟩
  have := h Q Q' a b c' d e
  clear h h0
  have e1 : (1 : R) * chi S (enc B N Q Q') = chi S (enc B N Q Q') := by grind
  rw [e1] at this; exact this

/-- COROLLARY: for N ≥ 2 no character of degree two (indeed of degree < 2N) agrees with the
    delta bit on the promised single-change domain, while the global character of degree
    2N does. -/
theorem no_low_degree_extension {B N q : Nat} (hq : q < B) {S : List Bool} (hS : S ∈ bitvecs (2 * (B * N)))
    (hdeg : ones S < 2 * N)
    (h : ∀ Q Q', Q.length = N → Q'.length = N → Game.Width B Q → Game.Width B Q' → LocalRestore.OneChange Q Q' →
      (chi S (enc B N Q Q') : R) = sg ((nimSum Q ^^^ nimSum Q').testBit q)) : False := by
  have := char_unique hq hS h
  rw [this, ones_gMask hq] at hdeg; omega

end Generic

/-! ## Agreement with the phase-6 rational statements -/

section RatCheck
open Prob

attribute [local instance] Semiring.natCast

theorem chi_rat (S x : List Bool) : (chi S x : Rat) = sgn (pm S x) := by
  unfold chi; cases pm S x <;> rfl

/-- At ℚ the normalised inner product of two characters is exactly the expression of
    Misc.char_orth, so `orthonormal` instantiates and agrees with it. -/
theorem ip_chi_rat (S T : List Bool) :
    ip (R := Rat) S.length (chi S) (chi T) = rsum (bitvecs S.length) (fun x => sgn (pm S x) * sgn (pm T x)) / 2 ^ S.length := by
  unfold ip
  rw [gs_rat, Rat.div_def]
  congr 1

theorem orthonormal_rat_agrees (S T : List Bool) (h : S.length = T.length) :
    ip (R := Rat) S.length (chi S) (chi T) = if S = T then 1 else 0 := by
  rw [ip_chi_rat]; exact Misc.char_orth S T h

/-- The paper's parity-correlation quantity in the indicator convention (as in the premise
    Bridge.ParityCorrPremise) is the Fourier coefficient of the indicator at the full mask. -/
theorem parity_corr_coef (m : Nat) (g : List Bool → Bool) :
    rsum (bitvecs m) (fun y => Bridge.ind (g y) * sgn (par y)) / 2 ^ m =
      coef (R := Rat) m (fun y => Noise.ind (g y)) (List.replicate m true) := by
  unfold coef ip
  rw [gs_rat, Rat.div_def]
  congr 1
  apply rsum_congr; intro y hy
  rw [chi_rat, par_eq_pm y, mem_bitvecs_length hy]
  show Bridge.ind (g y) * _ = Noise.ind (g y) * _
  cases g y <;> rfl

end RatCheck

/-! ## Axiom checks -/
#print axioms pm_comm
#print axioms pm_xor_right
#print axioms pm_of_false
#print axioms pm_zeros_right
#print axioms pm_selCount
#print axioms cube_mem
#print axioms nodup_map_cons
#print axioms cube_nodup
#print axioms cube_card
#print axioms ofPred_mem
#print axioms ofPred_getD
#print axioms mask_ext
#print axioms mask_of_subset
#print axioms two_pos'
#print axioms two_pow_pos''
#print axioms two_pow_ne
#print axioms pow_mul_inv
#print axioms one_ne_neg_one
#print axioms sg_xor
#print axioms sg_mul_self
#print axioms gs_mul_right
#print axioms gs_count
#print axioms gs_single_le
#print axioms chi_pow
#print axioms coef_congr
#print axioms chi_mul_left
#print axioms chi_mul_right
#print axioms chi_zeros
#print axioms char_sum_gen
#print axioms zipWith_length_eq
#print axioms orth_sum
#print axioms orthonormal
#print axioms dual_sum
#print axioms inversion
#print axioms uniqueness
#print axioms parseval
#print axioms plancherel
#print axioms dim_zero
#print axioms tail_nonneg
#print axioms tail_congr
#print axioms exactDeg_unique
#print axioms tail_of_degLe
#print axioms coef_sq_le_tail
#print axioms bandLimited_corr
#print axioms sign_mass
#print axioms tail_le_one
#print axioms coef_chi
#print axioms tail_chi
#print axioms chi_exactDeg
#print axioms bandLimited_chi
#print axioms sg_eq_ind
#print axioms coef_one
#print axioms sign_indicator
#print axioms par_eq_pm
#print axioms maskU_mem
#print axioms nimBitSign_chi
#print axioms nimBit_spectrum
#print axioms nimBit_corr_of_tail
#print axioms decode_two
#print axioms delta_spectrum
#print axioms delta_move_chi
#print axioms pt_mem
#print axioms pt_getD
#print axioms pm_pt
#print axioms twoMask_mem
#print axioms pm_twoMask
#print axioms twoMask_eq_map
#print axioms ones_map_range
#print axioms ite_lt_succ
#print axioms count_two
#print axioms ones_twoMask
#print axioms twoMask_getD
#print axioms eval_yC
#print axioms yC_chi
#print axioms eval_dC_any
#print axioms getD_replicate_false
#print axioms dSign_true
#print axioms dC_not_character
#print axioms dC_two_coefs
#print axioms dC_one
#print axioms dC_one_exactDeg
#print axioms dC_trivial
#print axioms enc_mem
#print axioms vfun_enc
#print axioms eval_enc
#print axioms dSign_enc
#print axioms set_split
#print axioms dSign_known_heap
#print axioms frame_length
#print axioms frame_mem
#print axioms frame_getD
#print axioms enc_split
#print axioms decode_frame
#print axioms gMask_mem
#print axioms ones_gMask
#print axioms gMask_delta
#print axioms toBitsBE_getD
#print axioms maskU_getD
#print axioms unitBoard_length
#print axioms zero_width
#print axioms unitBoard_width
#print axioms unitBoard_split
#print axioms boardBits_zero
#print axioms boardBits_unit
#print axioms enc_unit_left
#print axioms enc_unit_right
#print axioms pm_pt_left
#print axioms sg_inj
#print axioms char_unique
#print axioms nimSum_zeros
#print axioms enc_zeros
#print axioms char_unique_signed
#print axioms no_low_degree_extension
#print axioms chi_rat
#print axioms ip_chi_rat
#print axioms orthonormal_rat_agrees
#print axioms parity_corr_coef

end Fourier
end NimAudit
