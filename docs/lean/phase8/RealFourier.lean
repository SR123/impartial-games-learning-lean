import Mathlib.Data.Real.Archimedean
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Fourier
import RealNoise

/- Phase 8, part B at ℝ: the Fourier results of Fourier.lean instantiated at Mathlib's real
   numbers, with an explicit equivalence between the list cube `bitvecs n` and Mathlib's
   finite type Fin n → Bool (cube points and character indices), and the transfer of
   finite sums to Mathlib's ∑.  Written by Claude (10 October 2026).  Lean 4.26.0 with
   Mathlib v4.26.0 (commit 2df2f01).

   In the Fin form: x, S : Fin n → Bool, χ_S(x) = (−1)^{Σ_i [S_i ∧ x_i]},
   f̂(S) = 2^{−n} Σ_x f(x) χ_S(x), f(x) = Σ_S f̂(S) χ_S(x) for EVERY f, orthonormality,
   uniqueness, Parseval, tails and the parity spectrum.  B2/B3 for Nim are restated at ℝ in
   the list form used by the earlier modules (the cube there is bitvecs (B·N) resp.
   bitvecs (2·B·N)). -/

namespace NimAudit
namespace RealFourier

open Fourier Noise
open Bridge (bitvecs mem_bitvecs_length mem_bitvecs_of_length ones maskU)

attribute [local instance] Lean.Grind.Semiring.natCast

/-! ## The equivalence between bitvecs n and Fin n → Bool -/

/-- Cube point / mask as a list. -/
def toL {n : ℕ} (v : Fin n → Bool) : List Bool := List.ofFn v

theorem toL_mem {n : ℕ} (v : Fin n → Bool) : toL v ∈ bitvecs n := mem_bitvecs_of_length (by simp [toL])

theorem toL_injective (n : ℕ) : Function.Injective (@toL n) := fun _ _ h => List.ofFn_injective h

/-- Every list of length n is toL of a function (surjectivity onto the cube). -/
theorem toL_surj {n : ℕ} {x : List Bool} (hx : x ∈ bitvecs n) : ∃ v : Fin n → Bool, toL v = x := by
  have hl := mem_bitvecs_length hx
  subst hl
  exact ⟨fun i => x[i.1], List.ofFn_getElem x⟩

/-- The cube as a Finset is the image of Fin n → Bool. -/
theorem image_toL (n : ℕ) : Finset.univ.image (@toL n) = (bitvecs n).toFinset := by
  ext x
  simp only [Finset.mem_image, Finset.mem_univ, true_and, List.mem_toFinset]
  constructor
  · rintro ⟨v, rfl⟩; exact toL_mem v
  · exact toL_surj

/-- SUM TRANSFER: Σ over the list cube = Mathlib's Σ over Fin n → Bool. -/
theorem gs_eq_fintype_sum (n : ℕ) (g : List Bool → ℝ) : gs (bitvecs n) g = ∑ v : Fin n → Bool, g (toL v) := by
  rw [RealNoise.gs_real, ← List.sum_toFinset _ (cube_nodup n), ← image_toL,
    Finset.sum_image (fun a _ b _ h => toL_injective n h)]

/-! ## Fin-form Fourier analysis over ℝ -/

/-- χ_S(x) for S, x : Fin n → Bool. -/
noncomputable def chiF {n : ℕ} (S x : Fin n → Bool) : ℝ := chi (toL S) (toL x)

/-- Number of coordinates selected by S at which x is 1. -/
theorem selCount_toL : ∀ {n : ℕ} (S x : Fin n → Bool),
    selCount (toL S) (toL x) = ∑ i, if S i && x i then 1 else 0
  | 0, S, x => by simp [toL, selCount]
  | n + 1, S, x => by
    simp only [toL, List.ofFn_succ, selCount]
    rw [Fin.sum_univ_succ]
    congr 1
    exact selCount_toL (fun i => S i.succ) (fun i => x i.succ)

/-- THE PAPER'S FORMULA: χ_S(x) = (−1)^{Σ_{i∈S} x_i}. -/
theorem chiF_formula {n : ℕ} (S x : Fin n → Bool) : chiF S x = (-1) ^ (∑ i, if S i && x i then 1 else 0) := by
  unfold chiF; rw [chi_pow, selCount_toL]

/-- |S| = number of i with S i. -/
theorem ones_toL : ∀ {n : ℕ} (S : Fin n → Bool), ones (toL S) = ∑ i, if S i then 1 else 0
  | 0, S => by simp [toL, ones]
  | n + 1, S => by
    rw [Fin.sum_univ_succ, ← ones_toL (fun i => S i.succ)]
    simp only [toL, List.ofFn_succ, ones, List.filter_cons]
    cases S 0 <;> simp <;> omega

/-- Fourier coefficient on Fin n → Bool, with the uniform normalisation. -/
noncomputable def fhat {n : ℕ} (F : (Fin n → Bool) → ℝ) (S : Fin n → Bool) : ℝ :=
  (2 ^ n)⁻¹ * ∑ x, F x * chiF S x

/-- Lift of a function on Fin n → Bool to lists (0 off the cube). -/
noncomputable def lift {n : ℕ} (F : (Fin n → Bool) → ℝ) (x : List Bool) : ℝ :=
  if h : x.length = n then F (fun i => x[i.1]'(by omega)) else 0

theorem lift_toL {n : ℕ} (F : (Fin n → Bool) → ℝ) (v : Fin n → Bool) : lift F (toL v) = F v := by
  unfold lift toL
  rw [dif_pos (by simp)]
  congr 1; funext i; simp

theorem fhat_eq_coef {n : ℕ} (F : (Fin n → Bool) → ℝ) (S : Fin n → Bool) : fhat F S = coef n (lift F) (toL S) := by
  unfold fhat coef ip
  rw [gs_eq_fintype_sum, mul_comm]
  congr 1
  apply Finset.sum_congr rfl; intro v _
  rw [lift_toL]; rfl

/-- B1 AT ℝ (Fin form). FOURIER INVERSION for every F : (Fin n → Bool) → ℝ. -/
theorem inversion_fin {n : ℕ} (F : (Fin n → Bool) → ℝ) (x : Fin n → Bool) :
    F x = ∑ S, fhat F S * chiF S x := by
  have h := inversion (R := ℝ) n (lift F) (toL_mem x)
  rw [lift_toL, gs_eq_fintype_sum] at h
  rw [← h]
  apply Finset.sum_congr rfl; intro S _
  rw [fhat_eq_coef]; rfl

/-- ORTHONORMALITY (Fin form). -/
theorem orthonormal_fin {n : ℕ} (S T : Fin n → Bool) :
    (2 ^ n)⁻¹ * ∑ x, chiF S x * chiF T x = if S = T then 1 else 0 := by
  have h := orthonormal (R := ℝ) (toL_mem S) (toL_mem T)
  unfold ip at h
  rw [gs_eq_fintype_sum, mul_comm] at h
  rw [show (if S = T then (1 : ℝ) else 0) = if toL S = toL T then 1 else 0 by
    by_cases hST : S = T
    · simp [hST]
    · rw [if_neg hST, if_neg (fun e => hST (toL_injective n e))]]
  rw [← h]; rfl

/-- UNIQUENESS (Fin form). -/
theorem uniqueness_fin {n : ℕ} (F : (Fin n → Bool) → ℝ) (c : (Fin n → Bool) → ℝ)
    (h : ∀ x, F x = ∑ S, c S * chiF S x) : ∀ S, fhat F S = c S := by
  intro S
  rw [fhat_eq_coef]
  have hc := uniqueness (R := ℝ) n (lift F) (lift c) (fun x hx => by
    obtain ⟨v, rfl⟩ := toL_surj hx
    rw [lift_toL, h v, gs_eq_fintype_sum]
    apply Finset.sum_congr rfl; intro T _
    rw [lift_toL]; rfl) (toL S) (toL_mem S)
  rw [hc, lift_toL]

/-- PARSEVAL (Fin form). -/
theorem parseval_fin {n : ℕ} (F G : (Fin n → Bool) → ℝ) :
    (2 ^ n)⁻¹ * ∑ x, F x * G x = ∑ S, fhat F S * fhat G S := by
  have h := parseval (R := ℝ) n (lift F) (lift G)
  unfold ip at h
  rw [gs_eq_fintype_sum, gs_eq_fintype_sum, mul_comm] at h
  have e1 : ∑ x, F x * G x = ∑ x : Fin n → Bool, lift F (toL x) * lift G (toL x) := by
    apply Finset.sum_congr rfl; intro v _; rw [lift_toL, lift_toL]
  rw [e1, h]
  apply Finset.sum_congr rfl; intro S _
  rw [fhat_eq_coef, fhat_eq_coef]

/-- n = 0: one point, one character, f̂(S) = f(x) for the unique S and x. -/
theorem dim_zero_fin (F : (Fin 0 → Bool) → ℝ) (x S : Fin 0 → Bool) : F x = fhat F S * chiF S x := by
  rw [inversion_fin F x, Fintype.sum_unique]
  congr 1 <;> congr 1 <;> exact Subsingleton.elim _ _

/-- Degree-> k tail (Fin form). -/
noncomputable def tailF {n : ℕ} (F : (Fin n → Bool) → ℝ) (k : ℕ) : ℝ :=
  ∑ S : Fin n → Bool, if k < ∑ i, (if S i then 1 else 0) then fhat F S ^ 2 else 0

theorem tailF_eq {n : ℕ} (F : (Fin n → Bool) → ℝ) (k : ℕ) : tailF F k = tail n (lift F) k := by
  unfold tailF tail
  rw [gs_eq_fintype_sum]
  apply Finset.sum_congr rfl; intro S _
  rw [ones_toL, fhat_eq_coef]

/-- PARITY IS A PURE CHARACTER (Fin form): f̂_{χ_S}(T) = [T = S], and its tail is 1 below
    |S| and 0 from |S| on. -/
theorem parity_fin {n : ℕ} (S : Fin n → Bool) :
    (∀ T, fhat (chiF S) T = if T = S then 1 else 0) ∧
    ∀ k, tailF (chiF S) k = if k < ∑ i, (if S i then 1 else 0) then 1 else 0 := by
  have hc : ∀ x ∈ bitvecs n, lift (chiF S) x = chi (R := ℝ) (toL S) x := by
    intro x hx; obtain ⟨v, rfl⟩ := toL_surj hx; rw [lift_toL]; rfl
  refine ⟨fun T => ?_, fun k => ?_⟩
  · rw [fhat_eq_coef, coef_congr hc, coef_chi (toL_mem S) (toL_mem T)]
    by_cases h : T = S
    · simp [h]
    · rw [if_neg h, if_neg (fun e => h (toL_injective n e))]
  · rw [tailF_eq, tail_congr hc, tail_chi (toL_mem S), ones_toL]

/-! ## B2 and B3 at ℝ (list form, as in the Nim modules) -/

theorem nimBit_spectrum_real {B N j : ℕ} (hj : j < B) :
    (∀ T ∈ bitvecs (B * N), coef (B * N) (nimBitSign (R := ℝ) B N j) T = if T = maskU B N (2 ^ j) then 1 else 0) ∧
    ones (maskU B N (2 ^ j)) = N ∧ ExactDeg (B * N) (nimBitSign (R := ℝ) B N j) N ∧
    ∀ k, tail (B * N) (nimBitSign (R := ℝ) B N j) k = if k < N then 1 else 0 :=
  nimBit_spectrum hj

theorem delta_spectrum_real {B j : ℕ} (hj : j < B) :
    (∀ w ∈ bitvecs (B * 2), (deltaSign B j w : ℝ) = chi (maskU B 2 (2 ^ j)) w) ∧
    ones (maskU B 2 (2 ^ j)) = 2 ∧ ExactDeg (B * 2) (deltaSign (R := ℝ) B j) 2 :=
  delta_spectrum hj

theorem bandLimited_corr_real {n : ℕ} {f : List Bool → ℝ} {k : ℕ} {ε : ℝ} (hb : BandLimited n f k ε)
    {S : List Bool} (hS : S ∈ bitvecs n) (hk : k < ones S) : ip n f (chi S) ^ 2 ≤ ε :=
  bandLimited_corr hb hS hk

theorem dC_not_character_real {B N q : ℕ} (hN : 2 ≤ N) (hq : q < B) :
    ¬ ∃ (S : List Bool) (c : ℝ), c * c = 1 ∧ ∀ z ∈ bitvecs (2 * (B * N)), dSign B N q z = c * chi S z :=
  dC_not_character hN hq

theorem dC_two_coefs_real {B N q : ℕ} (hN : 2 ≤ N) (hq : q < B) :
    ∃ S ∈ bitvecs (2 * (B * N)), ∃ T ∈ bitvecs (2 * (B * N)), S ≠ T ∧
      coef (2 * (B * N)) (dSign (R := ℝ) B N q) S ≠ 0 ∧ coef (2 * (B * N)) (dSign (R := ℝ) B N q) T ≠ 0 :=
  dC_two_coefs hN hq

theorem dSign_enc_real {B N q : ℕ} {Q Q' : List ℕ} (hQ : Q.length = N) (hQ' : Q'.length = N)
    (hw : Game.Width B Q) (hw' : Game.Width B Q') (h1 : LocalRestore.OneChange Q Q') :
    (dSign B N q (enc B N Q Q') : ℝ) = sg ((nimSum Q ^^^ nimSum Q').testBit q) :=
  dSign_enc hQ hQ' hw hw' h1

theorem dSign_known_heap_real {B N q i : ℕ} (hq : q < B) (hi : i < N) {Q : List ℕ} (hQ : Q.length = N) (y : ℕ) :
    (dSign B N q (enc B N Q (Q.set i y)) : ℝ) =
      chi (twoMask (2 * (B * N)) (B * i + (B - 1 - q)) (B * N + (B * i + (B - 1 - q)))) (enc B N Q (Q.set i y)) :=
  dSign_known_heap hq hi hQ y

theorem dC_one_exactDeg_real {B q : ℕ} (hq : q < B) : ExactDeg (2 * (B * 1)) (dSign (R := ℝ) B 1 q) 2 :=
  dC_one_exactDeg hq

theorem gMask_delta_real {B N q : ℕ} (hq : q < B) {Q Q' : List ℕ} (hQ : Q.length = N) (hQ' : Q'.length = N)
    (hw : Game.Width B Q) (hw' : Game.Width B Q') :
    (chi (gMask B N q) (enc B N Q Q') : ℝ) = sg ((nimSum Q ^^^ nimSum Q').testBit q) :=
  gMask_delta hq hQ hQ' hw hw'

theorem char_unique_real {B N q : ℕ} (hq : q < B) {S : List Bool} (hS : S ∈ bitvecs (2 * (B * N)))
    (h : ∀ Q Q', Q.length = N → Q'.length = N → Game.Width B Q → Game.Width B Q' → LocalRestore.OneChange Q Q' →
      (chi S (enc B N Q Q') : ℝ) = sg ((nimSum Q ^^^ nimSum Q').testBit q)) :
    S = gMask B N q :=
  char_unique hq hS h

theorem char_unique_signed_real {B N q : ℕ} (hq : q < B) {S : List Bool} (hS : S ∈ bitvecs (2 * (B * N)))
    {c : ℝ} (h : ∀ Q Q', Q.length = N → Q'.length = N → Game.Width B Q → Game.Width B Q' → LocalRestore.OneChange Q Q' →
      c * chi S (enc B N Q Q') = sg ((nimSum Q ^^^ nimSum Q').testBit q)) :
    c = 1 ∧ S = gMask B N q :=
  char_unique_signed hq hS h

theorem no_low_degree_extension_real {B N q : ℕ} (hq : q < B) {S : List Bool} (hS : S ∈ bitvecs (2 * (B * N)))
    (hdeg : ones S < 2 * N)
    (h : ∀ Q Q', Q.length = N → Q'.length = N → Game.Width B Q → Game.Width B Q' → LocalRestore.OneChange Q Q' →
      (chi S (enc B N Q Q') : ℝ) = sg ((nimSum Q ^^^ nimSum Q').testBit q)) : False :=
  no_low_degree_extension hq hS hdeg h

/-! ## Axiom checks -/
#print axioms toL_mem
#print axioms toL_injective
#print axioms toL_surj
#print axioms image_toL
#print axioms gs_eq_fintype_sum
#print axioms selCount_toL
#print axioms chiF_formula
#print axioms ones_toL
#print axioms lift_toL
#print axioms fhat_eq_coef
#print axioms inversion_fin
#print axioms orthonormal_fin
#print axioms uniqueness_fin
#print axioms parseval_fin
#print axioms dim_zero_fin
#print axioms tailF_eq
#print axioms parity_fin
#print axioms nimBit_spectrum_real
#print axioms delta_spectrum_real
#print axioms bandLimited_corr_real
#print axioms dC_not_character_real
#print axioms dC_two_coefs_real
#print axioms dSign_enc_real
#print axioms dSign_known_heap_real
#print axioms dC_one_exactDeg_real
#print axioms gMask_delta_real
#print axioms char_unique_real
#print axioms char_unique_signed_real
#print axioms no_low_degree_extension_real

end RealFourier
end NimAudit
