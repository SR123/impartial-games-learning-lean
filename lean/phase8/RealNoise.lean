import Mathlib.Data.Real.Archimedean
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.GCongr
import NoiseModel

/- Phase 8, part A: the noise model at Mathlib's real numbers, an explicit integer sample
   count, the minimum sample count and its two-sided a^{-2} bounds, and the flip model.
   Written by Claude (10 October 2026).  Lean 4.26.0 with Mathlib v4.26.0 (commit 2df2f01),
   imported read-only from the pinned phase-8 Lake dependency.

   Paper target: Remark rem:noisy-rollout-decay.

   A1  The phase-7 theorems are stated for any type with Lean core's ordered-field
       interface.  At ℝ the six interfaces are Mathlib's instances (Field.toGrindField,
       the IsStrictOrderedRing → Lean.Grind.OrderedRing instance, LinearOrder →
       Std.IsLinearOrder, Preorder → Std.LawfulOrderLT); the adapters below show that the
       interface operations ARE Mathlib's (casts, inverses, powers: by rfl) and that the
       generic finite sum is List.sum.  Every theorem here applies the phase-7 theorem at ℝ.
   A2  The symmetric channel with p = (1 + a)/2; the integer m(a) = ⌈4/a²⌉₊ (Mathlib's
       Nat.ceil, available because ℝ is Archimedean); majority (ties declared 0) succeeds
       at every m ≥ m(a); every randomized rule with both errors ≤ 1/4 needs 32·m·a² ≥ 3.
   A3  mMin a = the least m for which SOME randomized rule has both errors ≤ 1/4: it exists,
       is attained and is minimal, and 3/(32a²) ≤ mMin a ≤ ⌈4/a²⌉₊ < 4/a² + 1 ≤ 17/(4a²)
       for 0 < a ≤ 1/2 (a uniform Θ(a^{-2}) statement with explicit constants).
       Boundaries: a = 0 (no m works), a = 1 (mMin = 1), m = 0 never works.
   A4  The flip model at ℝ: product law, agreement formula, fresh-block repetition law,
       and the sample-size conclusions for a = (1 − 2ε)^L with 0 ≤ ε < 1/2 in the
       small-bias regime a ≤ 1/2, which holds for every L ≥ ⌈1/(2ε)⌉₊ when ε > 0.
       ε = 0 or L = 0 give a = 1 (exact observations).  Reusing one error block for all
       repetitions (no fresh randomness) gives NO improvement: majority error stays
       (1 − a)/2. -/

namespace NimAudit
namespace RealNoise

open Noise
open Bridge (bitvecs par mem_bitvecs_length mem_bitvecs_of_length)

attribute [local instance] Lean.Grind.Semiring.natCast

/-! ## A1. The real interfaces and adapters -/

/-- The interface cast is Mathlib's cast. -/
theorem natCast_real (m : ℕ) : (@Nat.cast ℝ Lean.Grind.Semiring.natCast m) = (m : ℝ) := rfl

/-- The interface inverse is Mathlib's inverse. -/
theorem inv_real (x : ℝ) : (@Inv.inv ℝ (Lean.Grind.Field.toInv) x) = x⁻¹ := rfl

/-- The interface power (Lean.Grind.Semiring.npow, used in every generic statement) is
    Mathlib's monoid power. -/
theorem pow_real (x : ℝ) (n : ℕ) : @HPow.hPow ℝ ℕ ℝ (@Lean.Grind.Semiring.npow ℝ inferInstance) x n = x ^ n := rfl

/-- The interface addition, multiplication and numerals are Mathlib's. -/
theorem add_mul_real (x y : ℝ) :
    @HAdd.hAdd ℝ ℝ ℝ (@instHAdd ℝ (@Lean.Grind.Semiring.toAdd ℝ inferInstance)) x y = x + y ∧
    @HMul.hMul ℝ ℝ ℝ (@instHMul ℝ (@Lean.Grind.Semiring.toMul ℝ inferInstance)) x y = x * y ∧
    @OfNat.ofNat ℝ 2 (@Lean.Grind.Semiring.ofNat ℝ inferInstance 2) = (2 : ℝ) := ⟨rfl, rfl, rfl⟩

/-- The generic finite sum at ℝ is Mathlib's List.sum. -/
theorem gs_real {α : Type} (l : List α) (f : α → ℝ) : gs l f = (l.map f).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [gs_cons, ih, List.map_cons, List.sum_cons]

/-! ## A2. The symmetric observation channel over ℝ -/

/-- Agreement probability for signed bias a. -/
noncomputable def pOf (a : ℝ) : ℝ := (1 + a) / 2

theorem two_pOf (a : ℝ) : 2 * pOf a = 1 + a := by unfold pOf; ring

theorem pOf_bounds {a : ℝ} (h0 : -1 ≤ a) (h1 : a ≤ 1) : 0 ≤ pOf a ∧ pOf a ≤ 1 := by
  unfold pOf; constructor <;> linarith

/-- The m-sample channel law is a probability law (nonnegative, total mass 1). -/
theorem chan_law {a : ℝ} (h0 : -1 ≤ a) (h1 : a ≤ 1) (Y : Bool) (m : ℕ) :
    (∀ o, 0 ≤ chanW (pOf a) Y o) ∧ gs (bitvecs m) (chanW (pOf a) Y) = 1 :=
  ⟨chan_nonneg (pOf_bounds h0 h1).1 (pOf_bounds h0 h1).2 Y, chan_total _ Y m⟩

/-- The explicit integer sample count m(a) = ⌈4/a²⌉₊. -/
noncomputable def mUp (a : ℝ) : ℕ := ⌈4 / a ^ 2⌉₊

/-- THE ARCHIMEDEAN STEP: m(a)·a² ≥ 4 for every real a > 0. -/
theorem mUp_spec {a : ℝ} (ha : 0 < a) : 4 ≤ (mUp a : ℝ) * a ^ 2 := by
  have h1 : 4 / a ^ 2 ≤ (mUp a : ℝ) := Nat.le_ceil _
  have h2 : 0 < a ^ 2 := by positivity
  calc (4 : ℝ) = 4 / a ^ 2 * a ^ 2 := by field_simp
    _ ≤ (mUp a : ℝ) * a ^ 2 := by gcongr

theorem archimedean_step {a : ℝ} (ha : 0 < a) : ∃ m : ℕ, 4 ≤ (m : ℝ) * a ^ 2 := ⟨mUp a, mUp_spec ha⟩

theorem mUp_pos {a : ℝ} (ha : 0 < a) : 1 ≤ mUp a := by
  unfold mUp; rw [Nat.one_le_ceil_iff]; positivity

theorem mUp_lt {a : ℝ} (ha : 0 < a) : (mUp a : ℝ) < 4 / a ^ 2 + 1 :=
  Nat.ceil_lt_add_one (by positivity)

/-- With a ≤ 1/2 at least 16 samples are used. -/
theorem mUp_ge_16 {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1 / 2) : 16 ≤ mUp a := by
  have h1 : (16 : ℝ) ≤ 4 / a ^ 2 := by
    rw [le_div_iff₀ (by positivity)]; nlinarith
  have h2 : 4 / a ^ 2 ≤ (mUp a : ℝ) := Nat.le_ceil _
  exact_mod_cast le_trans h1 h2

/-- A2 (UPPER BOUND, at ℝ): for 0 < a ≤ 1 the majority rule (ties declared 0) has both error
    probabilities at most 1/4 for EVERY m ≥ m(a), in particular at m = m(a). -/
theorem majority_succeeds {a : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1) {m : ℕ} (hm : mUp a ≤ m) :
    err0 (pOf a) m (detRule maj) ≤ 1 / 4 ∧ err1 (pOf a) m (detRule maj) ≤ 1 / 4 := by
  have hmm : 4 ≤ (m : ℝ) * a ^ 2 := by
    have := mUp_spec ha0
    have h' : (mUp a : ℝ) ≤ m := by exact_mod_cast hm
    nlinarith [sq_nonneg a]
  have h := maj_upper (R := ℝ) (pOf a) a (two_pOf a) ha0 ha1 m hmm
  constructor <;> linarith [h.1, h.2]

/-- A2 (LOWER BOUND, at ℝ): for 0 < a ≤ 1/2, EVERY randomized rule (acceptance probability
    φ(o) ∈ [0,1]) with both errors ≤ 1/4 uses at least 3/(32a²) samples. -/
theorem any_rule_needs {a : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1 / 2) (m : ℕ) (φ : List Bool → ℝ) (hφ : Rule m φ)
    (h0 : err0 (pOf a) m φ ≤ 1 / 4) (h1 : err1 (pOf a) m φ ≤ 1 / 4) : 3 / (32 * a ^ 2) ≤ (m : ℝ) := by
  have h := lower_bound (R := ℝ) (pOf a) a (two_pOf a) ha0 (by linarith) m φ hφ (by linarith) (by linarith)
  rw [div_le_iff₀ (by positivity)]; linarith

/-! ## A3. The minimum sufficient sample count -/

/-- Some randomized rule on m samples has both errors ≤ 1/4. -/
def Ach (a : ℝ) (m : ℕ) : Prop := Achievable (pOf a) m

theorem ach_of_ge {a : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1) {m : ℕ} (hm : mUp a ≤ m) : Ach a m := by
  obtain ⟨h0, h1⟩ := majority_succeeds ha0 ha1 hm
  exact ⟨detRule maj, detRule_rule m maj, by linarith, by linarith⟩

theorem ach_exists {a : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1) : ∃ m, Ach a m := ⟨mUp a, ach_of_ge ha0 ha1 le_rfl⟩

open Classical in
/-- The least sufficient natural sample count; by convention 0 when no m suffices (e.g. at
    a = 0, `zero_signal_never`).  Every theorem below assumes a > 0, where it exists. -/
noncomputable def mMin (a : ℝ) : ℕ := if h : ∃ m, Ach a m then Nat.find h else 0

/-- EXISTENCE, ATTAINMENT AND MINIMALITY. -/
theorem mMin_spec {a : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1) :
    Ach a (mMin a) ∧ ∀ m, Ach a m → mMin a ≤ m := by
  classical
  have h := ach_exists ha0 ha1
  unfold mMin; rw [dif_pos h]
  exact ⟨Nat.find_spec h, fun m hm => Nat.find_min' h hm⟩

/-- A3 TWO-SIDED BOUNDS: 3/(32a²) ≤ mMin a ≤ ⌈4/a²⌉₊ < 4/a² + 1. -/
theorem mMin_bounds {a : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1 / 2) :
    3 / (32 * a ^ 2) ≤ (mMin a : ℝ) ∧ mMin a ≤ mUp a ∧ (mUp a : ℝ) < 4 / a ^ 2 + 1 := by
  obtain ⟨hach, hmin⟩ := mMin_spec ha0 (by linarith)
  obtain ⟨φ, hφ, h0, h1⟩ := hach
  refine ⟨any_rule_needs ha0 ha1 _ φ hφ (by linarith) (by linarith), hmin _ (ach_of_ge ha0 (by linarith) le_rfl),
    mUp_lt ha0⟩

/-- UNIFORM Θ(a^{-2}) WITH EXPLICIT CONSTANTS: for all 0 < a ≤ 1/2,
      (3/32)·a^{-2} ≤ mMin a ≤ (17/4)·a^{-2}. -/
theorem mMin_theta {a : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1 / 2) :
    3 / 32 * (a ^ 2)⁻¹ ≤ (mMin a : ℝ) ∧ (mMin a : ℝ) ≤ 17 / 4 * (a ^ 2)⁻¹ := by
  obtain ⟨h1, h2, h3⟩ := mMin_bounds ha0 ha1
  have hpos : 0 < a ^ 2 := by positivity
  have hsq : a ^ 2 ≤ 1 / 4 := by nlinarith
  constructor
  · calc 3 / 32 * (a ^ 2)⁻¹ = 3 / (32 * a ^ 2) := by field_simp
      _ ≤ _ := h1
  · have h2' : (mMin a : ℝ) ≤ mUp a := by exact_mod_cast h2
    have h4 : 4 / a ^ 2 + 1 ≤ 17 / 4 * (a ^ 2)⁻¹ := by
      rw [show 17 / 4 * (a ^ 2)⁻¹ = 4 / a ^ 2 + 1 / (4 * a ^ 2) by field_simp; ring]
      have : (1 : ℝ) ≤ 1 / (4 * a ^ 2) := by rw [le_div_iff₀ (by positivity)]; linarith
      linarith
    linarith

/-- The same in product form: 3/32 ≤ mMin a · a² ≤ 17/4. -/
theorem mMin_scaled {a : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1 / 2) :
    3 / 32 ≤ (mMin a : ℝ) * a ^ 2 ∧ (mMin a : ℝ) * a ^ 2 ≤ 17 / 4 := by
  obtain ⟨h1, h2⟩ := mMin_theta ha0 ha1
  have hpos : 0 < a ^ 2 := by positivity
  constructor
  · have := mul_le_mul_of_nonneg_right h1 hpos.le
    rwa [mul_assoc, inv_mul_cancel₀ hpos.ne', mul_one] at this
  · have := mul_le_mul_of_nonneg_right h2 hpos.le
    rwa [mul_assoc, inv_mul_cancel₀ hpos.ne', mul_one] at this

/-- Zero samples never suffice (a constant rule has err₀ + err₁ = 1). -/
theorem zero_samples_never (a : ℝ) : ¬ Ach a 0 := by
  rintro ⟨φ, _, h0, h1⟩
  simp only [err0, err1, bitvecs, gs_cons, gs_nil, chanW] at h0 h1
  linarith

/-- ZERO-SIGNAL BOUNDARY (a = 0, e.g. ε = 1/2 with L > 0): no sample count suffices. -/
theorem zero_signal_never (m : ℕ) : ¬ Ach 0 m := by
  rintro ⟨φ, _, h0, h1⟩
  have := no_signal (R := ℝ) (pOf 0) (by unfold pOf; ring) m φ
  linarith

/-- EXACT OBSERVATIONS (a = 1): one sample suffices and is necessary. -/
theorem mMin_one : mMin 1 = 1 := by
  obtain ⟨hach, hmin⟩ := mMin_spec (a := 1) one_pos le_rfl
  have h1 : Ach 1 1 := by
    have := exact_channel (R := ℝ)
    refine ⟨fun o => ind (o.getD 0 false), fun o _ => ⟨?_, ?_⟩, ?_, ?_⟩
    · show (0 : ℝ) ≤ ind (o.getD 0 false); unfold ind; split <;> norm_num
    · show ind (o.getD 0 false) ≤ (1 : ℝ); unfold ind; split <;> norm_num
    · rw [show pOf 1 = 1 by unfold pOf; norm_num, this.1]; norm_num
    · rw [show pOf 1 = 1 by unfold pOf; norm_num, this.2]; norm_num
  have hle := hmin 1 h1
  have hne : mMin 1 ≠ 0 := fun h => zero_samples_never 1 (h ▸ hach)
  omega

/-- An extra sample can be ignored: achievability is monotone in m. -/
theorem err_succ (p : ℝ) (m : ℕ) (φ : List Bool → ℝ) :
    err0 p (m + 1) (fun o => φ o.tail) = err0 p m φ ∧ err1 p (m + 1) (fun o => φ o.tail) = err1 p m φ := by
  unfold err0 err1
  rw [gs_bitvecs_succ, gs_bitvecs_succ]
  have a1 : ∀ v, chanW p false (false :: v) * φ (false :: v).tail = p * (chanW p false v * φ v) := by
    intro v; simp only [chanW, List.tail_cons, if_true]; ring
  have a2 : ∀ v, chanW p false (true :: v) * φ (true :: v).tail = (1 - p) * (chanW p false v * φ v) := by
    intro v; simp only [chanW, List.tail_cons, Bool.true_eq_false, if_false]; ring
  have b1 : ∀ v, chanW p true (false :: v) * (1 - φ (false :: v).tail) = (1 - p) * (chanW p true v * (1 - φ v)) := by
    intro v; simp only [chanW, List.tail_cons, Bool.false_eq_true, if_false]; ring
  have b2 : ∀ v, chanW p true (true :: v) * (1 - φ (true :: v).tail) = p * (chanW p true v * (1 - φ v)) := by
    intro v; simp only [chanW, List.tail_cons, if_true]; ring
  rw [gs_congr (fun v _ => a1 v), gs_congr (fun v _ => a2 v), gs_congr (fun v _ => b1 v), gs_congr (fun v _ => b2 v),
    gs_mul_left, gs_mul_left, gs_mul_left, gs_mul_left]
  constructor <;> ring

theorem ach_succ {a : ℝ} {m : ℕ} (h : Ach a m) : Ach a (m + 1) := by
  obtain ⟨φ, hφ, h0, h1⟩ := h
  obtain ⟨e0, e1⟩ := err_succ (pOf a) m φ
  refine ⟨fun o => φ o.tail, fun o ho => ?_, by rw [e0]; exact h0, by rw [e1]; exact h1⟩
  have hl := mem_bitvecs_length ho
  exact hφ o.tail (mem_bitvecs_of_length (by simp [hl]))

theorem ach_mono {a : ℝ} {m m' : ℕ} (h : Ach a m) (hm : m ≤ m') : Ach a m' := by
  induction hm with
  | refl => exact h
  | step _ ih => exact ach_succ ih

/-- THE SUFFICIENT COUNTS FORM A RAY: for a > 0, m samples suffice iff m ≥ mMin a. -/
theorem ach_iff_ge {a : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1) (m : ℕ) : Ach a m ↔ mMin a ≤ m :=
  ⟨fun h => (mMin_spec ha0 ha1).2 m h, fun h => ach_mono (mMin_spec ha0 ha1).1 h⟩

/-! ## A4. The flip model at ℝ -/

/-- The product Bernoulli(ε) law on {0,1}^L: nonnegative, total mass 1, marginals ε. -/
theorem flip_law {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (L : ℕ) :
    (∀ e, 0 ≤ fw ε e) ∧ gs (bitvecs L) (fw ε) = 1 ∧ ∀ i, i < L → prob ε L (fun e => e.getD i false) = ε :=
  ⟨fw_nonneg h0 h1, fw_total ε L, fun _ hi => fw_marginal ε hi⟩

/-- Independence (product rule) for the flip law at ℝ. -/
theorem flip_independent (ε : ℝ) (f : ℕ → Bool → ℝ) (L k : ℕ) :
    gs (bitvecs L) (fun e => fw ε e * pf f k e) = pe ε f k L := fw_product ε f L k

/-- The agreement formula of the remark, at ℝ. -/
theorem flip_agree_real (ε : ℝ) (L : ℕ) : agree ε L = (1 + (1 - 2 * ε) ^ L) / 2 := by
  have := agree_formula (R := ℝ) ε L
  linarith

theorem agree_eq_pOf (ε : ℝ) (L : ℕ) : agree ε L = pOf ((1 - 2 * ε) ^ L) := by
  rw [flip_agree_real]; rfl

/-- Fresh blocks: the m observations have the product channel law with p = agree ε L. -/
theorem flip_repeated (ε : ℝ) (Y : Bool) (L m : ℕ) (o : List Bool) (ho : o.length = m) :
    gs (bitvecs (m * L)) (fun e => fw ε e * ind (decide (obsOf Y L m e = o))) = chanW (agree ε L) Y o :=
  repeated_law ε Y L m o ho

/-- The bias is positive for ε < 1/2. -/
theorem flip_bias_pos {ε : ℝ} (h1 : ε < 1 / 2) (L : ℕ) : 0 < (1 - 2 * ε) ^ L := by
  apply pow_pos; linarith

/-- A4 SAMPLE SIZES FOR THE FLIP MODEL: for 0 ≤ ε < 1/2 and a = (1 − 2ε)^L ≤ 1/2, with errors
    computed on the space of m·L independent flips (fresh blocks):
      majority succeeds for every m ≥ ⌈4/a²⌉₊;  every randomized rule with both errors ≤ 1/4
      needs 32·m·a² ≥ 3;  and the minimum sufficient m satisfies the Θ(a^{-2}) bounds. -/
theorem flip_samples {ε : ℝ} (h1 : ε < 1 / 2) (L : ℕ) (hsmall : (1 - 2 * ε) ^ L ≤ 1 / 2) :
    (∀ m, mUp ((1 - 2 * ε) ^ L) ≤ m →
      gs (bitvecs (m * L)) (fun e => fw ε e * detRule maj (obsOf false L m e)) ≤ 1 / 4 ∧
      gs (bitvecs (m * L)) (fun e => fw ε e * (1 - detRule maj (obsOf true L m e))) ≤ 1 / 4) ∧
    (∀ (m : ℕ) (φ : List Bool → ℝ), Rule m φ →
      gs (bitvecs (m * L)) (fun e => fw ε e * φ (obsOf false L m e)) ≤ 1 / 4 →
      gs (bitvecs (m * L)) (fun e => fw ε e * (1 - φ (obsOf true L m e))) ≤ 1 / 4 →
      3 / (32 * ((1 - 2 * ε) ^ L) ^ 2) ≤ (m : ℝ)) ∧
    3 / 32 * (((1 - 2 * ε) ^ L) ^ 2)⁻¹ ≤ (mMin ((1 - 2 * ε) ^ L) : ℝ) ∧
    (mMin ((1 - 2 * ε) ^ L) : ℝ) ≤ 17 / 4 * (((1 - 2 * ε) ^ L) ^ 2)⁻¹ := by
  have ha0 := flip_bias_pos h1 L
  refine ⟨fun m hm => ?_, fun m φ hφ e0 e1 => ?_, (mMin_theta ha0 hsmall).1, (mMin_theta ha0 hsmall).2⟩
  · rw [rep_expect ε false L m (detRule maj), rep_expect ε true L m (fun o => 1 - detRule maj o), agree_eq_pOf]
    exact majority_succeeds ha0 (by linarith) hm
  · rw [rep_expect ε false L m φ, agree_eq_pOf] at e0
    rw [rep_expect ε true L m (fun o => 1 - φ o), agree_eq_pOf] at e1
    exact any_rule_needs ha0 hsmall m φ hφ e0 e1

/-- Achievability with errors computed on the space of m·L independent flips (fresh blocks). -/
def FlipAch (ε : ℝ) (L m : ℕ) : Prop :=
  ∃ φ : List Bool → ℝ, Rule m φ ∧
    gs (bitvecs (m * L)) (fun e => fw ε e * φ (obsOf false L m e)) ≤ 1 / 4 ∧
    gs (bitvecs (m * L)) (fun e => fw ε e * (1 - φ (obsOf true L m e))) ≤ 1 / 4

/-- The flip-space problem and the channel problem with a = (1 − 2ε)^L have the same
    achievable sample counts; so mMin a is also the minimum for the flip model. -/
theorem flipAch_iff (ε : ℝ) (L m : ℕ) : FlipAch ε L m ↔ Ach ((1 - 2 * ε) ^ L) m := by
  unfold FlipAch Ach Achievable
  constructor
  · rintro ⟨φ, hφ, h0, h1⟩
    rw [rep_expect ε false L m φ, agree_eq_pOf] at h0
    rw [rep_expect ε true L m (fun o => 1 - φ o), agree_eq_pOf] at h1
    exact ⟨φ, hφ, by unfold err0; linarith, by unfold err1; linarith⟩
  · rintro ⟨φ, hφ, h0, h1⟩
    refine ⟨φ, hφ, ?_, ?_⟩
    · rw [rep_expect ε false L m φ, agree_eq_pOf]; unfold err0 at h0; linarith
    · rw [rep_expect ε true L m (fun o => 1 - φ o), agree_eq_pOf]; unfold err1 at h1; linarith

/-- For 0 ≤ ε < 1/2 the flip-space sample counts that suffice are exactly m ≥ mMin a. -/
theorem flip_mMin {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε < 1 / 2) (L m : ℕ) :
    FlipAch ε L m ↔ mMin ((1 - 2 * ε) ^ L) ≤ m := by
  rw [flipAch_iff]
  exact ach_iff_ge (flip_bias_pos h1 L) (pow_le_one₀ (by linarith) (by linarith)) m

/-- ε = 0 or L = 0: exact observations (a = 1, one sample suffices and is needed). -/
theorem flip_exact {ε : ℝ} {L : ℕ} (h : ε = 0 ∨ L = 0) : (1 - 2 * ε) ^ L = 1 ∧ mMin ((1 - 2 * ε) ^ L) = 1 := by
  have e : (1 - 2 * ε) ^ L = 1 := by
    rcases h with rfl | rfl
    · simp
    · simp
  exact ⟨e, by rw [e]; exact mMin_one⟩

theorem bernoulli_real {x : ℝ} (hx : 0 ≤ x) : ∀ n : ℕ, 1 + (n : ℝ) * x ≤ (1 + x) ^ n
  | 0 => by simp
  | n + 1 => by
    have ih := bernoulli_real hx n
    push_cast
    rw [pow_succ]
    nlinarith [mul_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n) (mul_nonneg hx hx)]

/-- THE SMALL-BIAS REGIME IS EVENTUALLY REACHED: for 0 < ε < 1/2,
    (1 − 2ε)^L ≤ 1/2 for every L ≥ ⌈1/(2ε)⌉₊ (via (1 − x)^L ≤ 1/(1 + Lx)). -/
theorem eventually_small {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1 / 2) {L : ℕ} (hL : ⌈1 / (2 * ε)⌉₊ ≤ L) :
    (1 - 2 * ε) ^ L ≤ 1 / 2 := by
  set x := 2 * ε with hx
  have hx0 : 0 < x := by positivity
  have hx1 : x < 1 := by linarith
  have hLx : 1 ≤ (L : ℝ) * x := by
    have h' : 1 / x ≤ (L : ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast hL)
    rw [div_le_iff₀ hx0] at h'; linarith
  have hb := bernoulli_real hx0.le L
  have hprod : (1 - x) ^ L * (1 + x) ^ L ≤ 1 := by
    rw [← mul_pow]; apply pow_le_one₀ <;> nlinarith
  have hpos : 0 ≤ (1 - x) ^ L := pow_nonneg (by linarith) L
  have h2 : 2 ≤ (1 + x) ^ L := by linarith
  nlinarith

/-- NO FRESH RANDOMNESS, NO GAIN: if one error block e is reused for all m ≥ 1 repetitions
    (as when re-running the same deterministic rollout), the m observations are identical,
    majority returns the single observation, and its error stays (1 − a)/2. -/
def obsReuse (Y : Bool) (e : List Bool) (m : ℕ) : List Bool := List.replicate m (xor Y (par e))

theorem cnt_true_replicate (b : Bool) : ∀ m : ℕ, cnt true (List.replicate m b) = if b then m else 0
  | 0 => by cases b <;> rfl
  | m + 1 => by
    simp only [List.replicate_succ, cnt, cnt_true_replicate b m]
    cases b <;> simp; omega

theorem maj_replicate {m : ℕ} (hm : 1 ≤ m) (b : Bool) : maj (List.replicate m b) = b := by
  unfold maj
  rw [cnt_true_replicate, List.length_replicate]
  cases b <;> simp <;> omega

theorem reuse_no_gain (ε : ℝ) (L : ℕ) {m : ℕ} (hm : 1 ≤ m) :
    gs (bitvecs L) (fun e => fw ε e * detRule maj (obsReuse false e m)) = (1 - (1 - 2 * ε) ^ L) / 2 := by
  have e1 : ∀ e, fw ε e * detRule maj (obsReuse false e m) = fw ε e - fw ε e * ind (!par e) := by
    intro e
    simp only [obsReuse, detRule, Bool.false_xor, maj_replicate hm]
    cases par e <;> simp [ind]
  rw [gs_congr (fun e _ => e1 e), gs_sub, fw_total]
  have := flip_agree_real ε L
  unfold agree prob at this
  rw [this]; ring

/-- … and no rule does better: with one reused block, for EVERY m and every randomized rule,
    err₀ + err₁ ≥ 1 − a (a = (1 − 2ε)^L ≥ 0).  So for a < 1/2 no number of repetitions of the
    same randomness reaches error ≤ 1/4. -/
theorem reuse_any_rule {ε : ℝ} (hε : ε ≤ 1 / 2) (L m : ℕ) (φ : List Bool → ℝ) (hφ : Rule m φ) :
    1 - (1 - 2 * ε) ^ L ≤ gs (bitvecs L) (fun e => fw ε e * φ (obsReuse false e m)) +
      gs (bitvecs L) (fun e => fw ε e * (1 - φ (obsReuse true e m))) := by
  set u := φ (List.replicate m false)
  set v := φ (List.replicate m true)
  have hu := hφ _ (mem_bitvecs_of_length (List.length_replicate (n := m) (a := false)))
  have hv := hφ _ (mem_bitvecs_of_length (List.length_replicate (n := m) (a := true)))
  set A := gs (bitvecs L) (fun e => fw ε e * ind (!par e)) with hA
  have e0 : ∀ e, fw ε e * φ (obsReuse false e m) = u * (fw ε e * ind (!par e)) + v * (fw ε e - fw ε e * ind (!par e)) := by
    intro e; cases h : par e <;> simp [obsReuse, h, ind, u, v] <;> ring
  have e1 : ∀ e, fw ε e * (1 - φ (obsReuse true e m)) =
      (1 - v) * (fw ε e * ind (!par e)) + (1 - u) * (fw ε e - fw ε e * ind (!par e)) := by
    intro e; cases h : par e <;> simp [obsReuse, h, ind, u, v] <;> ring
  rw [gs_congr (fun e _ => e0 e), gs_congr (fun e _ => e1 e), gs_add, gs_add, gs_mul_left, gs_mul_left,
    gs_mul_left, gs_mul_left, gs_sub, fw_total, ← hA]
  have hag := flip_agree_real ε L
  unfold agree prob at hag
  rw [← hA] at hag
  have ha : 0 ≤ (1 - 2 * ε) ^ L := pow_nonneg (by linarith) L
  nlinarith [mul_nonneg ha (show 0 ≤ u - v + 1 by linarith [hu.1, hv.2])]

theorem reuse_never {ε : ℝ} (hε : ε ≤ 1 / 2) {L : ℕ} (hsmall : (1 - 2 * ε) ^ L < 1 / 2) (m : ℕ)
    (φ : List Bool → ℝ) (hφ : Rule m φ) :
    ¬ (gs (bitvecs L) (fun e => fw ε e * φ (obsReuse false e m)) ≤ 1 / 4 ∧
      gs (bitvecs L) (fun e => fw ε e * (1 - φ (obsReuse true e m))) ≤ 1 / 4) := by
  rintro ⟨h0, h1⟩
  have := reuse_any_rule hε L m φ hφ
  linarith

/-- THE REMARK'S NUMBERS AT ℝ: for ε = 1/100 and L = 50 the bias a = (1 − 2ε)^L satisfies
    0.364 ≤ a ≤ 0.3644 (so the small-bias condition a ≤ 1/2 holds); the explicit count is
    m(a) = ⌈4/a²⌉₊ = 31, so 31 fresh repetitions with majority give both errors ≤ 1/4, and
    1 ≤ mMin a ≤ 31.  (Optimality of 31 is not claimed.) -/
theorem remark_real :
    (0.364 : ℝ) ≤ (1 - 2 * (1 / 100)) ^ 50 ∧ ((1 - 2 * (1 / 100)) ^ 50 : ℝ) ≤ 0.3644 ∧
    mUp ((1 - 2 * (1 / 100)) ^ 50) = 31 ∧ 1 ≤ mMin ((1 - 2 * (1 / 100)) ^ 50) ∧
    mMin ((1 - 2 * (1 / 100)) ^ 50) ≤ 31 := by
  have hb : (0.364 : ℝ) ≤ (1 - 2 * (1 / 100)) ^ 50 ∧ ((1 - 2 * (1 / 100)) ^ 50 : ℝ) ≤ 0.3644 := by norm_num
  have ha0 : (0 : ℝ) < (1 - 2 * (1 / 100)) ^ 50 := by linarith [hb.1]
  have ha1 : ((1 - 2 * (1 / 100)) ^ 50 : ℝ) ≤ 1 / 2 := by linarith [hb.2]
  have h31 : mUp ((1 - 2 * (1 / 100)) ^ 50) = 31 := by
    unfold mUp
    rw [Nat.ceil_eq_iff (by norm_num)]
    constructor <;> norm_num
  obtain ⟨hach, hmin⟩ := mMin_spec ha0 (by linarith)
  have hle := (mMin_bounds ha0 ha1).2.1
  have hne : mMin ((1 - 2 * (1 / 100)) ^ 50) ≠ 0 := fun h => zero_samples_never _ (h ▸ hach)
  exact ⟨hb.1, hb.2, h31, by omega, by rw [h31] at hle; exact hle⟩

/-! ## Axiom checks -/
#print axioms natCast_real
#print axioms inv_real
#print axioms pow_real
#print axioms add_mul_real
#print axioms gs_real
#print axioms two_pOf
#print axioms pOf_bounds
#print axioms chan_law
#print axioms mUp_spec
#print axioms archimedean_step
#print axioms mUp_pos
#print axioms mUp_lt
#print axioms mUp_ge_16
#print axioms majority_succeeds
#print axioms any_rule_needs
#print axioms ach_of_ge
#print axioms ach_exists
#print axioms mMin_spec
#print axioms mMin_bounds
#print axioms mMin_theta
#print axioms mMin_scaled
#print axioms zero_samples_never
#print axioms zero_signal_never
#print axioms err_succ
#print axioms ach_succ
#print axioms ach_mono
#print axioms ach_iff_ge
#print axioms mMin_one
#print axioms flip_law
#print axioms flip_independent
#print axioms flip_agree_real
#print axioms agree_eq_pOf
#print axioms flip_repeated
#print axioms flip_bias_pos
#print axioms flip_samples
#print axioms flipAch_iff
#print axioms flip_mMin
#print axioms flip_exact
#print axioms bernoulli_real
#print axioms eventually_small
#print axioms cnt_true_replicate
#print axioms maj_replicate
#print axioms reuse_no_gain
#print axioms reuse_any_rule
#print axioms reuse_never
#print axioms remark_real

end RealNoise
end NimAudit
