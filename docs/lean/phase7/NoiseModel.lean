import Misc

/- Phase 7, Part B: the independent outcome-flip model of Remark rem:noisy-rollout-decay as
   a genuine finite probability law, and the two-sided order-a^{-2} repetition bound.
   Written by Claude (10 October 2026).  Lean 4.26.0, core/Std only.

   PARAMETER SCOPE.  Everything in the generic section is proved for an arbitrary type R
   carrying Lean core's ordered-field interface
       [Lean.Grind.Field R] [LE R] [LT R] [Std.LawfulOrderLT R] [Std.IsLinearOrder R]
       [Lean.Grind.OrderedRing R],
   i.e. a linearly ordered field.  Core Lean supplies these instances for ℚ, and the
   ℚ-instantiation is checked below and tied to the phase-6 identities Misc.bw_total,
   Misc.bw_sign and Misc.flip_agree.  The real numbers are not available in this core-only
   environment, so instantiation at ℝ (which needs the same five instances, e.g. from
   Mathlib) is NOT checked here.

   B1  fw ε: the product Bernoulli(ε) law on error patterns e ∈ {0,1}^L; nonnegative for
       0 ≤ ε ≤ 1, total mass 1, block factorisation, full product/independence formula
       for coordinate functions, coordinate marginals ε.
   B2  agreement probability: 2·P[Y ⊕ E₁ ⊕ … ⊕ E_L = Y] = 1 + (1 − 2ε)^L; the m-fold law
       of the observations with FRESH independent error blocks is the product channel law
       chanW p Y with p the agreement probability.
   B3  the testing problem: hypotheses Y ∈ {0,1}, m observations from chanW p Y, arbitrary
       randomized rules φ (acceptance probabilities in [0,1]), error probabilities err0,
       err1, the majority rule with ties declared 0.
   B4  upper bound: bias a = 2p − 1, 0 < a ≤ 1, m·a² ≥ 4 ⇒ majority has both errors ≤ 1/4
       (finite second-moment / Chebyshev argument).
   B5  lower bound: 0 < a ≤ 1/2 and both errors ≤ 1/4 for ANY randomized rule ⇒
       32·m·a² ≥ 3 (finite χ²/Cauchy–Schwarz argument plus a Bernoulli-type inequality).
   B6  packaging and the specialisation a = (1 − 2ε)^L.
   Nothing here concerns erroneous game moves, learned heads or training dynamics. -/

namespace NimAudit
namespace Noise

set_option linter.unusedSectionVars false

open Lean.Grind Std Bridge

section Generic

variable {R : Type} [Field R] [LE R] [LT R] [LawfulOrderLT R] [IsLinearOrder R] [OrderedRing R]

attribute [local instance] Semiring.natCast

/-! ## Finite sums over lists -/

/-- Finite sum Σ_{a ∈ l} f a. -/
def gs {α : Type} (l : List α) (f : α → R) : R := l.foldr (fun a s => f a + s) 0

@[simp] theorem gs_nil {α : Type} (f : α → R) : gs [] f = 0 := rfl
@[simp] theorem gs_cons {α : Type} (a : α) (l : List α) (f : α → R) : gs (a :: l) f = f a + gs l f := rfl

theorem gs_append {α : Type} (l m : List α) (f : α → R) : gs (l ++ m) f = gs l f + gs m f := by
  induction l with
  | nil => simp only [List.nil_append, gs_nil]; grind
  | cons a l ih => simp only [List.cons_append, gs_cons, ih]; grind

theorem gs_map {α β : Type} (g : α → β) (l : List α) (f : β → R) : gs (l.map g) f = gs l (fun a => f (g a)) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.map_cons, gs_cons, ih]

theorem gs_congr {α : Type} {l : List α} {f g : α → R} (h : ∀ a ∈ l, f a = g a) : gs l f = gs l g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [gs_cons]
    rw [h a (by simp), ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]

theorem gs_add {α : Type} (l : List α) (f g : α → R) : gs l (fun a => f a + g a) = gs l f + gs l g := by
  induction l with
  | nil => simp only [gs_nil]; grind
  | cons a l ih => simp only [gs_cons, ih]; grind

theorem gs_sub {α : Type} (l : List α) (f g : α → R) : gs l (fun a => f a - g a) = gs l f - gs l g := by
  induction l with
  | nil => simp only [gs_nil]; grind
  | cons a l ih => simp only [gs_cons, ih]; grind

theorem gs_mul_left {α : Type} (l : List α) (c : R) (f : α → R) : gs l (fun a => c * f a) = c * gs l f := by
  induction l with
  | nil => simp only [gs_nil]; grind
  | cons a l ih => simp only [gs_cons, ih]; grind

theorem gs_zero {α : Type} (l : List α) : gs l (fun _ => (0 : R)) = 0 := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [gs_cons, ih]; grind

theorem gs_le {α : Type} {l : List α} {f g : α → R} (h : ∀ a ∈ l, f a ≤ g a) : gs l f ≤ gs l g := by
  induction l with
  | nil => simp only [gs_nil]; grind
  | cons a l ih =>
    simp only [gs_cons]
    have h1 := h a (by simp)
    have h2 := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    grind

theorem gs_nonneg {α : Type} {l : List α} {f : α → R} (h : ∀ a ∈ l, 0 ≤ f a) : 0 ≤ gs l f := by
  have := gs_le (l := l) (f := fun _ => (0 : R)) (g := f) h
  rw [gs_zero] at this; exact this

theorem gs_bitvecs_succ (n : Nat) (f : List Bool → R) :
    gs (bitvecs (n + 1)) f = gs (bitvecs n) (fun v => f (false :: v)) + gs (bitvecs n) (fun v => f (true :: v)) := by
  simp only [bitvecs, gs_append, gs_map]

theorem gs_bitvecs_add (m n : Nat) (f : List Bool → R) :
    gs (bitvecs (m + n)) f = gs (bitvecs m) (fun v => gs (bitvecs n) (fun w => f (v ++ w))) := by
  induction m generalizing f with
  | zero => simp only [Nat.zero_add, bitvecs, gs_cons, gs_nil, List.nil_append]; grind
  | succ m ih =>
    rw [show m + 1 + n = (m + n) + 1 by omega, gs_bitvecs_succ, gs_bitvecs_succ, ih, ih]
    rfl

/-! ## B1. The product Bernoulli(ε) law on error patterns -/

/-- Weight of an error pattern e ∈ {0,1}^L: ∏ (ε if Eᵢ = 1, 1 − ε if Eᵢ = 0). -/
def fw (ε : R) : List Bool → R
  | [] => 1
  | b :: e => (if b then ε else 1 - ε) * fw ε e

/-- NONNEGATIVITY on the domain 0 ≤ ε ≤ 1. -/
theorem fw_nonneg {ε : R} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) : ∀ e, 0 ≤ fw ε e
  | [] => by simp only [fw]; exact OrderedRing.zero_le_one
  | b :: e => by
    simp only [fw]
    apply OrderedRing.mul_nonneg _ (fw_nonneg h0 h1 e)
    cases b
    · simp only [Bool.false_eq_true, if_false]; grind
    · simp only [if_true]; exact h0

/-- NORMALISATION (for every ε). -/
theorem fw_total (ε : R) : ∀ L, gs (bitvecs L) (fw ε) = 1
  | 0 => by simp only [bitvecs, gs_cons, gs_nil, fw]; grind
  | L + 1 => by
    rw [gs_bitvecs_succ]
    simp only [fw, Bool.false_eq_true, if_false, if_true]
    rw [gs_mul_left, gs_mul_left, fw_total ε L]; grind

/-- BLOCK FACTORISATION: the weight of a concatenation is the product of the weights. -/
theorem fw_append (ε : R) : ∀ e f : List Bool, fw ε (e ++ f) = fw ε e * fw ε f
  | [], f => by simp only [List.nil_append, fw]; grind
  | b :: e, f => by simp only [List.cons_append, fw, fw_append ε e f]; grind

/-- Product of coordinate functions: pf f k (e₀ … e_{L−1}) = ∏ f (k+i) eᵢ. -/
def pf (f : Nat → Bool → R) : Nat → List Bool → R
  | _, [] => 1
  | k, b :: e => f k b * pf f (k + 1) e

/-- Product of the coordinate expectations: ∏_{i<L} (ε·f (k+i) 1 + (1−ε)·f (k+i) 0). -/
def pe (ε : R) (f : Nat → Bool → R) : Nat → Nat → R
  | _, 0 => 1
  | k, L + 1 => (ε * f k true + (1 - ε) * f k false) * pe ε f (k + 1) L

/-- INDEPENDENCE (product formula): the expectation of a product of functions of distinct
    coordinates is the product of their expectations.  With indicator functions this is
    P[∀ i, Eᵢ ∈ Aᵢ] = ∏ P[Eᵢ ∈ Aᵢ]: the coordinates are mutually independent. -/
theorem fw_product (ε : R) (f : Nat → Bool → R) : ∀ L k,
    gs (bitvecs L) (fun e => fw ε e * pf f k e) = pe ε f k L
  | 0, k => by simp only [bitvecs, gs_cons, gs_nil, fw, pf, pe]; grind
  | L + 1, k => by
    rw [gs_bitvecs_succ]
    have e0 : ∀ v, fw ε (false :: v) * pf f k (false :: v) = ((1 - ε) * f k false) * (fw ε v * pf f (k + 1) v) := by
      intro v; simp only [fw, pf, Bool.false_eq_true, if_false]; grind
    have e1 : ∀ v, fw ε (true :: v) * pf f k (true :: v) = (ε * f k true) * (fw ε v * pf f (k + 1) v) := by
      intro v; simp only [fw, pf, if_true]; grind
    rw [gs_congr (fun v _ => e0 v), gs_congr (fun v _ => e1 v), gs_mul_left, gs_mul_left, fw_product ε f L (k + 1)]
    simp only [pe]; grind

/-- BLOCK INDEPENDENCE: events on disjoint blocks of coordinates multiply. -/
theorem fw_blocks (ε : R) (m n : Nat) (g h : List Bool → R) :
    gs (bitvecs (m + n)) (fun e => fw ε e * (g (e.take m) * h (e.drop m))) =
      gs (bitvecs m) (fun v => fw ε v * g v) * gs (bitvecs n) (fun w => fw ε w * h w) := by
  rw [gs_bitvecs_add]
  have e1 : ∀ v ∈ bitvecs m, gs (bitvecs n) (fun w => fw ε (v ++ w) * (g ((v ++ w).take m) * h ((v ++ w).drop m))) =
      (fw ε v * g v) * gs (bitvecs n) (fun w => fw ε w * h w) := by
    intro v hv
    have hl := mem_bitvecs_length hv
    rw [← gs_mul_left]
    apply gs_congr; intro w _
    rw [fw_append, List.take_left' hl, List.drop_left' hl]; grind
  rw [gs_congr e1]
  have e2 := gs_mul_left (bitvecs m) (gs (bitvecs n) (fun w => fw ε w * h w)) (fun v => fw ε v * g v)
  rw [show (fun v => fw ε v * g v * gs (bitvecs n) (fun w => fw ε w * h w)) =
      (fun v => gs (bitvecs n) (fun w => fw ε w * h w) * (fw ε v * g v)) by funext v; grind, e2]
  grind

/-- Indicator of a Boolean in R. -/
def ind (b : Bool) : R := if b then 1 else 0

/-- Probability of an event A ⊆ {0,1}^L under the flip law. -/
def prob (ε : R) (L : Nat) (A : List Bool → Bool) : R := gs (bitvecs L) (fun e => fw ε e * ind (A e))

theorem getD_drop' (e : List Bool) (i : Nat) : e.getD i false = (e.drop i).getD 0 false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_drop, Nat.add_zero]

theorem gs_fw_one (ε : R) (i : Nat) : gs (bitvecs i) (fun v => fw ε v * (1 : R)) = 1 := by
  rw [show (fun v => fw ε v * (1 : R)) = fw ε by funext v; grind]; exact fw_total ε i

theorem gs_fw_head (ε : R) (n : Nat) : gs (bitvecs (n + 1)) (fun w => fw ε w * ind (w.getD 0 false)) = ε := by
  rw [gs_bitvecs_succ]
  simp only [fw, ind, List.getD_cons_zero, Bool.false_eq_true, if_false, if_true]
  have h0 : gs (bitvecs n) (fun v => (1 - ε) * fw ε v * (0 : R)) = 0 := by
    rw [show (fun v => (1 - ε) * fw ε v * (0 : R)) = (fun _ => (0 : R)) by funext v; grind, gs_zero]
  have h1 : gs (bitvecs n) (fun v => ε * fw ε v * (1 : R)) = ε * gs (bitvecs n) (fw ε) := by
    rw [← gs_mul_left]; apply gs_congr; intro v _; grind
  rw [h0, h1, fw_total]; grind

/-- COORDINATE MARGINALS: every coordinate is 1 with probability ε. -/
theorem fw_marginal (ε : R) {i L : Nat} (hi : i < L) : prob ε L (fun e => e.getD i false) = ε := by
  obtain ⟨n, rfl⟩ : ∃ n, L = i + (n + 1) := ⟨L - i - 1, by omega⟩
  unfold prob
  have hb := fw_blocks ε i (n + 1) (fun _ => (1 : R)) (fun w => ind (w.getD 0 false))
  simp only at hb
  have e1 : ∀ e : List Bool, fw ε e * ind (e.getD i false) = fw ε e * (1 * ind ((e.drop i).getD 0 false)) := by
    intro e; rw [getD_drop' e i, Semiring.one_mul]
  rw [gs_congr (fun e _ => e1 e), hb, gs_fw_one, gs_fw_head, Semiring.one_mul]

/-! ## B2. The corrupted observation and fresh repetitions -/

/-- ±1 encoding of a bit. -/
def sg (b : Bool) : R := if b then -1 else 1

/-- SIGN IDENTITY: E[(−1)^{E₁ ⊕ … ⊕ E_L}] = (1 − 2ε)^L. -/
theorem fw_sign (ε : R) : ∀ L, gs (bitvecs L) (fun e => fw ε e * sg (par e)) = (1 - 2 * ε) ^ L
  | 0 => by simp only [bitvecs, gs_cons, gs_nil, fw, par, sg, Bool.false_eq_true, if_false]; grind
  | L + 1 => by
    rw [gs_bitvecs_succ]
    have e0 : ∀ v, fw ε (false :: v) * sg (par (false :: v)) = (1 - ε) * (fw ε v * sg (par v)) := by
      intro v; simp only [fw, par, Bool.false_xor, Bool.false_eq_true, if_false]; grind
    have e1 : ∀ v, fw ε (true :: v) * sg (par (true :: v)) = (-ε) * (fw ε v * sg (par v)) := by
      intro v; simp only [fw, par, Bool.true_xor, if_true]; cases par v <;> simp only [sg, Bool.not_false,
        Bool.not_true, Bool.false_eq_true, if_false, if_true] <;> grind
    rw [gs_congr (fun v _ => e0 v), gs_congr (fun v _ => e1 v), gs_mul_left, gs_mul_left, fw_sign ε L,
      Semiring.pow_succ]
    grind

/-- Probability that the observed bit Y ⊕ E₁ ⊕ … ⊕ E_L equals the ideal bit Y. -/
def agree (ε : R) (L : Nat) : R := prob ε L (fun e => !par e)

/-- THE REMARK'S FORMULA: P[Ỹ = Y] = (1 + (1 − 2ε)^L)/2, stated without division. -/
theorem agree_formula (ε : R) (L : Nat) : 2 * agree ε L = 1 + (1 - 2 * ε) ^ L := by
  unfold agree prob
  have h : ∀ e : List Bool, 2 * (fw ε e * ind (!par e)) = fw ε e + fw ε e * sg (par e) := by
    intro e; cases par e <;> simp only [ind, sg, Bool.not_false, Bool.not_true, Bool.false_eq_true,
      if_false, if_true] <;> grind
  rw [← gs_mul_left, gs_congr (fun e _ => h e), gs_add, fw_total, fw_sign]

/-- The observed bit's law given the ideal bit Y. -/
theorem observe_law (ε : R) (L : Nat) (Y b : Bool) :
    prob ε L (fun e => decide (xor Y (par e) = b)) = if b = Y then agree ε L else 1 - agree ε L := by
  unfold agree prob
  by_cases hb : b = Y
  · subst hb; rw [if_pos rfl]; apply gs_congr; intro e _
    simp only; cases b <;> cases par e <;> simp
  · rw [if_neg hb]
    have h : ∀ e : List Bool, fw ε e * ind (decide (xor Y (par e) = b)) = fw ε e - fw ε e * ind (!par e) := by
      intro e
      have hb' : b = !Y := by cases b <;> cases Y <;> simp_all
      subst hb'
      cases Y <;> cases par e <;> simp only [ind, Bool.not_false, Bool.not_true, Bool.false_xor, Bool.true_xor,
        decide_eq_true_eq, decide_eq_false_iff_not, Bool.false_eq_true, if_false, if_true, decide_true,
        decide_false] <;> grind
    rw [gs_congr (fun e _ => h e), gs_sub, fw_total]

theorem one_pow' : ∀ L : Nat, (1 : R) ^ L = 1
  | 0 => Semiring.pow_zero _
  | L + 1 => by rw [Semiring.pow_succ, one_pow' L]; grind

/-- EDGE CASES of the agreement probability. -/
theorem agree_edges (ε : R) (L : Nat) :
    agree ε 0 = 1 ∧ agree (0 : R) L = 1 ∧ (2 * ε = 1 → 0 < L → 2 * agree ε L = 1) := by
  refine ⟨?_, ?_, fun h hL => ?_⟩
  · have := agree_formula ε 0; rw [Semiring.pow_zero] at this; grind
  · have := agree_formula (0 : R) L
    have e : (1 - 2 * (0 : R)) = 1 := by grind
    rw [e, one_pow'] at this
    grind
  · have hf := agree_formula ε L
    have e : 1 - 2 * ε = 0 := by grind
    rw [e] at hf
    obtain ⟨k, rfl⟩ : ∃ k, L = k + 1 := ⟨L - 1, by omega⟩
    rw [Semiring.pow_succ] at hf; grind

/-- The observations of m repetitions, each using its own block of L error bits. -/
def obsOf (Y : Bool) (L : Nat) : Nat → List Bool → List Bool
  | 0, _ => []
  | m + 1, e => xor Y (par (e.take L)) :: obsOf Y L m (e.drop L)

/-- The m-sample symmetric channel law: each sample equals Y with probability p. -/
def chanW (p : R) (Y : Bool) : List Bool → R
  | [] => 1
  | b :: o => (if b = Y then p else 1 - p) * chanW p Y o

theorem ind_and (a b : Bool) : ind (a && b) = (ind a : R) * ind b := by
  cases a <;> cases b <;> simp only [ind, Bool.and_true, Bool.and_false, Bool.true_and, Bool.false_and,
    Bool.false_eq_true, if_false, if_true] <;> grind

/-- REPEATED OBSERVATIONS WITH FRESH ERRORS: the law of the m observations, when the error
    pattern of length m·L has the product law (independent fresh blocks), is the product
    channel law with agreement probability agree ε L. -/
theorem repeated_law (ε : R) (Y : Bool) (L : Nat) : ∀ (m : Nat) (o : List Bool), o.length = m →
    gs (bitvecs (m * L)) (fun e => fw ε e * ind (decide (obsOf Y L m e = o))) = chanW (agree ε L) Y o
  | 0, o, ho => by
    have : o = [] := List.eq_nil_of_length_eq_zero ho
    subst this
    simp only [Nat.zero_mul, bitvecs, gs_cons, gs_nil, fw, obsOf, decide_true, ind, if_true, chanW]; grind
  | m + 1, o, ho => by
    obtain ⟨b, o', rfl⟩ : ∃ b o', o = b :: o' := by
      cases o with
      | nil => simp at ho
      | cons b o' => exact ⟨b, o', rfl⟩
    have ho' : o'.length = m := by simpa using ho
    rw [show (m + 1) * L = L + m * L by rw [Nat.succ_mul, Nat.add_comm]]
    have hb := fw_blocks ε L (m * L) (fun v => ind (decide (xor Y (par v) = b)))
      (fun w => ind (decide (obsOf Y L m w = o')))
    simp only at hb
    have e1 : ∀ e : List Bool, fw ε e * ind (decide (obsOf Y L (m + 1) e = b :: o')) =
        fw ε e * (ind (decide (xor Y (par (e.take L)) = b)) * ind (decide (obsOf Y L m (e.drop L) = o'))) := by
      intro e
      simp only [obsOf, List.cons.injEq]
      rw [← ind_and]; congr 2
      by_cases h1 : (xor Y (par (List.take L e)) = b) <;> by_cases h2 : obsOf Y L m (List.drop L e) = o' <;> simp [h1, h2]
    rw [gs_congr (fun e _ => e1 e), hb, repeated_law ε Y L m o' ho']
    have hq := observe_law ε L Y b
    unfold prob at hq
    rw [hq]; simp only [chanW]

/-! ## B3. The testing problem -/

/-- Number of observations equal to b. -/
def cnt (b : Bool) : List Bool → Nat
  | [] => 0
  | c :: o => (if c = b then 1 else 0) + cnt b o

theorem cnt_add : ∀ o : List Bool, cnt true o + cnt false o = o.length
  | [] => rfl
  | c :: o => by have := cnt_add o; cases c <;> simp only [cnt, List.length_cons] <;> simp <;> omega

/-- A RANDOMIZED decision rule on m observations: φ o ∈ [0,1] is the probability of
    declaring Y = 1.  Deterministic rules are the {0,1}-valued ones (detRule). -/
def Rule (m : Nat) (φ : List Bool → R) : Prop := ∀ o ∈ bitvecs m, 0 ≤ φ o ∧ φ o ≤ 1

def detRule (δ : List Bool → Bool) : List Bool → R := fun o => ind (δ o)

theorem detRule_rule (m : Nat) (δ : List Bool → Bool) : Rule m (detRule (R := R) δ) := by
  intro o _; unfold detRule ind; cases δ o <;> simp only [Bool.false_eq_true, if_false, if_true] <;>
    exact ⟨by grind, by grind⟩

/-- Error under Y = 0 (declaring 1) and under Y = 1 (declaring 0). -/
def err0 (p : R) (m : Nat) (φ : List Bool → R) : R := gs (bitvecs m) (fun o => chanW p false o * φ o)
def err1 (p : R) (m : Nat) (φ : List Bool → R) : R := gs (bitvecs m) (fun o => chanW p true o * (1 - φ o))

/-- THE MAJORITY RULE: declare 1 iff more than half of the m observations are 1; a tie
    (possible for even m) is declared 0. -/
def maj (o : List Bool) : Bool := decide (o.length < 2 * cnt true o)

/-! ## Moments of the channel law -/

def qY (p : R) (Y b : Bool) : R := if b = Y then p else 1 - p

def prodF (f : Bool → R) : List Bool → R
  | [] => 1
  | b :: o => f b * prodF f o

/-- Product formula for the channel law. -/
theorem chan_prod (p : R) (Y : Bool) (f : Bool → R) : ∀ m,
    gs (bitvecs m) (fun o => chanW p Y o * prodF f o) = (qY p Y true * f true + qY p Y false * f false) ^ m
  | 0 => by simp only [bitvecs, gs_cons, gs_nil, chanW, prodF, Semiring.pow_zero]; grind
  | m + 1 => by
    rw [gs_bitvecs_succ]
    have e0 : ∀ v, chanW p Y (false :: v) * prodF f (false :: v) = (qY p Y false * f false) * (chanW p Y v * prodF f v) := by
      intro v; simp only [chanW, prodF, qY]; grind
    have e1 : ∀ v, chanW p Y (true :: v) * prodF f (true :: v) = (qY p Y true * f true) * (chanW p Y v * prodF f v) := by
      intro v; simp only [chanW, prodF, qY]; grind
    rw [gs_congr (fun v _ => e0 v), gs_congr (fun v _ => e1 v), gs_mul_left, gs_mul_left, chan_prod p Y f m,
      Semiring.pow_succ]
    grind

theorem prodF_one : ∀ o : List Bool, prodF (fun _ => (1 : R)) o = 1
  | [] => rfl
  | b :: o => by simp only [prodF, prodF_one o]; grind

/-- NORMALISATION of the channel law (every p). -/
theorem chan_total (p : R) (Y : Bool) (m : Nat) : gs (bitvecs m) (chanW p Y) = 1 := by
  have h := chan_prod p Y (fun _ => 1) m
  rw [show (fun o => chanW p Y o * prodF (fun _ => (1 : R)) o) = chanW p Y by funext o; rw [prodF_one]; grind] at h
  rw [h]
  have : qY p Y true * 1 + qY p Y false * 1 = 1 := by cases Y <;> simp only [qY] <;> simp <;> grind
  rw [this, one_pow']

theorem chan_nonneg {p : R} (h0 : 0 ≤ p) (h1 : p ≤ 1) (Y : Bool) : ∀ o, 0 ≤ chanW p Y o
  | [] => by simp only [chanW]; exact OrderedRing.zero_le_one
  | b :: o => by
    simp only [chanW]
    apply OrderedRing.mul_nonneg _ (chan_nonneg h0 h1 Y o)
    split <;> grind

/-- Centred agreement count D(o) = #{j : oⱼ = Y} − m·p. -/
def dev (p : R) (Y : Bool) (o : List Bool) : R := (cnt Y o : R) - (o.length : R) * p

theorem sum3 {α : Type} (l : List α) (A B C : R) (W y : α → R) :
    gs l (fun v => A * W v + B * (W v * y v) + C * (W v * y v ^ 2)) =
      A * gs l W + B * gs l (fun v => W v * y v) + C * gs l (fun v => W v * y v ^ 2) := by
  rw [gs_add, gs_add, gs_mul_left, gs_mul_left, gs_mul_left]

theorem dev_cons (p : R) (Y b : Bool) (v : List Bool) :
    dev p Y (b :: v) = ((if b = Y then 1 else 0) - p) + dev p Y v := by
  unfold dev; simp only [cnt, List.length_cons]; split <;> grind

/-- FIRST AND SECOND MOMENTS: E[D] = 0 and E[D²] = m·p·(1 − p). -/
theorem chan_moments (p : R) (Y : Bool) : ∀ m,
    gs (bitvecs m) (fun o => chanW p Y o * dev p Y o) = 0 ∧
    gs (bitvecs m) (fun o => chanW p Y o * dev p Y o ^ 2) = (m : R) * p * (1 - p)
  | 0 => by
    simp only [bitvecs, gs_cons, gs_nil, chanW, dev, cnt, List.length_nil]
    constructor <;> grind
  | m + 1 => by
    obtain ⟨ih1, ih2⟩ := chan_moments p Y m
    have ht := chan_total p Y m
    have hv : ∀ v ∈ bitvecs m, v.length = m := fun v hv => mem_bitvecs_length hv
    have br : ∀ b : Bool,
        gs (bitvecs m) (fun v => chanW p Y (b :: v) * dev p Y (b :: v)) =
          qY p Y b * ((if b = Y then 1 else 0) - p) ∧
        gs (bitvecs m) (fun v => chanW p Y (b :: v) * dev p Y (b :: v) ^ 2) =
          qY p Y b * (((if b = Y then 1 else 0) - p) ^ 2 + (m : R) * p * (1 - p)) := by
      intro b
      have hc : ∀ v, chanW p Y (b :: v) = qY p Y b * chanW p Y v := fun v => rfl
      generalize hx : ((if b = Y then 1 else 0) - p : R) = x
      have hd : ∀ v, dev p Y (b :: v) = x + dev p Y v := fun v => by rw [dev_cons, hx]
      generalize qY p Y b = q at hc
      constructor
      · have e : ∀ v, chanW p Y (b :: v) * dev p Y (b :: v) =
            (q * x) * chanW p Y v + q * (chanW p Y v * dev p Y v) + 0 * (chanW p Y v * dev p Y v ^ 2) := by
          intro v; rw [hc, hd]; grind
        rw [gs_congr (fun v _ => e v), sum3, ht, ih1, ih2]; grind
      · have e : ∀ v, chanW p Y (b :: v) * dev p Y (b :: v) ^ 2 =
            (q * x ^ 2) * chanW p Y v + (2 * q * x) * (chanW p Y v * dev p Y v) + q * (chanW p Y v * dev p Y v ^ 2) := by
          intro v; rw [hc, hd]; grind
        rw [gs_congr (fun v _ => e v), sum3, ht, ih1, ih2]; grind
    obtain ⟨f0, s0⟩ := br false
    obtain ⟨f1, s1⟩ := br true
    rw [gs_bitvecs_succ, gs_bitvecs_succ, f0, f1, s0, s1]
    cases Y <;> simp only [qY, Bool.false_eq_true, Bool.true_eq_false, if_false, if_true] <;> constructor <;> grind

/-! ## B4. Upper bound for the majority rule (finite Chebyshev) -/

theorem sq_le_sq' {x y : R} (h0 : 0 ≤ x) (h : x ≤ y) : x ^ 2 ≤ y ^ 2 := by
  have h1 : x * x ≤ x * y := OrderedRing.mul_le_mul_of_nonneg_left h h0
  have h2 : x * y ≤ y * y := OrderedRing.mul_le_mul_of_nonneg_right h (by grind)
  have e1 : x ^ 2 = x * x := by grind
  have e2 : y ^ 2 = y * y := by grind
  rw [e1, e2]; grind

/-- Pointwise Chebyshev: on the event 2·#agreements ≤ m the centred count is at least m·a/2
    in absolute value. -/
theorem cheb_point {p a : R} (hap : 2 * p = 1 + a) (ha : 0 ≤ a) (Y : Bool) (o : List Bool) :
    ind (decide (2 * cnt Y o ≤ o.length)) * ((o.length : R) * a) ^ 2 ≤ 4 * dev p Y o ^ 2 := by
  unfold ind dev
  by_cases h : 2 * cnt Y o ≤ o.length
  · rw [_root_.decide_eq_true h, if_pos rfl]
    have hc : 2 * (cnt Y o : R) ≤ (o.length : R) := by
      have := OrderedRing.natCast_le_natCast_of_le (R := R) _ _ h; grind
    have hm : (0 : R) ≤ (o.length : R) * a := OrderedRing.mul_nonneg (by
      have := OrderedRing.natCast_le_natCast_of_le (R := R) 0 o.length (Nat.zero_le _); grind) ha
    have hmp : (o.length : R) * (2 * p) = (o.length : R) * (1 + a) := by rw [hap]
    have key : (o.length : R) * a ≤ 2 * ((o.length : R) * p - (cnt Y o : R)) := by grind
    have := sq_le_sq' hm key
    grind
  · rw [_root_.decide_eq_false h, if_neg (by simp)]
    have : (0 : R) ≤ ((cnt Y o : R) - (o.length : R) * p) ^ 2 := OrderedRing.sq_nonneg
    grind

/-- CHEBYSHEV: P_Y[2·#agreements ≤ m] · (m a)² ≤ 4 m p (1 − p). -/
theorem cheb (p a : R) (hap : 2 * p = 1 + a) (ha : 0 ≤ a) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (Y : Bool) (m : Nat) :
    gs (bitvecs m) (fun o => chanW p Y o * ind (decide (2 * cnt Y o ≤ m))) * ((m : R) * a) ^ 2 ≤
      4 * ((m : R) * p * (1 - p)) := by
  rw [← (chan_moments p Y m).2, ← gs_mul_left]
  have e : gs (bitvecs m) (fun o => chanW p Y o * ind (decide (2 * cnt Y o ≤ m))) * ((m : R) * a) ^ 2 =
      gs (bitvecs m) (fun o => chanW p Y o * (ind (decide (2 * cnt Y o ≤ o.length)) * ((o.length : R) * a) ^ 2)) := by
    rw [show gs (bitvecs m) (fun o => chanW p Y o * ind (decide (2 * cnt Y o ≤ m))) * ((m : R) * a) ^ 2 =
        ((m : R) * a) ^ 2 * gs (bitvecs m) (fun o => chanW p Y o * ind (decide (2 * cnt Y o ≤ m))) by grind,
      ← gs_mul_left]
    apply gs_congr; intro o ho; rw [mem_bitvecs_length ho]; grind
  rw [e]
  apply gs_le; intro o _
  have hw := chan_nonneg hp0 hp1 Y o
  have := OrderedRing.mul_le_mul_of_nonneg_left (cheb_point hap ha Y o) hw
  grind

theorem nat_cast_nonneg' (n : Nat) : (0 : R) ≤ (n : R) := by
  have := OrderedRing.natCast_le_natCast_of_le (R := R) 0 n (Nat.zero_le _); grind

/-- From the Chebyshev bound to error ≤ 1/4 once m·a² ≥ 4. -/
theorem quarter_of_cheb {p a E : R} {m : Nat} (hap : 2 * p = 1 + a) (hE : 0 ≤ E)
    (hc : E * ((m : R) * a) ^ 2 ≤ 4 * ((m : R) * p * (1 - p))) (hm : 4 ≤ (m : R) * a ^ 2) : 4 * E ≤ 1 := by
  have hm0 := nat_cast_nonneg' (R := R) m
  have hEm : 0 ≤ E * (m : R) := OrderedRing.mul_nonneg hE hm0
  have h1 : E * (m : R) * 4 ≤ E * (m : R) * ((m : R) * a ^ 2) := OrderedRing.mul_le_mul_of_nonneg_left hm hEm
  have h2 : 4 * ((m : R) * p * (1 - p)) = (m : R) * (1 - a ^ 2) := by
    have : 4 * (p * (1 - p)) = 1 - a ^ 2 := by
      have e : 4 * (p * (1 - p)) = (2 * p) * (2 - 2 * p) := by grind
      rw [e, hap]; grind
    grind
  have h3 : (m : R) * (1 - a ^ 2) ≤ (m : R) := by
    have : 0 ≤ (m : R) * a ^ 2 := OrderedRing.mul_nonneg hm0 OrderedRing.sq_nonneg
    grind
  have hpos : (0 : R) < (m : R) := by
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h; exfalso
      have : ((0 : Nat) : R) = 0 := by grind
      rw [this] at hm; grind
    · have := OrderedRing.natCast_le_natCast_of_le (R := R) 1 m h; grind
  have h4 : (4 * E) * (m : R) ≤ 1 * (m : R) := by grind
  exact (Field.IsOrdered.mul_le_mul_iff_of_pos_right hpos).1 h4

/-- B4. UPPER BOUND (constructive): for bias 0 < a ≤ 1 (p = (1 + a)/2) and every m with
    m·a² ≥ 4, the majority rule (ties declared 0) has error at most 1/4 under BOTH
    hypotheses. -/
theorem maj_upper (p a : R) (hap : 2 * p = 1 + a) (ha0 : 0 < a) (ha1 : a ≤ 1) (m : Nat)
    (hm : 4 ≤ (m : R) * a ^ 2) :
    4 * err0 p m (detRule maj) ≤ 1 ∧ 4 * err1 p m (detRule maj) ≤ 1 := by
  have hp0 : 0 ≤ p := by grind
  have hp1 : p ≤ 1 := by grind
  constructor
  · have hle : err0 p m (detRule maj) ≤ gs (bitvecs m) (fun o => chanW p false o * ind (decide (2 * cnt false o ≤ m))) := by
      apply gs_le; intro o ho
      have hl := mem_bitvecs_length ho
      apply OrderedRing.mul_le_mul_of_nonneg_left _ (chan_nonneg hp0 hp1 false o)
      unfold detRule maj ind
      have hc := cnt_add o
      by_cases h : o.length < 2 * cnt true o
      · rw [_root_.decide_eq_true h, if_pos rfl, _root_.decide_eq_true (by omega), if_pos rfl]; grind
      · rw [_root_.decide_eq_false h, if_neg (by simp)]; split <;> grind
    have hE := gs_nonneg (l := bitvecs m) (f := fun o => chanW p false o * ind (decide (2 * cnt false o ≤ m)))
      (fun o _ => OrderedRing.mul_nonneg (chan_nonneg hp0 hp1 false o) (by unfold ind; split <;> grind))
    have := quarter_of_cheb hap hE (cheb p a hap (by grind) hp0 hp1 false m) hm
    grind
  · have he : err1 p m (detRule maj) = gs (bitvecs m) (fun o => chanW p true o * ind (decide (2 * cnt true o ≤ m))) := by
      apply gs_congr; intro o ho
      have hl := mem_bitvecs_length ho
      unfold detRule maj ind
      by_cases h : o.length < 2 * cnt true o
      · rw [_root_.decide_eq_true h, if_pos rfl, _root_.decide_eq_false (by omega), if_neg (by simp)]; grind
      · rw [_root_.decide_eq_false h, if_neg (by simp), _root_.decide_eq_true (by omega), if_pos rfl]; grind
    have hE := gs_nonneg (l := bitvecs m) (f := fun o => chanW p true o * ind (decide (2 * cnt true o ≤ m)))
      (fun o _ => OrderedRing.mul_nonneg (chan_nonneg hp0 hp1 true o) (by unfold ind; split <;> grind))
    rw [he]
    exact quarter_of_cheb hap hE (cheb p a hap (by grind) hp0 hp1 true m) hm

/-! ## B5. Lower bound for arbitrary randomized rules (finite χ² argument) -/

/-- Per-observation likelihood ratio P₁(b)/P₀(b) (P₀ = law under Y = 0, P₁ under Y = 1). -/
def rr (p : R) (b : Bool) : R := if b then p * (1 - p)⁻¹ else (1 - p) * p⁻¹

/-- The single-observation χ² factor: Σ_b P₁(b)²/P₀(b). -/
def chiG (p : R) : R := p * (p * (1 - p)⁻¹) + (1 - p) * ((1 - p) * p⁻¹)

theorem lr_mul {p : R} (hp : p * p⁻¹ = 1) (hq : (1 - p) * (1 - p)⁻¹ = 1) :
    ∀ o, chanW p false o * prodF (rr p) o = chanW p true o
  | [] => by simp only [chanW, prodF]; grind
  | b :: o => by
    have ih := lr_mul hp hq o
    simp only [chanW, prodF]
    generalize chanW p false o = W0 at ih ⊢
    generalize prodF (rr p) o = Lr at ih ⊢
    generalize chanW p true o = W1 at ih ⊢
    subst ih
    cases b
    · simp only [rr, Bool.false_eq_true, if_false, if_true]
      have : p * W0 * ((1 - p) * p⁻¹ * Lr) = (p * p⁻¹) * ((1 - p) * (W0 * Lr)) := by grind
      rw [this, hp]; grind
    · simp only [rr, Bool.true_eq_false, if_false, if_true]
      have : (1 - p) * W0 * (p * (1 - p)⁻¹ * Lr) = ((1 - p) * (1 - p)⁻¹) * (p * (W0 * Lr)) := by grind
      rw [this, hq]; grind

/-- Σ_o P₀(o)·LR(o)² = G^m (the χ² identity for the product law). -/
theorem chi_identity {p : R} (hp : p * p⁻¹ = 1) (hq : (1 - p) * (1 - p)⁻¹ = 1) (m : Nat) :
    gs (bitvecs m) (fun o => chanW p false o * prodF (rr p) o ^ 2) = chiG p ^ m := by
  have e : ∀ o, chanW p false o * prodF (rr p) o ^ 2 = chanW p true o * prodF (rr p) o := by
    intro o; rw [← lr_mul hp hq o]; grind
  rw [gs_congr (fun o _ => e o), chan_prod]
  simp only [qY, rr, chiG, if_true, Bool.false_eq_true, Bool.true_eq_false, if_false]

/-- The χ² factor in terms of the bias: (G − 1)(1 − a²) = 4a². -/
theorem chiG_bias {p a : R} (hap : 2 * p = 1 + a) (hp : p * p⁻¹ = 1) (hq : (1 - p) * (1 - p)⁻¹ = 1) :
    (chiG p - 1) * (1 - a ^ 2) = 4 * a ^ 2 := by
  have hG : chiG p * (p * (1 - p)) = p ^ 3 + (1 - p) ^ 3 := by
    unfold chiG
    have e : (p * (p * (1 - p)⁻¹) + (1 - p) * ((1 - p) * p⁻¹)) * (p * (1 - p)) =
        p ^ 3 * ((1 - p) * (1 - p)⁻¹) + (1 - p) ^ 3 * (p * p⁻¹) := by grind
    rw [e, hp, hq]; grind
  have h4 : 4 * (p * (1 - p)) = 1 - a ^ 2 := by
    have e : 4 * (p * (1 - p)) = (2 * p) * (2 - 2 * p) := by grind
    rw [e, hap]; grind
  have e2 : (chiG p - 1) * (1 - a ^ 2) = 4 * (chiG p * (p * (1 - p))) - 4 * (p * (1 - p)) := by rw [← h4]; grind
  rw [e2, hG]
  have e3 : p ^ 3 + (1 - p) ^ 3 = 1 - 3 * (p * (1 - p)) := by grind
  rw [e3]; grind

/-- A Bernoulli-type inequality: (1 + x)^m (1 − m x) ≤ 1 for x ≥ 0. -/
theorem bernoulli_le (x : R) (hx : 0 ≤ x) : ∀ m : Nat, (1 + x) ^ m * (1 - (m : R) * x) ≤ 1
  | 0 => by rw [Semiring.pow_zero]; grind
  | m + 1 => by
    have ih := bernoulli_le x hx m
    have hpow : 0 ≤ (1 + x) ^ m := by
      clear ih
      induction m with
      | zero => rw [Semiring.pow_zero]; exact OrderedRing.zero_le_one
      | succ k ihk => rw [Semiring.pow_succ]; exact OrderedRing.mul_nonneg ihk (by grind)
    have hm := nat_cast_nonneg' (R := R) m
    have h2 : 0 ≤ (1 + x) ^ m * (((m : R) + 1) * x ^ 2) :=
      OrderedRing.mul_nonneg hpow (OrderedRing.mul_nonneg (by grind) OrderedRing.sq_nonneg)
    have e : (1 + x) ^ (m + 1) * (1 - ((m + 1 : Nat) : R) * x) =
        (1 + x) ^ m * (1 - (m : R) * x) - (1 + x) ^ m * (((m : R) + 1) * x ^ 2) := by
      rw [Semiring.pow_succ]; grind
    rw [e]; grind

/-- The quadratic (Cauchy–Schwarz) step: Σ P₀ (LR − 1)² ≥ (Σ (P₁ − P₀)(2φ − 1))² whenever
    0 ≤ φ ≤ 1. -/
theorem sum3' {α : Type} (l : List α) (A B C : R) (f g h : α → R) :
    gs l (fun v => A * f v + B * g v + C * h v) = A * gs l f + B * gs l g + C * gs l h := by
  rw [gs_add, gs_add, gs_mul_left, gs_mul_left, gs_mul_left]

/-- Sum of the two errors of any rule: err₀ + err₁ = 1 − Σ (P₁ − P₀) φ. -/
theorem err_sum (p : R) (m : Nat) (φ : List Bool → R) :
    err0 p m φ + err1 p m φ = 1 - gs (bitvecs m) (fun o => (chanW p true o - chanW p false o) * φ o) := by
  unfold err0 err1
  have e : ∀ o, chanW p true o * (1 - φ o) = chanW p true o - chanW p true o * φ o := fun o => by grind
  have e2 : ∀ o, (chanW p true o - chanW p false o) * φ o = chanW p true o * φ o - chanW p false o * φ o :=
    fun o => by grind
  rw [gs_congr (fun o _ => e o), gs_congr (fun o _ => e2 o), gs_sub, gs_sub, chan_total]; grind

theorem sq_unit {φ : R} (hl : 0 ≤ φ) (hu : φ ≤ 1) : (2 * φ - 1) ^ 2 ≤ 1 := by
  have : 0 ≤ (1 - (2 * φ - 1)) * (1 + (2 * φ - 1)) := OrderedRing.mul_nonneg (by grind) (by grind)
  grind

theorem final_arith (A D G : R) (hq0 : 0 ≤ D ^ 2 * A + (-2 * D) * D + 1 * (G - 1)) (hA : D ^ 2 * A ≤ D ^ 2 * 1)
    (h1 : 1 ≤ D ^ 2) : 2 ≤ G := by grind

/-- B5 core: if both errors are at most 1/4 then G^m ≥ 2. -/
theorem chi_ge_two {p : R} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hp : p * p⁻¹ = 1) (hq : (1 - p) * (1 - p)⁻¹ = 1)
    (m : Nat) (φ : List Bool → R) (hφ : Rule m φ) (h0 : 4 * err0 p m φ ≤ 1) (h1 : 4 * err1 p m φ ≤ 1) :
    2 ≤ chiG p ^ m := by
  -- Δ := Σ (P₁ − P₀) φ ≥ 1/2
  have hs := err_sum p m φ
  generalize hΔ : gs (bitvecs m) (fun o => (chanW p true o - chanW p false o) * φ o) = Δ at hs
  have hΔ2 : 1 ≤ 2 * Δ := by grind
  -- the quadratic form at t = 2Δ
  let P0 := chanW p false
  let LR := prodF (rr p)
  have hlr : ∀ o, P0 o * LR o = chanW p true o := lr_mul hp hq
  have hq0 : 0 ≤ gs (bitvecs m) (fun o => P0 o * ((2 * Δ) * (2 * φ o - 1) - (LR o - 1)) ^ 2) :=
    gs_nonneg (fun o _ => OrderedRing.mul_nonneg (chan_nonneg hp0 hp1 false o) OrderedRing.sq_nonneg)
  have expand : ∀ o, P0 o * ((2 * Δ) * (2 * φ o - 1) - (LR o - 1)) ^ 2 =
      (2 * Δ) ^ 2 * (P0 o * (2 * φ o - 1) ^ 2) + (-2 * (2 * Δ)) * ((2 * φ o - 1) * (chanW p true o - P0 o)) +
        1 * (P0 o * LR o ^ 2 - 2 * chanW p true o + P0 o) := by
    intro o; rw [← hlr o]; grind
  rw [gs_congr (fun o _ => expand o), sum3'] at hq0
  -- A = Σ P₀ (2φ − 1)² ≤ 1
  have hA : gs (bitvecs m) (fun o => P0 o * (2 * φ o - 1) ^ 2) ≤ 1 := by
    have h := gs_le (l := bitvecs m) (f := fun o => P0 o * (2 * φ o - 1) ^ 2) (g := chanW p false) (by
      intro o ho
      obtain ⟨hl, hu⟩ := hφ o ho
      have hw : (2 * φ o - 1) ^ 2 ≤ 1 := sq_unit hl hu
      have := OrderedRing.mul_le_mul_of_nonneg_left hw (chan_nonneg hp0 hp1 false o)
      simp only [P0]; grind)
    rw [chan_total] at h; exact h
  -- B = Σ (2φ − 1)(P₁ − P₀) = 2Δ
  have hB : gs (bitvecs m) (fun o => (2 * φ o - 1) * (chanW p true o - P0 o)) = 2 * Δ := by
    have e : ∀ o, (2 * φ o - 1) * (chanW p true o - P0 o) =
        2 * ((chanW p true o - chanW p false o) * φ o) - (chanW p true o - chanW p false o) := by
      intro o; simp only [P0]; grind
    rw [gs_congr (fun o _ => e o), gs_sub, gs_mul_left, hΔ, gs_sub, chan_total, chan_total]; grind
  -- C = G^m − 1
  have hC : gs (bitvecs m) (fun o => P0 o * LR o ^ 2 - 2 * chanW p true o + P0 o) = chiG p ^ m - 1 := by
    rw [gs_add, gs_sub, gs_mul_left, chi_identity hp hq, chan_total, chan_total]; grind
  rw [hB, hC] at hq0
  have hsq : 0 ≤ (2 * Δ) ^ 2 := OrderedRing.sq_nonneg
  have hAm := OrderedRing.mul_le_mul_of_nonneg_left hA hsq
  have h1' : (1 : R) ≤ (2 * Δ) ^ 2 := by
    have := sq_le_sq' (by grind : (0 : R) ≤ 1) hΔ2; grind
  exact final_arith _ _ _ hq0 hAm h1'

/-- From G^m ≥ 2 and (G − 1)(1 − a²) = 4a² to 8·m·a² ≥ 1 − a². -/
theorem samples_from_chi {a x : R} {m : Nat} (hx : x * (1 - a ^ 2) = 4 * a ^ 2) (ha : a ^ 2 < 1)
    (hG : 2 ≤ (1 + x) ^ m) : 1 - a ^ 2 ≤ 8 * ((m : R) * a ^ 2) := by
  have hpos : 0 < 1 - a ^ 2 := by grind
  have hx0 : 0 ≤ x := by
    rcases IsLinearPreorder.le_total 0 x with h | h
    · exact h
    · by_cases hz : x = 0
      · grind
      · have hneg : x < 0 := by grind
        have := OrderedRing.mul_neg_of_neg_of_pos hneg hpos
        have : 0 ≤ a ^ 2 := OrderedRing.sq_nonneg
        grind
  have hb := bernoulli_le x hx0 m
  have h2 : 1 ≤ 2 * ((m : R) * x) := by
    rcases IsLinearPreorder.le_total (1 - (m : R) * x) 0 with h | h
    · grind
    · have := OrderedRing.mul_le_mul_of_nonneg_right hG h
      grind
  have e : (2 * ((m : R) * x)) * (1 - a ^ 2) = 8 * ((m : R) * a ^ 2) := by
    rw [show (2 * ((m : R) * x)) * (1 - a ^ 2) = 2 * (m : R) * (x * (1 - a ^ 2)) by grind, hx]; grind
  have h3 := OrderedRing.mul_le_mul_of_nonneg_right h2 (Preorder.le_of_lt hpos)
  grind

/-- B5 (general bias 0 < a < 1): any rule with both errors ≤ 1/4 needs 8·m·a² ≥ 1 − a². -/
theorem lower_bound_general (p a : R) (hap : 2 * p = 1 + a) (ha0 : 0 < a) (ha1 : a < 1) (m : Nat)
    (φ : List Bool → R) (hφ : Rule m φ) (h0 : 4 * err0 p m φ ≤ 1) (h1 : 4 * err1 p m φ ≤ 1) :
    1 - a ^ 2 ≤ 8 * ((m : R) * a ^ 2) := by
  have hp0 : 0 ≤ p := by grind
  have hp1 : p ≤ 1 := by grind
  have hpne : p ≠ 0 := by intro h; rw [h] at hap; grind
  have hqne : 1 - p ≠ 0 := by intro h; grind
  have hp : p * p⁻¹ = 1 := Field.mul_inv_cancel hpne
  have hq : (1 - p) * (1 - p)⁻¹ = 1 := Field.mul_inv_cancel hqne
  have hG := chi_ge_two hp0 hp1 hp hq m φ hφ h0 h1
  have hx := chiG_bias hap hp hq
  have ha2 : a ^ 2 < 1 := by
    have : a * a < 1 * 1 := by
      have h1' : a * a < a * 1 := OrderedRing.mul_lt_mul_of_pos_left ha1 ha0
      grind
    grind
  have hG' : 2 ≤ (1 + (chiG p - 1)) ^ m := by rw [show 1 + (chiG p - 1) = chiG p by grind]; exact hG
  exact samples_from_chi hx ha2 hG'

/-- B5. LOWER BOUND for ARBITRARY (randomized, hence also deterministic) rules: with bias
    0 < a ≤ 1/2, if both error probabilities are at most 1/4 then 32·m·a² ≥ 3. -/
theorem lower_bound (p a : R) (hap : 2 * p = 1 + a) (ha0 : 0 < a) (ha1 : 2 * a ≤ 1) (m : Nat)
    (φ : List Bool → R) (hφ : Rule m φ) (h0 : 4 * err0 p m φ ≤ 1) (h1 : 4 * err1 p m φ ≤ 1) :
    3 ≤ 32 * ((m : R) * a ^ 2) := by
  have h := lower_bound_general p a hap ha0 (by grind) m φ hφ h0 h1
  have h4 : 4 * a ^ 2 ≤ 1 := by
    have := sq_le_sq' (by grind : (0 : R) ≤ 2 * a) ha1
    grind
  grind

/-! ## B3 edge cases -/

/-- NO SIGNAL (a = 0, e.g. ε = 1/2 with L > 0): the two hypotheses give the same law, so
    every rule has err₀ + err₁ = 1 and worst-case error at least 1/2. -/
theorem no_signal (p : R) (hp : 2 * p = 1) (m : Nat) (φ : List Bool → R) :
    err0 p m φ + err1 p m φ = 1 := by
  have e : ∀ o, chanW p true o = chanW p false o := by
    intro o; induction o with
    | nil => rfl
    | cons b o ih =>
      simp only [chanW, ih]
      have : 1 - p = p := by grind
      cases b <;> simp only [Bool.false_eq_true, Bool.true_eq_false, if_true, if_false, this]
  rw [err_sum]
  have : gs (bitvecs m) (fun o => (chanW p true o - chanW p false o) * φ o) = 0 := by
    rw [show (fun o => (chanW p true o - chanW p false o) * φ o) = (fun _ => (0 : R)) by
      funext o; rw [e o]; grind, gs_zero]
  rw [this]; grind

/-- EXACT OBSERVATIONS (a = 1, e.g. ε = 0 or L = 0): one sample and the identity rule give
    zero error under both hypotheses. -/
theorem exact_channel : err0 (1 : R) 1 (fun o => ind (o.getD 0 false)) = 0 ∧
    err1 (1 : R) 1 (fun o => ind (o.getD 0 false)) = 0 := by
  simp only [err0, err1, bitvecs, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    gs_cons, gs_nil, chanW, ind, List.getD_cons_zero, Bool.false_eq_true, Bool.true_eq_false, if_true, if_false]
  constructor <;> grind

/-! ## B6. Packaging: the precise meaning of "order a^{-2} repetitions" -/

/-- m samples suffice for worst-case error ≤ 1/4 (some randomized rule achieves it). -/
def Achievable (p : R) (m : Nat) : Prop :=
  ∃ φ : List Bool → R, Rule m φ ∧ 4 * err0 p m φ ≤ 1 ∧ 4 * err1 p m φ ≤ 1

/-- ORDER a^{-2}, TWO-SIDED: for bias 0 < a ≤ 1/2,
      m·a² ≥ 4  ⇒  achievable (by the majority rule), and
      achievable (by ANY randomized rule) ⇒ 32·m·a² ≥ 3.
    So the least sufficient m lies between 3/(32a²) and the least m with m·a² ≥ 4. -/
theorem order_inv_sq (p a : R) (hap : 2 * p = 1 + a) (ha0 : 0 < a) (ha1 : 2 * a ≤ 1) :
    (∀ m : Nat, 4 ≤ (m : R) * a ^ 2 → Achievable p m) ∧
    (∀ m : Nat, Achievable p m → 3 ≤ 32 * ((m : R) * a ^ 2)) := by
  refine ⟨fun m hm => ⟨detRule maj, detRule_rule m maj, maj_upper p a hap ha0 (by grind) m hm⟩,
    fun m ⟨φ, hφ, h0, h1⟩ => lower_bound p a hap ha0 ha1 m φ hφ h0 h1⟩

/-! ## Errors computed on the underlying error space (fresh repetitions) -/

theorem gs_comm {α β : Type} (l : List α) (k : List β) (f : α → β → R) :
    gs l (fun a => gs k (fun b => f a b)) = gs k (fun b => gs l (fun a => f a b)) := by
  induction l with
  | nil => simp only [gs_nil]; rw [gs_zero]
  | cons a l ih => simp only [gs_cons]; rw [ih, ← gs_add]

theorem gs_point : ∀ (m : Nat) (x : List Bool), x.length = m → ∀ g : List Bool → R,
    gs (bitvecs m) (fun o => ind (decide (x = o)) * g o) = g x
  | 0, x, hx, g => by
    have : x = [] := List.eq_nil_of_length_eq_zero hx
    subst this; simp only [bitvecs, gs_cons, gs_nil, decide_true, ind, if_true]; grind
  | m + 1, x, hx, g => by
    obtain ⟨b, x', rfl⟩ : ∃ b x', x = b :: x' := by
      cases x with
      | nil => simp at hx
      | cons b x' => exact ⟨b, x', rfl⟩
    have hx' : x'.length = m := by simpa using hx
    rw [gs_bitvecs_succ]
    have hf : ∀ c v, ind (decide (b :: x' = c :: v)) * g (c :: v) =
        (if b = c then 1 else 0) * (ind (decide (x' = v)) * g (c :: v)) := by
      intro c v
      by_cases hbc : b = c <;> by_cases hxv : x' = v <;> simp only [hbc, hxv, List.cons.injEq, and_self,
        and_true, true_and, and_false, false_and, decide_true, decide_false, ind, if_true, if_false,
        Bool.false_eq_true] <;> grind
    rw [gs_congr (fun v _ => hf false v), gs_congr (fun v _ => hf true v), gs_mul_left, gs_mul_left,
      gs_point m x' hx' (fun o => g (false :: o)), gs_point m x' hx' (fun o => g (true :: o))]
    cases b <;> simp only [Bool.false_eq_true, Bool.true_eq_false, if_true, if_false] <;> grind

theorem obsOf_length (Y : Bool) (L : Nat) : ∀ m e, (obsOf Y L m e).length = m
  | 0, _ => rfl
  | m + 1, e => by simp [obsOf, obsOf_length Y L m]

/-- TRANSFER TO THE ERROR SPACE: averaging a function of the m observations over the
    fresh-error law equals averaging it over the channel law chanW (agree ε L) Y. -/
theorem rep_expect (ε : R) (Y : Bool) (L m : Nat) (g : List Bool → R) :
    gs (bitvecs (m * L)) (fun e => fw ε e * g (obsOf Y L m e)) =
      gs (bitvecs m) (fun o => chanW (agree ε L) Y o * g o) := by
  have e1 : ∀ e, fw ε e * g (obsOf Y L m e) =
      gs (bitvecs m) (fun o => (fw ε e * ind (decide (obsOf Y L m e = o))) * g o) := by
    intro e
    rw [← gs_point m (obsOf Y L m e) (obsOf_length Y L m e) g, ← gs_mul_left]
    apply gs_congr; intro o _; grind
  rw [gs_congr (fun e _ => e1 e), gs_comm]
  apply gs_congr; intro o ho
  have := repeated_law ε Y L m o (mem_bitvecs_length ho)
  rw [show (fun e => fw ε e * ind (decide (obsOf Y L m e = o)) * g o) =
      (fun e => g o * (fw ε e * ind (decide (obsOf Y L m e = o)))) by funext e; grind, gs_mul_left, this]
  grind

/-- B6, SPECIALISED to the flip model: a = (1 − 2ε)^L, p = P[Ỹ = Y].  If 0 ≤ ε, 2ε < 1
    and (1 − 2ε)^L ≤ 1/2, then for m fresh repetitions (error space of m·L independent
    flips): m·a² ≥ 4 suffices (majority), and any randomized rule with both errors ≤ 1/4
    needs 32·m·a² ≥ 3.  Errors are computed directly on the error space.  (0 ≤ ε is not
    needed as a hypothesis: the regime condition 2a ≤ 1 with a > 0 is what is used; the
    error law is a probability law when 0 ≤ ε ≤ 1, fw_nonneg.) -/
theorem flip_order_inv_sq (ε : R) (L : Nat) (hε1 : 2 * ε < 1)
    (hsmall : 2 * (1 - 2 * ε) ^ L ≤ 1) :
    (∀ m : Nat, 4 ≤ (m : R) * ((1 - 2 * ε) ^ L) ^ 2 →
      4 * gs (bitvecs (m * L)) (fun e => fw ε e * detRule maj (obsOf false L m e)) ≤ 1 ∧
      4 * gs (bitvecs (m * L)) (fun e => fw ε e * (1 - detRule maj (obsOf true L m e))) ≤ 1) ∧
    (∀ (m : Nat) (φ : List Bool → R), Rule m φ →
      4 * gs (bitvecs (m * L)) (fun e => fw ε e * φ (obsOf false L m e)) ≤ 1 →
      4 * gs (bitvecs (m * L)) (fun e => fw ε e * (1 - φ (obsOf true L m e))) ≤ 1 →
      3 ≤ 32 * ((m : R) * ((1 - 2 * ε) ^ L) ^ 2)) := by
  have hap := agree_formula ε L
  have ha0 : 0 < (1 - 2 * ε) ^ L := by
    have hb : 0 < 1 - 2 * ε := by grind
    clear hsmall hap
    induction L with
    | zero => rw [Semiring.pow_zero]; exact OrderedRing.zero_lt_one
    | succ L ih => rw [Semiring.pow_succ]; exact OrderedRing.mul_pos ih hb
  have hle1 : (1 - 2 * ε) ^ L ≤ 1 := by
    have h1 := hsmall; have h2 := ha0
    generalize (1 - 2 * ε) ^ L = a at h1 h2 ⊢; grind
  refine ⟨fun m hm => ?_, fun m φ hφ h0 h1 => ?_⟩
  · rw [rep_expect ε false L m (detRule maj), rep_expect ε true L m (fun o => 1 - detRule maj o)]
    exact maj_upper (agree ε L) ((1 - 2 * ε) ^ L) hap ha0 hle1 m hm
  · rw [rep_expect ε false L m φ] at h0
    rw [rep_expect ε true L m (fun o => 1 - φ o)] at h1
    exact lower_bound (agree ε L) ((1 - 2 * ε) ^ L) hap ha0 hsmall m φ hφ h0 h1

end Generic

/-! ## The rational instantiation, tied to the phase-6 identities -/

section RatInst

open Prob

theorem gs_rat {α : Type} (l : List α) (f : α → Rat) : gs l f = rsum l f := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [gs_cons, rsum_cons, ih]

/-- The law fw at R = ℚ is exactly the phase-6 weight Misc.bw. -/
theorem fw_rat (ε : Rat) : ∀ e, fw ε e = Misc.bw ε e
  | [] => rfl
  | b :: e => by simp only [fw, Misc.bw, fw_rat ε e]

/-- Misc.bw IS a probability law on the domain 0 ≤ ε ≤ 1 (nonnegative, total mass 1), and
    the phase-6 agreement identity Misc.flip_agree is the event probability agree ε L. -/
theorem bw_probability (ε : Rat) (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (L : Nat) :
    (∀ e, 0 ≤ Misc.bw ε e) ∧ rsum (bitvecs L) (Misc.bw ε) = 1 ∧
    agree ε L = rsum (bitvecs L) (fun e => Misc.bw ε e * (if par e then 0 else 1)) ∧
    agree ε L = (1 + (1 - 2 * ε) ^ L) / 2 := by
  have hag : agree ε L = rsum (bitvecs L) (fun e => Misc.bw ε e * (if par e then 0 else 1)) := by
    unfold agree prob; rw [gs_rat]; apply rsum_congr; intro e _
    rw [fw_rat]; simp only; cases par e <;> simp [ind]
  refine ⟨fun e => by rw [← fw_rat]; exact fw_nonneg h0 h1 e, ?_, hag, by rw [hag]; exact Misc.flip_agree ε L⟩
  rw [← gs_rat, show (Misc.bw ε) = fw ε by funext e; rw [fw_rat]]; exact fw_total ε L

theorem q_bounds (q T : Rat) (hT : 0 < T) (c1 : 364 * T ≤ 1000 * (q * T)) (c2 : 10000 * (q * T) ≤ 3644 * T) :
    2 * q ≤ 1 ∧ 4 ≤ ((31 : Nat) : Rat) * q ^ 2 ∧ 364 ≤ 1000 * q ∧ 10000 * q ≤ 3644 := by
  have d1 : (364 : Rat) ≤ 1000 * q := by
    apply Rat.le_of_mul_le_mul_right _ hT
    have : 1000 * (q * T) = (1000 * q) * T := by grind
    rw [← this]; exact c1
  have d2 : 10000 * q ≤ (3644 : Rat) := by
    apply Rat.le_of_mul_le_mul_right _ hT
    have : 10000 * (q * T) = (10000 * q) * T := by grind
    rw [← this]; exact c2
  refine ⟨by grind, ?_, d1, d2⟩
  have := sq_le_sq' (R := Rat) (by grind : (0 : Rat) ≤ 364) d1
  have e31 : ((31 : Nat) : Rat) = 31 := by grind
  rw [e31]; grind

/-- WORKED INSTANCE of the remark's numbers ε = 1/100, L = 50: a = (49/50)^50 lies in
    [0.364, 0.3644], the small-bias condition 2a ≤ 1 holds, 31·a² ≥ 4, and therefore 31
    fresh repetitions with the majority rule give both error probabilities ≤ 1/4 (errors
    computed on the error space of 31·50 independent flips). -/
theorem remark_instance :
    364 ≤ 1000 * (1 - 2 * (1 / 100 : Rat)) ^ 50 ∧ 10000 * (1 - 2 * (1 / 100 : Rat)) ^ 50 ≤ 3644 ∧
    2 * (1 - 2 * (1 / 100 : Rat)) ^ 50 ≤ 1 ∧
    4 ≤ ((31 : Nat) : Rat) * ((1 - 2 * (1 / 100 : Rat)) ^ 50) ^ 2 ∧
    4 * gs (bitvecs (31 * 50)) (fun e => fw (1 / 100 : Rat) e * detRule maj (obsOf false 50 31 e)) ≤ 1 ∧
    4 * gs (bitvecs (31 * 50)) (fun e => fw (1 / 100 : Rat) e * (1 - detRule maj (obsOf true 50 31 e))) ≤ 1 := by
  have e1 : (1 - 2 * (1 / 100 : Rat)) = ((49 : Nat) : Rat) / ((50 : Nat) : Rat) := by grind
  have hq := Misc.pow_frac 49 50 (by decide) 50
  obtain ⟨n1, n2⟩ := Misc.flip_example_nat
  have c1 : (364 : Rat) * ((50 : Nat) : Rat) ^ 50 ≤ 1000 * ((49 : Nat) : Rat) ^ 50 := by exact_mod_cast n1
  have c2 : (10000 : Rat) * ((49 : Nat) : Rat) ^ 50 ≤ 3644 * ((50 : Nat) : Rat) ^ 50 := by exact_mod_cast n2
  have hT : (0 : Rat) < ((50 : Nat) : Rat) ^ 50 := Rat.pow_pos (by decide)
  rw [← hq] at c1 c2
  obtain ⟨hsmall, hm, hlo, hhi⟩ := q_bounds _ _ hT c1 c2
  rw [← e1] at hsmall hm hlo hhi
  have hf := flip_order_inv_sq (R := Rat) (1 / 100) 50 (by grind) hsmall
  exact ⟨hlo, hhi, hsmall, hm, hf.1 31 hm⟩

/-! ## Axiom audit -/

#print axioms gs_nil
#print axioms gs_cons
#print axioms gs_append
#print axioms gs_map
#print axioms gs_congr
#print axioms gs_add
#print axioms gs_sub
#print axioms gs_mul_left
#print axioms gs_zero
#print axioms gs_le
#print axioms gs_nonneg
#print axioms gs_bitvecs_succ
#print axioms gs_bitvecs_add
#print axioms fw_nonneg
#print axioms fw_total
#print axioms fw_append
#print axioms fw_product
#print axioms fw_blocks
#print axioms getD_drop'
#print axioms gs_fw_one
#print axioms gs_fw_head
#print axioms fw_marginal
#print axioms fw_sign
#print axioms agree_formula
#print axioms observe_law
#print axioms one_pow'
#print axioms agree_edges
#print axioms ind_and
#print axioms repeated_law
#print axioms cnt_add
#print axioms detRule_rule
#print axioms chan_prod
#print axioms prodF_one
#print axioms chan_total
#print axioms chan_nonneg
#print axioms sum3
#print axioms dev_cons
#print axioms chan_moments
#print axioms sq_le_sq'
#print axioms cheb_point
#print axioms cheb
#print axioms nat_cast_nonneg'
#print axioms quarter_of_cheb
#print axioms maj_upper
#print axioms lr_mul
#print axioms chi_identity
#print axioms chiG_bias
#print axioms bernoulli_le
#print axioms sum3'
#print axioms err_sum
#print axioms sq_unit
#print axioms final_arith
#print axioms chi_ge_two
#print axioms samples_from_chi
#print axioms lower_bound_general
#print axioms lower_bound
#print axioms no_signal
#print axioms exact_channel
#print axioms order_inv_sq
#print axioms gs_comm
#print axioms gs_point
#print axioms obsOf_length
#print axioms rep_expect
#print axioms flip_order_inv_sq
#print axioms gs_rat
#print axioms fw_rat
#print axioms bw_probability
#print axioms q_bounds
#print axioms remark_instance

end RatInst
end Noise
end NimAudit
