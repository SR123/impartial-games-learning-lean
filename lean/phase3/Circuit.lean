import NimProbability

/- Phase 3, target C: network-to-AC0 simulation.  Written by Claude (10 October 2026).
   Lean 4.26.0, core/Std only.

   Circuit model.  `Circ` is a Boolean FORMULA (tree, no sharing) over input
   variables indexed by Nat, with constants, NOT, and unbounded fan-in AND/OR.
     size  = number of formula nodes (leaves, NOT, AND, OR).  A formula-size
             bound is also a circuit-size bound (gates + wires is at most twice it).
     depth = longest root-to-leaf path counting every AND, OR and NOT node.
   Gates (paper Definition NN-formal, after clearing the denominator D > 0):
     nonnegative integer coefficients a_j on literals z_j XOR eta_j, integer
     threshold b, firing iff  b ≤ Σ_j a_j [z_j XOR eta_j].  Validity: b ≤ W
     (and a_j ≤ W, which the construction does not need).
   Proved here:
     * rational form with denominator D > 0 ↔ integer form (gate_rat_iff);
     * bounded witness lemma (≤ b ≤ W true literals suffice);
     * DNF compilation with semantic equality, depth ≤ 3 and size
       ≤ 1 + (m+1)^W (2W+1), including b = 0, m = 0 and W = 0;
     * layer/network composition by substitution, with depth ≤ 3L and size
       ≤ 2 (2W+3)^L (M+1)^(W L) for L layers of fan-in/width ≤ M;
     * network-family statement with widths ≤ c (n+1)^k (polynomial bound);
     * recurrent unrolling for a fixed number T of updates from an
       input-independent initial state.
   Not formalised: softmax or any attention primitive not already built from
   these gates; floating-point semantics; trained models. -/

namespace NimAudit
namespace AC0

open Prob

attribute [local simp] Rat.add_zero Rat.zero_add Rat.zero_mul Rat.mul_zero Rat.one_mul

inductive Circ where
  | input (i : Nat)
  | const (b : Bool)
  | not (c : Circ)
  | and (cs : List Circ)
  | or (cs : List Circ)

namespace Circ

def eval (x : Nat → Bool) : Circ → Bool
  | input i => x i
  | const b => b
  | not c => !(eval x c)
  | and cs => cs.attach.all (fun ⟨c, _⟩ => eval x c)
  | or cs => cs.attach.any (fun ⟨c, _⟩ => eval x c)

def size : Circ → Nat
  | input _ => 1
  | const _ => 1
  | not c => size c + 1
  | and cs => (cs.attach.map (fun ⟨c, _⟩ => size c)).sum + 1
  | or cs => (cs.attach.map (fun ⟨c, _⟩ => size c)).sum + 1

/-- Maximum of a list of naturals (0 for the empty list). -/
def listMax (l : List Nat) : Nat := l.foldr max 0

def depth : Circ → Nat
  | input _ => 0
  | const _ => 0
  | not c => depth c + 1
  | and cs => listMax (cs.attach.map (fun ⟨c, _⟩ => depth c)) + 1
  | or cs => listMax (cs.attach.map (fun ⟨c, _⟩ => depth c)) + 1

/-- One more than the largest input index used (0 if none). -/
def maxInput : Circ → Nat
  | input i => i + 1
  | const _ => 0
  | not c => maxInput c
  | and cs => listMax (cs.attach.map (fun ⟨c, _⟩ => maxInput c))
  | or cs => listMax (cs.attach.map (fun ⟨c, _⟩ => maxInput c))

/-- Substitute circuits for input variables. -/
def subst (σ : Nat → Circ) : Circ → Circ
  | input i => σ i
  | const b => const b
  | not c => not (subst σ c)
  | and cs => and (cs.attach.map (fun ⟨c, _⟩ => subst σ c))
  | or cs => or (cs.attach.map (fun ⟨c, _⟩ => subst σ c))

@[simp] theorem eval_input (x : Nat → Bool) (i : Nat) : eval x (input i) = x i := by simp [eval]
@[simp] theorem eval_const (x : Nat → Bool) (b : Bool) : eval x (const b) = b := by simp [eval]
@[simp] theorem eval_not (x : Nat → Bool) (c : Circ) : eval x (not c) = !(eval x c) := by
  simp [eval]
@[simp] theorem eval_and (x : Nat → Bool) (cs : List Circ) : eval x (and cs) = cs.all (eval x) := by
  simp [eval]
@[simp] theorem eval_or (x : Nat → Bool) (cs : List Circ) : eval x (or cs) = cs.any (eval x) := by
  simp [eval]
@[simp] theorem size_input (i : Nat) : size (input i) = 1 := by simp [size]
@[simp] theorem size_const (b : Bool) : size (const b) = 1 := by simp [size]
@[simp] theorem size_not (c : Circ) : size (not c) = size c + 1 := by simp [size]
@[simp] theorem size_and (cs : List Circ) : size (and cs) = (cs.map size).sum + 1 := by simp [size]
@[simp] theorem size_or (cs : List Circ) : size (or cs) = (cs.map size).sum + 1 := by simp [size]
@[simp] theorem depth_input (i : Nat) : depth (input i) = 0 := by simp [depth]
@[simp] theorem depth_const (b : Bool) : depth (const b) = 0 := by simp [depth]
@[simp] theorem depth_not (c : Circ) : depth (not c) = depth c + 1 := by simp [depth]
@[simp] theorem depth_and (cs : List Circ) : depth (and cs) = listMax (cs.map depth) + 1 := by
  simp [depth]
@[simp] theorem depth_or (cs : List Circ) : depth (or cs) = listMax (cs.map depth) + 1 := by
  simp [depth]
@[simp] theorem maxInput_input (i : Nat) : maxInput (input i) = i + 1 := by simp [maxInput]
@[simp] theorem maxInput_const (b : Bool) : maxInput (const b) = 0 := by simp [maxInput]
@[simp] theorem maxInput_not (c : Circ) : maxInput (not c) = maxInput c := by simp [maxInput]
@[simp] theorem maxInput_and (cs : List Circ) : maxInput (and cs) = listMax (cs.map maxInput) := by
  simp [maxInput]
@[simp] theorem maxInput_or (cs : List Circ) : maxInput (or cs) = listMax (cs.map maxInput) := by
  simp [maxInput]
@[simp] theorem subst_input (σ : Nat → Circ) (i : Nat) : subst σ (input i) = σ i := by simp [subst]
@[simp] theorem subst_const (σ : Nat → Circ) (b : Bool) : subst σ (const b) = const b := by
  simp [subst]
@[simp] theorem subst_not (σ : Nat → Circ) (c : Circ) : subst σ (not c) = not (subst σ c) := by
  simp [subst]
@[simp] theorem subst_and (σ : Nat → Circ) (cs : List Circ) :
    subst σ (and cs) = and (cs.map (subst σ)) := by simp [subst]
@[simp] theorem subst_or (σ : Nat → Circ) (cs : List Circ) :
    subst σ (or cs) = or (cs.map (subst σ)) := by simp [subst]

theorem le_listMax {l : List Nat} {a : Nat} (h : a ∈ l) : a ≤ listMax l := by
  induction l with
  | nil => simp at h
  | cons b l ih =>
    simp only [listMax, List.foldr_cons] at *
    rcases List.mem_cons.mp h with rfl | h
    · omega
    · have := ih h; omega

theorem listMax_le {l : List Nat} {d : Nat} (h : ∀ a ∈ l, a ≤ d) : listMax l ≤ d := by
  induction l with
  | nil => simp [listMax]
  | cons b l ih =>
    simp only [listMax, List.foldr_cons]
    have h1 := h b (by simp)
    have h2 := ih (fun a ha => h a (List.mem_cons_of_mem _ ha))
    simp only [listMax] at h2
    omega

theorem all_congr_mem {α : Type} {l : List α} {f g : α → Bool} (h : ∀ a ∈ l, f a = g a) :
    l.all f = l.all g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.all_cons]
    rw [h a (by simp), ih (fun b hb => h b (List.mem_cons_of_mem _ hb))]

theorem any_congr_mem {α : Type} {l : List α} {f g : α → Bool} (h : ∀ a ∈ l, f a = g a) :
    l.any f = l.any g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.any_cons]
    rw [h a (by simp), ih (fun b hb => h b (List.mem_cons_of_mem _ hb))]

theorem sum_map_le_mem {α : Type} {l : List α} {f g : α → Nat} (h : ∀ a ∈ l, f a ≤ g a) :
    (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    have := h a (by simp)
    have := ih (fun b hb => h b (List.mem_cons_of_mem _ hb))
    omega

theorem sum_map_mul_right {α : Type} (l : List α) (f : α → Nat) (k : Nat) :
    (l.map (fun a => f a * k)).sum = (l.map f).sum * k := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.sum_cons, ih, Nat.add_mul]

/-- Substitution is composition of semantics. -/
theorem eval_subst (σ : Nat → Circ) (x : Nat → Bool) : ∀ c : Circ,
    eval x (subst σ c) = eval (fun i => eval x (σ i)) c
  | input i => by simp
  | const b => by simp
  | not c => by simp [eval_subst σ x c]
  | and cs => by
    simp only [subst_and, eval_and, List.all_map]
    exact all_congr_mem (fun c _ => eval_subst σ x c)
  | or cs => by
    simp only [subst_or, eval_or, List.any_map]
    exact any_congr_mem (fun c _ => eval_subst σ x c)

/-- Size of a substitution: each leaf grows to at most S + 1 nodes. -/
theorem size_subst_le (σ : Nat → Circ) (S : Nat) (hσ : ∀ i, size (σ i) ≤ S) : ∀ c : Circ,
    size (subst σ c) ≤ size c * (S + 1)
  | input i => by simp; have := hσ i; omega
  | const b => by simp
  | not c => by
    have := size_subst_le σ S hσ c
    simp only [subst_not, size_not, Nat.add_mul, Nat.one_mul]
    omega
  | and cs => by
    simp only [subst_and, size_and, List.map_map, Nat.add_mul, Nat.one_mul]
    have h := sum_map_le_mem (l := cs) (f := size ∘ subst σ) (g := fun c => size c * (S + 1))
      (fun c _ => size_subst_le σ S hσ c)
    rw [sum_map_mul_right] at h
    omega
  | or cs => by
    simp only [subst_or, size_or, List.map_map, Nat.add_mul, Nat.one_mul]
    have h := sum_map_le_mem (l := cs) (f := size ∘ subst σ) (g := fun c => size c * (S + 1))
      (fun c _ => size_subst_le σ S hσ c)
    rw [sum_map_mul_right] at h
    omega

/-- Depth of a substitution: at most depth c + D. -/
theorem depth_subst_le (σ : Nat → Circ) (D : Nat) (hσ : ∀ i, depth (σ i) ≤ D) : ∀ c : Circ,
    depth (subst σ c) ≤ depth c + D
  | input i => by simp; exact hσ i
  | const b => by simp
  | not c => by have := depth_subst_le σ D hσ c; simp; omega
  | and cs => by
    simp only [subst_and, depth_and, List.map_map]
    have : listMax (cs.map (depth ∘ subst σ)) ≤ listMax (cs.map depth) + D := by
      apply listMax_le
      intro a ha
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ha
      have h1 := depth_subst_le σ D hσ c
      have h2 := le_listMax (List.mem_map_of_mem (f := depth) hc)
      simp only [Function.comp]; omega
    omega
  | or cs => by
    simp only [subst_or, depth_or, List.map_map]
    have : listMax (cs.map (depth ∘ subst σ)) ≤ listMax (cs.map depth) + D := by
      apply listMax_le
      intro a ha
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ha
      have h1 := depth_subst_le σ D hσ c
      have h2 := le_listMax (List.mem_map_of_mem (f := depth) hc)
      simp only [Function.comp]; omega
    omega

/-- Substituting leaves (inputs or constants) preserves size and depth exactly. -/
def IsLeaf : Circ → Prop
  | input _ => True
  | const _ => True
  | _ => False

theorem size_leaf {c : Circ} (h : IsLeaf c) : size c = 1 := by
  cases c <;> simp_all [IsLeaf]

theorem depth_leaf {c : Circ} (h : IsLeaf c) : depth c = 0 := by
  cases c <;> simp_all [IsLeaf]

theorem size_subst_leaf (σ : Nat → Circ) (hσ : ∀ i, IsLeaf (σ i)) : ∀ c : Circ,
    size (subst σ c) = size c
  | input i => by simp [size_leaf (hσ i)]
  | const b => by simp
  | not c => by simp [size_subst_leaf σ hσ c]
  | and cs => by
    simp only [subst_and, size_and, List.map_map]
    congr 2
    exact List.map_congr_left (fun c _ => size_subst_leaf σ hσ c)
  | or cs => by
    simp only [subst_or, size_or, List.map_map]
    congr 2
    exact List.map_congr_left (fun c _ => size_subst_leaf σ hσ c)

theorem depth_subst_leaf (σ : Nat → Circ) (hσ : ∀ i, IsLeaf (σ i)) : ∀ c : Circ,
    depth (subst σ c) = depth c
  | input i => by simp [depth_leaf (hσ i)]
  | const b => by simp
  | not c => by simp [depth_subst_leaf σ hσ c]
  | and cs => by
    simp only [subst_and, depth_and, List.map_map]
    congr 2
    exact List.map_congr_left (fun c _ => depth_subst_leaf σ hσ c)
  | or cs => by
    simp only [subst_or, depth_or, List.map_map]
    congr 2
    exact List.map_congr_left (fun c _ => depth_subst_leaf σ hσ c)

/-- Inputs of a substitution: bounded when every substituted circuit is bounded. -/
theorem maxInput_subst_le (σ : Nat → Circ) (m : Nat) (hσ : ∀ i, maxInput (σ i) ≤ m) :
    ∀ c : Circ, maxInput (subst σ c) ≤ m
  | input i => by simp; exact hσ i
  | const b => by simp
  | not c => by simp; exact maxInput_subst_le σ m hσ c
  | and cs => by
    simp only [subst_and, maxInput_and, List.map_map]
    apply listMax_le
    intro a ha
    obtain ⟨c, _, rfl⟩ := List.mem_map.mp ha
    exact maxInput_subst_le σ m hσ c
  | or cs => by
    simp only [subst_or, maxInput_or, List.map_map]
    apply listMax_le
    intro a ha
    obtain ⟨c, _, rfl⟩ := List.mem_map.mp ha
    exact maxInput_subst_le σ m hσ c

/-- Evaluation depends only on inputs below maxInput. -/
theorem eval_congr_below (x y : Nat → Bool) : ∀ c : Circ,
    (∀ i, i < maxInput c → x i = y i) → eval x c = eval y c
  | input i => by intro h; simp; exact h i (by simp)
  | const b => by intro _; simp
  | not c => by intro h; simp only [eval_not]; rw [eval_congr_below x y c (by simpa using h)]
  | and cs => by
    intro h
    simp only [eval_and]
    apply all_congr_mem
    intro c hc
    apply eval_congr_below x y c
    intro i hi
    apply h i
    simp only [maxInput_and]
    exact Nat.lt_of_lt_of_le hi (le_listMax (List.mem_map_of_mem hc))
  | or cs => by
    intro h
    simp only [eval_or]
    apply any_congr_mem
    intro c hc
    apply eval_congr_below x y c
    intro i hi
    apply h i
    simp only [maxInput_or]
    exact Nat.lt_of_lt_of_le hi (le_listMax (List.mem_map_of_mem hc))

end Circ

open Circ

/-! ## Threshold gates -/

/-- A literal-threshold gate after clearing denominators: coefficients a_j,
    negation bits eta_j, threshold b.  Its fan-in is `coeffs.length`. -/
structure Gate where
  coeffs : List Nat
  negs : List Bool
  thr : Nat

namespace Gate

def fanin (g : Gate) : Nat := g.coeffs.length
def coeff (g : Gate) (j : Nat) : Nat := g.coeffs.getD j 0
def lit (g : Gate) (z : Nat → Bool) (j : Nat) : Bool := xor (z j) (g.negs.getD j false)

/-- Partial weighted sum over the first c inputs. -/
def psum (g : Gate) (z : Nat → Bool) (c : Nat) : Nat :=
  ((List.range c).map (fun j => g.coeff j * (if g.lit z j then 1 else 0))).sum

def wsum (g : Gate) (z : Nat → Bool) : Nat := g.psum z g.fanin

/-- The gate fires iff b ≤ Σ_j a_j [z_j XOR eta_j]. -/
def eval (g : Gate) (z : Nat → Bool) : Bool := decide (g.thr ≤ g.wsum z)

/-- Fixed-scale validity: threshold and coefficients in 0..W. -/
def Valid (W : Nat) (g : Gate) : Prop := g.thr ≤ W ∧ ∀ a ∈ g.coeffs, a ≤ W

end Gate

/-! ### Rational form with denominator D -/

/-- Paper's form: weights a_j/D, threshold b/D, Heaviside(Σ w_j lit_j − θ). -/
def ratFires (g : Gate) (D : Nat) (z : Nat → Bool) : Prop :=
  0 ≤ rsum (List.range g.fanin)
      (fun j => ((g.coeff j : Nat) : Rat) / (D : Rat) * (if g.lit z j then 1 else 0)) -
    ((g.thr : Nat) : Rat) / (D : Rat)

theorem rsum_natCast (l : List Nat) (f : Nat → Nat) :
    rsum l (fun j => ((f j : Nat) : Rat)) = (((l.map f).sum : Nat) : Rat) := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [rsum_cons, ih, List.map_cons, List.sum_cons, Rat.natCast_add]

/-- CLEARING DENOMINATORS: for D > 0 the rational gate fires iff the integer gate does. -/
theorem gate_rat_iff (g : Gate) {D : Nat} (hD : 0 < D) (z : Nat → Bool) :
    ratFires g D z ↔ g.eval z = true := by
  have hDr : (0 : Rat) < (D : Rat) := Rat.natCast_pos.mpr hD
  have hD' : (D : Rat) ≠ 0 := Rat.ne_of_gt hDr
  have e : rsum (List.range g.fanin)
      (fun j => ((g.coeff j : Nat) : Rat) / (D : Rat) * (if g.lit z j then 1 else 0)) =
      ((g.wsum z : Nat) : Rat) / (D : Rat) := by
    have e1 : rsum (List.range g.fanin)
        (fun j => ((g.coeff j : Nat) : Rat) / (D : Rat) * (if g.lit z j then 1 else 0)) =
        rsum (List.range g.fanin)
          (fun j => (1 / (D : Rat)) * (((g.coeff j * (if g.lit z j then 1 else 0) : Nat)) : Rat)) := by
      apply rsum_congr; intro j _
      by_cases hl : g.lit z j = true <;> simp [hl] <;> grind
    rw [e1, rsum_mul_left, rsum_natCast]
    unfold Gate.wsum Gate.psum
    grind
  unfold ratFires Gate.eval
  rw [e, decide_eq_true_iff]
  generalize g.wsum z = s
  generalize g.thr = b
  constructor
  · intro h
    have h' : ((b : Nat) : Rat) / (D : Rat) ≤ ((s : Nat) : Rat) / (D : Rat) := by grind
    have := Rat.mul_le_mul_of_nonneg_right h' (Rat.le_of_lt hDr)
    have e2 : ((b : Nat) : Rat) / (D : Rat) * (D : Rat) = b := by grind
    have e3 : ((s : Nat) : Rat) / (D : Rat) * (D : Rat) = s := by grind
    rw [e2, e3] at this
    exact Rat.natCast_le_natCast.mp this
  · intro h
    have h1 : ((b : Nat) : Rat) ≤ (s : Rat) := Rat.natCast_le_natCast.mpr h
    have hinv : (0 : Rat) ≤ 1 / (D : Rat) := by
      have := Rat.mul_le_mul_of_nonneg_right (Rat.le_of_lt hDr) (Rat.le_of_lt hDr)
      have h2 : (0 : Rat) < 1 / (D : Rat) := by
        have := (Rat.mul_pos_iff_of_pos_left hDr).mp (by grind : (0 : Rat) < (D : Rat) * (1 / (D : Rat)))
        exact this
      exact Rat.le_of_lt h2
    have := Rat.mul_le_mul_of_nonneg_right h1 hinv
    grind

/-! ### Nat sums over ranges -/

def nsum (c : Nat) (f : Nat → Nat) : Nat := ((List.range c).map f).sum

theorem nsum_succ (c : Nat) (f : Nat → Nat) : nsum (c + 1) f = nsum c f + f c := by
  simp [nsum, List.range_succ, List.sum_append_nat]

theorem nsum_zero (f : Nat → Nat) : nsum 0 f = 0 := rfl

theorem nsum_le {c : Nat} {f g : Nat → Nat} (h : ∀ j < c, f j ≤ g j) : nsum c f ≤ nsum c g := by
  induction c with
  | zero => simp [nsum]
  | succ c ih =>
    rw [nsum_succ, nsum_succ]
    have := ih (fun j hj => h j (by omega))
    have := h c (by omega)
    omega

theorem nsum_congr {c : Nat} {f g : Nat → Nat} (h : ∀ j < c, f j = g j) : nsum c f = nsum c g := by
  induction c with
  | zero => rfl
  | succ c ih => rw [nsum_succ, nsum_succ, ih (fun j hj => h j (by omega)), h c (by omega)]

theorem nsum_mono (f : Nat → Nat) {c d : Nat} (h : c ≤ d) : nsum c f ≤ nsum d f := by
  induction d with
  | zero => have : c = 0 := by omega
            subst this; exact Nat.le_refl _
  | succ d ih =>
    by_cases hc : c = d + 1
    · subst hc; exact Nat.le_refl _
    · rw [nsum_succ]; have := ih (by omega); omega

/-- Restricting the sum to j < c. -/
theorem nsum_cut (f : Nat → Nat) {c m : Nat} (h : c ≤ m) :
    nsum m (fun j => if j < c then f j else 0) = nsum c f := by
  induction m with
  | zero => have : c = 0 := by omega
            subst this; rfl
  | succ m ih =>
    by_cases hc : c = m + 1
    · subst hc
      rw [nsum_succ, nsum_succ]
      rw [nsum_congr (g := f) (fun j hj => by simp [show j < m + 1 by omega])]
      simp
    · rw [nsum_succ, ih (by omega)]
      simp [show ¬ m < c by omega]

theorem length_filter_eq_nsum (c : Nat) (p : Nat → Bool) :
    ((List.range c).filter p).length = nsum c (fun j => if p j then 1 else 0) := by
  induction c with
  | zero => rfl
  | succ c ih =>
    rw [List.range_succ, List.filter_append, List.length_append, ih, nsum_succ]
    cases hp : p c <;> simp [hp]

/-! ### Bounded witness lemma -/

namespace Gate

theorem psum_succ (g : Gate) (z : Nat → Bool) (c : Nat) :
    g.psum z (c + 1) = g.psum z c + g.coeff c * (if g.lit z c then 1 else 0) := by
  simp [psum, List.range_succ, List.sum_append_nat]

theorem psum_mono (g : Gate) (z : Nat → Bool) {c d : Nat} (h : c ≤ d) : g.psum z c ≤ g.psum z d :=
  nsum_mono _ h

/-- The active (true, positive-coefficient) literals among the first c inputs. -/
def active (g : Gate) (z : Nat → Bool) (c : Nat) : List Nat :=
  (List.range c).filter (fun j => g.lit z j && decide (1 ≤ g.coeff j))

theorem active_length_le (g : Gate) (z : Nat → Bool) (c : Nat) :
    (g.active z c).length ≤ g.psum z c := by
  unfold active
  rw [length_filter_eq_nsum]
  unfold psum
  apply nsum_le
  intro j _
  by_cases hl : g.lit z j = true <;> by_cases ha : 1 ≤ g.coeff j <;> simp [hl, ha] <;> omega

theorem exists_cut (g : Gate) (z : Nat → Bool) (c : Nat) (h : g.thr ≤ g.psum z c) :
    ∃ c' ≤ c, g.thr ≤ g.psum z c' ∧ ∀ c'' < c', g.psum z c'' < g.thr := by
  induction c with
  | zero => exact ⟨0, Nat.le_refl _, h, fun c'' hc'' => by omega⟩
  | succ c ih =>
    by_cases hc : g.thr ≤ g.psum z c
    · obtain ⟨c', hc', h1, h2⟩ := ih hc
      exact ⟨c', by omega, h1, h2⟩
    · refine ⟨c + 1, Nat.le_refl _, h, ?_⟩
      intro c'' hc''
      have := g.psum_mono z (show c'' ≤ c by omega)
      omega

/-- BOUNDED WITNESS LEMMA.  If the gate fires on z, there is a list T of at most
    b ≤ W distinct input positions, all with true literal and positive coefficient,
    whose coefficients sum to at least b; T is an initial segment of the active
    literals (T = active literals below a cut c'). -/
theorem bounded_witness (g : Gate) (z : Nat → Bool) (h : g.eval z = true) :
    ∃ c' ≤ g.fanin,
      (g.active z c').length ≤ g.thr ∧
      (∀ j ∈ g.active z c', g.lit z j = true ∧ 1 ≤ g.coeff j ∧ j < c') ∧
      g.thr ≤ nsum g.fanin (fun j => if j ∈ g.active z c' then g.coeff j else 0) := by
  unfold eval wsum at h
  have h' : g.thr ≤ g.psum z g.fanin := of_decide_eq_true h
  obtain ⟨c', hc', h1, h2⟩ := exists_cut g z g.fanin h'
  refine ⟨c', hc', ?_, ?_, ?_⟩
  · -- length bound
    cases c' with
    | zero => simp [active]
    | succ c =>
      have hlt := h2 c (by omega)
      have hlen := active_length_le g z c
      have hstep : (g.active z (c + 1)).length ≤ (g.active z c).length + 1 := by
        unfold active
        rw [List.range_succ, List.filter_append, List.length_append]
        have : (List.filter (fun j => g.lit z j && decide (1 ≤ g.coeff j)) [c]).length ≤ 1 := by
          simp only [List.filter_cons, List.filter_nil]; split <;> simp
        omega
      omega
  · intro j hj
    unfold active at hj
    simp only [List.mem_filter, List.mem_range, Bool.and_eq_true, decide_eq_true_eq] at hj
    exact ⟨hj.2.1, hj.2.2, hj.1⟩
  · have e : nsum g.fanin (fun j => if j ∈ g.active z c' then g.coeff j else 0) =
        nsum g.fanin (fun j => if j < c' then g.coeff j * (if g.lit z j then 1 else 0) else 0) := by
      apply nsum_congr
      intro j _
      unfold active
      simp only [List.mem_filter, List.mem_range, Bool.and_eq_true, decide_eq_true_eq]
      by_cases hjc : j < c' <;> by_cases hl : g.lit z j = true <;>
        by_cases ha : 1 ≤ g.coeff j <;> simp [hjc, hl, ha] <;> omega
    rw [e, nsum_cut _ hc']
    exact h1

end Gate

/-! ### DNF compilation of one gate -/

/-- Literal circuit for input j of gate g. -/
def litC (g : Gate) (j : Nat) : Circ :=
  if g.negs.getD j false then not (input j) else input j

theorem eval_litC (g : Gate) (z : Nat → Bool) (j : Nat) : eval z (litC g j) = g.lit z j := by
  unfold litC Gate.lit
  cases g.negs.getD j false <;> simp

/-- Sum of coefficients of the positions (below the fan-in) occurring in tuple t. -/
def selSum (g : Gate) (t : List Nat) : Nat :=
  nsum g.fanin (fun j => if j ∈ t then g.coeff j else 0)

/-- The conjunction of the literals named in t (entries ≥ fan-in are padding). -/
def termC (g : Gate) (t : List Nat) : Circ :=
  and (t.filterMap (fun j => if j < g.fanin then some (litC g j) else none))

/-- DNF: OR over padded tuples t ∈ {0..m}^W with selSum ≥ b of termC t. -/
def dnf (W : Nat) (g : Gate) : Circ :=
  or (((boards (g.fanin + 1) W).filter (fun t => decide (g.thr ≤ selSum g t))).map (termC g))

theorem mem_boards_of {q N : Nat} {P : List Nat} (hl : P.length = N) (hb : ∀ x ∈ P, x < q) :
    P ∈ boards q N := by
  induction N generalizing P with
  | zero => cases P with
    | nil => simp [boards]
    | cons _ _ => simp at hl
  | succ N ih =>
    cases P with
    | nil => simp at hl
    | cons x P =>
      simp only [boards, List.mem_flatMap, List.mem_range, List.mem_map]
      refine ⟨x, hb x (by simp), P, ih (by simpa using hl) (fun y hy => hb y (by simp [hy])), rfl⟩

theorem length_boards (q N : Nat) : (boards q N).length = q ^ N := by
  induction N with
  | zero => simp [boards]
  | succ N ih =>
    simp only [boards, List.length_flatMap, List.length_map, ih]
    rw [List.map_const', List.sum_replicate_nat, List.length_range, Nat.pow_succ, Nat.mul_comm]

theorem eval_termC (g : Gate) (z : Nat → Bool) (t : List Nat) :
    eval z (termC g t) = true ↔ ∀ j ∈ t, j < g.fanin → g.lit z j = true := by
  unfold termC
  simp only [eval_and, List.all_eq_true, List.mem_filterMap]
  constructor
  · intro h j hj hjm
    have := h (litC g j) ⟨j, hj, by simp [hjm]⟩
    rwa [eval_litC] at this
  · rintro h c ⟨j, hj, hc⟩
    by_cases hjm : j < g.fanin
    · simp only [hjm, if_true, Option.some.injEq] at hc
      subst hc
      rw [eval_litC]
      exact h j hj hjm
    · simp [hjm] at hc

/-- DNF CORRECTNESS: for b ≤ W, the DNF computes the gate exactly (any fan-in,
    including 0; b = 0 gives the constant-true DNF). -/
theorem eval_dnf {W : Nat} (g : Gate) (hW : g.thr ≤ W) (z : Nat → Bool) :
    eval z (dnf W g) = g.eval z := by
  apply Bool.eq_iff_iff.mpr
  unfold dnf
  simp only [eval_or, List.any_map, List.any_eq_true, List.mem_filter, decide_eq_true_eq,
    Function.comp]
  constructor
  · rintro ⟨t, ⟨_, hsel⟩, ht⟩
    have hlit := (eval_termC g z t).1 ht
    unfold Gate.eval Gate.wsum Gate.psum
    apply decide_eq_true
    apply Nat.le_trans hsel
    unfold selSum
    apply nsum_le
    intro j hj
    by_cases hjt : j ∈ t
    · simp [hjt, hlit j hjt hj]
    · simp [hjt]
  · intro h
    obtain ⟨c', hc', hlen, hact, hsum⟩ := g.bounded_witness z h
    generalize g.active z c' = L at hlen hact hsum
    let t := L ++ List.replicate (W - L.length) g.fanin
    have hmemt : ∀ j, j < g.fanin → (j ∈ t ↔ j ∈ L) := by
      intro j hj
      simp only [t, List.mem_append, List.mem_replicate]
      constructor
      · rintro (h | ⟨_, h⟩)
        · exact h
        · omega
      · exact Or.inl
    refine ⟨t, ⟨?_, ?_⟩, ?_⟩
    · apply mem_boards_of
      · simp only [t, List.length_append, List.length_replicate]; omega
      · intro x hx
        simp only [t, List.mem_append, List.mem_replicate] at hx
        rcases hx with hx | ⟨_, rfl⟩
        · have := (hact x hx).2.2; omega
        · omega
    · unfold selSum
      rw [nsum_congr (g := fun j => if j ∈ L then g.coeff j else 0)]
      · exact hsum
      · intro j hj
        by_cases hjL : j ∈ L
        · simp [hjL, (hmemt j hj).2 hjL]
        · have : j ∉ t := fun h' => hjL ((hmemt j hj).1 h')
          simp [hjL, this]
    · rw [eval_termC]
      intro j hjt hjm
      exact (hact j ((hmemt j hjm).1 hjt)).1

theorem size_termC (g : Gate) (t : List Nat) : size (termC g t) ≤ 2 * t.length + 1 := by
  unfold termC
  simp only [size_and]
  have h : ∀ (l : List Nat),
      ((l.filterMap (fun j => if j < g.fanin then some (litC g j) else none)).map size).sum ≤
        2 * l.length := by
    intro l
    induction l with
    | nil => simp
    | cons j l ih =>
      simp only [List.filterMap_cons, List.length_cons]
      by_cases hj : j < g.fanin
      · simp only [hj, if_true, List.map_cons, List.sum_cons]
        have : size (litC g j) ≤ 2 := by unfold litC; split <;> simp
        omega
      · simp only [hj, if_false]; omega
  have := h t
  omega

theorem depth_termC (g : Gate) (t : List Nat) : depth (termC g t) ≤ 2 := by
  unfold termC
  simp only [depth_and]
  have : listMax ((t.filterMap (fun j => if j < g.fanin then some (litC g j) else none)).map depth) ≤ 1 := by
    apply listMax_le
    intro a ha
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ha
    obtain ⟨j, _, hj⟩ := List.mem_filterMap.mp hc
    by_cases hjm : j < g.fanin
    · simp only [hjm, if_true, Option.some.injEq] at hj
      subst hj; unfold litC; split <;> simp
    · simp [hjm] at hj
  omega

theorem maxInput_termC (g : Gate) (t : List Nat) : maxInput (termC g t) ≤ g.fanin := by
  unfold termC
  simp only [maxInput_and]
  apply listMax_le
  intro a ha
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ha
  obtain ⟨j, _, hj⟩ := List.mem_filterMap.mp hc
  by_cases hjm : j < g.fanin
  · simp only [hjm, if_true, Option.some.injEq] at hj
    subst hj; unfold litC; split <;> simp <;> omega
  · simp [hjm] at hj

/-- DNF SIZE: at most 1 + (m+1)^W (2W+1) formula nodes, m = fan-in. -/
theorem size_dnf (W : Nat) (g : Gate) : size (dnf W g) ≤ 1 + (g.fanin + 1) ^ W * (2 * W + 1) := by
  unfold dnf
  simp only [size_or, List.map_map]
  have hterm : ∀ t ∈ (boards (g.fanin + 1) W).filter (fun t => decide (g.thr ≤ selSum g t)),
      (size ∘ termC g) t ≤ 2 * W + 1 := by
    intro t ht
    have hmem := (List.mem_filter.mp ht).1
    have hl := (mem_boards hmem).1
    have := size_termC g t
    simp only [Function.comp]; omega
  have h1 := sum_map_le_mem hterm
  rw [List.map_const', List.sum_replicate_nat] at h1
  have h2 : ((boards (g.fanin + 1) W).filter (fun t => decide (g.thr ≤ selSum g t))).length ≤
      (g.fanin + 1) ^ W := by
    rw [← length_boards]; exact List.length_filter_le _ _
  have h3 := Nat.mul_le_mul_right (2 * W + 1) h2
  omega

theorem depth_dnf (W : Nat) (g : Gate) : depth (dnf W g) ≤ 3 := by
  unfold dnf
  simp only [depth_or, List.map_map]
  have : listMax (((boards (g.fanin + 1) W).filter
      (fun t => decide (g.thr ≤ selSum g t))).map (depth ∘ termC g)) ≤ 2 := by
    apply listMax_le
    intro a ha
    obtain ⟨t, _, rfl⟩ := List.mem_map.mp ha
    exact depth_termC g t
  omega

theorem maxInput_dnf (W : Nat) (g : Gate) : maxInput (dnf W g) ≤ g.fanin := by
  unfold dnf
  simp only [maxInput_or, List.map_map]
  apply listMax_le
  intro a ha
  obtain ⟨t, _, rfl⟩ := List.mem_map.mp ha
  exact maxInput_termC g t

/-- ONE-GATE LEMMA (paper Lemma unit-ac0): exact, depth ≤ 3, size ≤ 1 + (m+1)^W (2W+1). -/
theorem gate_ac0 {W : Nat} (g : Gate) (hW : g.thr ≤ W) :
    (∀ z, eval z (dnf W g) = g.eval z) ∧ depth (dnf W g) ≤ 3 ∧
      size (dnf W g) ≤ 1 + (g.fanin + 1) ^ W * (2 * W + 1) ∧ maxInput (dnf W g) ≤ g.fanin :=
  ⟨eval_dnf g hW, depth_dnf W g, size_dnf W g, maxInput_dnf W g⟩

/-! ## Layers and networks -/

/-- A layer: a list of gates reading the previous layer's outputs (indexed by Nat). -/
abbrev Layer := List Gate

def evalLayer (l : Layer) (z : Nat → Bool) : Nat → Bool :=
  fun i => match l[i]? with
    | some g => g.eval z
    | none => false

/-- A network: layers applied in order. -/
def evalNet : List Layer → (Nat → Bool) → (Nat → Bool)
  | [], z => z
  | l :: ls, z => evalNet ls (evalLayer l z)

def compileLayer (W : Nat) (l : Layer) (prev : Nat → Circ) : Nat → Circ :=
  fun i => match l[i]? with
    | some g => subst prev (dnf W g)
    | none => const false

def compileNet (W : Nat) : List Layer → (Nat → Circ) → (Nat → Circ)
  | [], prev => prev
  | l :: ls, prev => compileNet W ls (compileLayer W l prev)

/-- All gates valid for W. -/
def NetValid (W : Nat) (ls : List Layer) : Prop := ∀ l ∈ ls, ∀ g ∈ l, Gate.Valid W g

/-- Fan-in and width bounded by M. -/
def NetBounded (M : Nat) (ls : List Layer) : Prop := ∀ l ∈ ls, l.length ≤ M ∧ ∀ g ∈ l, g.fanin ≤ M

theorem eval_compileLayer {W : Nat} (l : Layer) (hv : ∀ g ∈ l, Gate.Valid W g)
    (prev : Nat → Circ) (x : Nat → Bool) (i : Nat) :
    eval x (compileLayer W l prev i) = evalLayer l (fun j => eval x (prev j)) i := by
  unfold compileLayer evalLayer
  cases h : l[i]? with
  | none => simp
  | some g =>
    simp only
    rw [eval_subst, eval_dnf g (hv g (List.mem_of_getElem? h)).1]

/-- NETWORK CORRECTNESS: compiled circuits compute the network. -/
theorem eval_compileNet {W : Nat} : ∀ (ls : List Layer), NetValid W ls →
    ∀ (prev : Nat → Circ) (x : Nat → Bool) (i : Nat),
      eval x (compileNet W ls prev i) = evalNet ls (fun j => eval x (prev j)) i
  | [], _, prev, x, i => rfl
  | l :: ls, hv, prev, x, i => by
    simp only [compileNet, evalNet]
    rw [eval_compileNet ls (fun l' hl' => hv l' (List.mem_cons_of_mem _ hl'))]
    congr 1
    funext j
    exact eval_compileLayer l (hv l (by simp)) prev x j

/-- Per-layer size factor G = 1 + (M+1)^W (2W+1). -/
def gfac (W M : Nat) : Nat := 1 + (M + 1) ^ W * (2 * W + 1)

/-- Size bound after L layers starting from circuits of size ≤ S. -/
def sizeBound (W M S : Nat) : Nat → Nat
  | 0 => S
  | L + 1 => gfac W M * (sizeBound W M S L + 1)

theorem compileLayer_size {W M S : Nat} (l : Layer) (hb : ∀ g ∈ l, g.fanin ≤ M)
    (prev : Nat → Circ) (hp : ∀ j, size (prev j) ≤ S) (i : Nat) :
    size (compileLayer W l prev i) ≤ gfac W M * (S + 1) := by
  unfold compileLayer
  cases h : l[i]? with
  | none => simp only; simp; have : 1 ≤ gfac W M := by unfold gfac; omega
            exact Nat.le_trans this (Nat.le_mul_of_pos_right _ (by omega))
  | some g =>
    simp only
    have h1 := size_subst_le prev S hp (dnf W g)
    have h2 := size_dnf W g
    have hf := hb g (List.mem_of_getElem? h)
    have h3 : (g.fanin + 1) ^ W ≤ (M + 1) ^ W := Nat.pow_le_pow_left (by omega) W
    have h4 : size (dnf W g) ≤ gfac W M := by
      unfold gfac; have := Nat.mul_le_mul_right (2 * W + 1) h3; omega
    exact Nat.le_trans h1 (Nat.mul_le_mul_right _ h4)

theorem compileLayer_depth {W D : Nat} (l : Layer) (prev : Nat → Circ)
    (hp : ∀ j, depth (prev j) ≤ D) (i : Nat) : depth (compileLayer W l prev i) ≤ D + 3 := by
  unfold compileLayer
  cases h : l[i]? with
  | none => simp
  | some g =>
    simp only
    have h1 := depth_subst_le prev D hp (dnf W g)
    have h2 := depth_dnf W g
    omega

theorem compileLayer_maxInput {W m : Nat} (l : Layer) (prev : Nat → Circ)
    (hp : ∀ j, maxInput (prev j) ≤ m) (i : Nat) : maxInput (compileLayer W l prev i) ≤ m := by
  unfold compileLayer
  cases h : l[i]? with
  | none => simp
  | some g => exact maxInput_subst_le prev m hp (dnf W g)

theorem sizeBound_succ' (W M L S : Nat) :
    sizeBound W M (gfac W M * (S + 1)) L = sizeBound W M S (L + 1) := by
  induction L generalizing S with
  | zero => rfl
  | succ L ih => simp only [sizeBound] at *; rw [ih]

/-- NETWORK SIZE/DEPTH: L = ls.length layers with fan-ins ≤ M, from circuits of size
    ≤ S and depth ≤ D, give circuits of size ≤ sizeBound W M S L and depth ≤ D + 3L. -/
theorem compileNet_sd {W M : Nat} : ∀ (ls : List Layer), NetBounded M ls →
    ∀ (prev : Nat → Circ) (S D : Nat), (∀ j, size (prev j) ≤ S) → (∀ j, depth (prev j) ≤ D) →
      ∀ i, size (compileNet W ls prev i) ≤ sizeBound W M S ls.length ∧
        depth (compileNet W ls prev i) ≤ D + 3 * ls.length
  | [], _, prev, S, D, hs, hd, i => ⟨by simpa [sizeBound] using hs i, by simpa using hd i⟩
  | l :: ls, hb, prev, S, D, hs, hd, i => by
    have hl := hb l (by simp)
    have := compileNet_sd (W := W) ls (fun l' hl' => hb l' (List.mem_cons_of_mem _ hl'))
      (compileLayer W l prev) (gfac W M * (S + 1)) (D + 3)
      (compileLayer_size l hl.2 prev hs) (compileLayer_depth l prev hd) i
    simp only [compileNet, List.length_cons]
    refine ⟨?_, ?_⟩
    · rw [← sizeBound_succ']; exact this.1
    · have := this.2; omega

/-- Compiled circuits read only inputs read by the starting circuits. -/
theorem compileNet_max {W : Nat} : ∀ (ls : List Layer) (prev : Nat → Circ) (m : Nat),
    (∀ j, maxInput (prev j) ≤ m) → ∀ i, maxInput (compileNet W ls prev i) ≤ m
  | [], prev, m, hm, i => hm i
  | l :: ls, prev, m, hm, i => by
    simp only [compileNet]
    exact compileNet_max ls (compileLayer W l prev) m (compileLayer_maxInput l prev hm) i

theorem gfac_le (W M : Nat) : gfac W M + 1 ≤ (2 * W + 3) * (M + 1) ^ W := by
  unfold gfac
  have hp : 1 ≤ (M + 1) ^ W := Nat.pow_pos (by omega)
  generalize (M + 1) ^ W = p at *
  have e1 : p * (2 * W + 1) = 2 * (W * p) + p := by grind
  have e2 : (2 * W + 3) * p = 2 * (W * p) + 3 * p := by grind
  rw [e1, e2]
  omega

theorem pow_step (W M L : Nat) :
    (2 * W + 3) * (M + 1) ^ W * ((2 * W + 3) ^ L * (M + 1) ^ (W * L)) =
      (2 * W + 3) ^ (L + 1) * (M + 1) ^ (W * (L + 1)) := by
  rw [Nat.pow_succ (2 * W + 3) L, show W * (L + 1) = W * L + W by rw [Nat.mul_succ], Nat.pow_add]
  generalize (2 * W + 3) ^ L = A
  generalize (M + 1) ^ (W * L) = B'
  generalize (M + 1) ^ W = C
  generalize 2 * W + 3 = E
  grind

theorem sizeBound_pos (W M L : Nat) {S : Nat} (hS : 1 ≤ S) : 1 ≤ sizeBound W M S L := by
  induction L with
  | zero => simpa [sizeBound]
  | succ L ih =>
    simp only [sizeBound]
    have : 1 ≤ gfac W M := by unfold gfac; omega
    have := Nat.mul_le_mul this (show 1 ≤ sizeBound W M S L + 1 by omega)
    omega

/-- Closed form: sizeBound W M S L + 1 ≤ (S+1) (2W+3)^L (M+1)^(W L). -/
theorem sizeBound_affine (W M L S : Nat) :
    sizeBound W M S L + 1 ≤ (S + 1) * ((2 * W + 3) ^ L * (M + 1) ^ (W * L)) := by
  have hG := gfac_le W M
  induction L with
  | zero =>
    simp only [sizeBound, Nat.pow_zero, Nat.mul_zero, Nat.one_mul]
    omega
  | succ L ih =>
    simp only [sizeBound]
    have h1 : gfac W M * (sizeBound W M S L + 1) + 1 ≤ (gfac W M + 1) * (sizeBound W M S L + 1) := by
      rw [Nat.add_mul, Nat.one_mul]; omega
    have h2 := Nat.mul_le_mul hG ih
    have e : (2 * W + 3) * (M + 1) ^ W * ((S + 1) * ((2 * W + 3) ^ L * (M + 1) ^ (W * L))) =
        (S + 1) * ((2 * W + 3) ^ (L + 1) * (M + 1) ^ (W * (L + 1))) := by
      rw [← pow_step]
      generalize (2 * W + 3) * (M + 1) ^ W = X
      generalize (2 * W + 3) ^ L * (M + 1) ^ (W * L) = Y
      grind
    omega

theorem sizeBound_closed (W M L : Nat) :
    sizeBound W M 1 L + 1 ≤ 2 * ((2 * W + 3) ^ L * (M + 1) ^ (W * L)) := by
  have := sizeBound_affine W M L 1
  omega

/-- FEEDFORWARD SIMULATION THEOREM (one network).  A valid network of L layers with
    all fan-ins and widths ≤ M, on inputs x_0..x_{n-1} (n ≤ M), is computed output by
    output by formulas of depth ≤ 3L and size ≤ 2 (2W+3)^L (M+1)^(W L), reading only
    inputs < n. -/
theorem network_ac0 {W M n : Nat} (ls : List Layer) (hv : NetValid W ls) (hb : NetBounded M ls)
    (i : Nat) :
    (∀ x : Nat → Bool, eval x (compileNet W ls input i) = evalNet ls x i) ∧
    depth (compileNet W ls input i) ≤ 3 * ls.length ∧
    size (compileNet W ls input i) ≤ 2 * ((2 * W + 3) ^ ls.length * (M + 1) ^ (W * ls.length)) ∧
    maxInput (compileNet W ls (fun j => if j < n then input j else const false) i) ≤ n := by
  have hb' := compileNet_sd (W := W) ls hb input 1 0 (fun _ => by simp) (fun _ => by simp) i
  refine ⟨fun x => by rw [eval_compileNet ls hv]; simp, by have := hb'.2; omega, ?_, ?_⟩
  · have := sizeBound_closed W M ls.length; have := hb'.1; omega
  · exact compileNet_max (W := W) ls (fun j => if j < n then input j else const false) n
      (fun j => by
        show maxInput (if j < n then input j else const false) ≤ n
        split <;> simp <;> omega) i

/-- NETWORK-FAMILY SIMULATION.  Fix W, L, c, k.  Let (net n) be valid networks with
    exactly L layers whose fan-ins and widths are ≤ c (n+1)^k.  Then every output of
    net n is computed by a formula of depth ≤ 3L and size
      ≤ 2 (2W+3)^L (c+1)^(W L) (n+1)^(k W L),
    a polynomial in n whose degree k W L and constant depend only on W, L, c, k. -/
theorem family_ac0 {W L c k : Nat} (net : Nat → List Layer) (hlen : ∀ n, (net n).length = L)
    (hv : ∀ n, NetValid W (net n)) (hb : ∀ n, NetBounded (c * (n + 1) ^ k) (net n)) (n i : Nat) :
    (∀ x : Nat → Bool, eval x (compileNet W (net n) input i) = evalNet (net n) x i) ∧
    depth (compileNet W (net n) input i) ≤ 3 * L ∧
    size (compileNet W (net n) input i) ≤
      2 * ((2 * W + 3) ^ L * ((c + 1) ^ (W * L) * (n + 1) ^ (k * (W * L)))) := by
  obtain ⟨h1, h2, h3, _⟩ := network_ac0 (n := 0) (net n) (hv n) (hb n) i
  rw [hlen] at h2 h3
  refine ⟨h1, h2, Nat.le_trans h3 ?_⟩
  apply Nat.mul_le_mul_left
  apply Nat.mul_le_mul_left
  have hM : c * (n + 1) ^ k + 1 ≤ (c + 1) * (n + 1) ^ k := by
    have : 1 ≤ (n + 1) ^ k := Nat.pow_pos (by omega)
    generalize (n + 1) ^ k = p at *
    have e : (c + 1) * p = c * p + p := by rw [Nat.add_mul, Nat.one_mul]
    rw [e]; omega
  calc (c * (n + 1) ^ k + 1) ^ (W * L) ≤ ((c + 1) * (n + 1) ^ k) ^ (W * L) :=
        Nat.pow_le_pow_left hM _
    _ = (c + 1) ^ (W * L) * (n + 1) ^ (k * (W * L)) := by
        rw [Nat.mul_pow, ← Nat.pow_mul, Nat.mul_comm k]

/-! ## Recurrent unrolling with a fixed number of updates -/

/-- A recurrent cell: a network reading input bits x_0..x_{n-1} at indices < n and
    state bits h_0.. at indices n + j, producing the new state at indices j. -/
def cellInput (n : Nat) (x : Nat → Bool) (h : Nat → Bool) : Nat → Bool :=
  fun j => if j < n then x j else h (j - n)

/-- State after t updates from the input-independent initial state h0; the input of
    update t is the global input block x (t*n + j). -/
def rnnState (cell : List Layer) (n : Nat) (h0 : Nat → Bool) (x : Nat → Bool) : Nat → Nat → Bool
  | 0 => h0
  | t + 1 => evalNet cell (cellInput n (fun j => x (t * n + j)) (rnnState cell n h0 x t))

def rnnCirc (W : Nat) (cell : List Layer) (n : Nat) (h0 : Nat → Bool) : Nat → Nat → Circ
  | 0 => fun i => const (h0 i)
  | t + 1 => compileNet W cell
      (fun j => if j < n then input (t * n + j) else rnnCirc W cell n h0 t (j - n))

theorem eval_rnnCirc {W : Nat} (cell : List Layer) (hv : NetValid W cell) (n : Nat)
    (h0 x : Nat → Bool) : ∀ t i, eval x (rnnCirc W cell n h0 t i) = rnnState cell n h0 x t i
  | 0, i => by simp [rnnCirc, rnnState]
  | t + 1, i => by
    simp only [rnnCirc, rnnState]
    rw [eval_compileNet cell hv]
    congr 1
    funext j
    unfold cellInput
    by_cases hj : j < n
    · simp [hj]
    · simp only [hj, if_false]; exact eval_rnnCirc cell hv n h0 x t (j - n)

/-- Size bound after t updates. -/
def rnnSize (W M L : Nat) : Nat → Nat
  | 0 => 1
  | t + 1 => sizeBound W M (rnnSize W M L t) L

theorem rnnSize_pos (W M L t : Nat) : 1 ≤ rnnSize W M L t := by
  induction t with
  | zero => simp [rnnSize]
  | succ t ih => simp only [rnnSize]; exact sizeBound_pos W M L ih

/-- BOUNDED-UNROLLING RECURRENCE (paper Definition RNN-formal with total unrolling T):
    the state after T updates of a valid L-layer cell with fan-ins/widths ≤ M is
    computed by formulas of depth ≤ 3 L T and size ≤ rnnSize W M L T, reading only
    the inputs of the T blocks (indices < T n). -/
theorem rnn_ac0 {W M : Nat} (cell : List Layer) (hv : NetValid W cell) (hb : NetBounded M cell)
    (n : Nat) (h0 : Nat → Bool) : ∀ T i,
    (∀ x : Nat → Bool, eval x (rnnCirc W cell n h0 T i) = rnnState cell n h0 x T i) ∧
    size (rnnCirc W cell n h0 T i) ≤ rnnSize W M cell.length T ∧
    depth (rnnCirc W cell n h0 T i) ≤ 3 * cell.length * T ∧
    maxInput (rnnCirc W cell n h0 T i) ≤ T * n
  | 0, i => ⟨fun x => eval_rnnCirc cell hv n h0 x 0 i, by simp [rnnCirc, rnnSize],
      by simp [rnnCirc], by simp [rnnCirc]⟩
  | T + 1, i => by
    have ih := fun j => rnn_ac0 cell hv hb n h0 T j
    have hp_size : ∀ j, size ((fun j => if j < n then input (T * n + j)
        else rnnCirc W cell n h0 T (j - n)) j) ≤ rnnSize W M cell.length T := by
      intro j; simp only; split
      · simp; exact rnnSize_pos W M cell.length T
      · exact (ih (j - n)).2.1
    have hp_depth : ∀ j, depth ((fun j => if j < n then input (T * n + j)
        else rnnCirc W cell n h0 T (j - n)) j) ≤ 3 * cell.length * T := by
      intro j; simp only; split
      · simp
      · exact (ih (j - n)).2.2.1
    have hp_max : ∀ j, maxInput ((fun j => if j < n then input (T * n + j)
        else rnnCirc W cell n h0 T (j - n)) j) ≤ (T + 1) * n := by
      intro j; simp only; split
      · simp; rw [Nat.succ_mul]; omega
      · have := (ih (j - n)).2.2.2; rw [Nat.succ_mul]; omega
    have hb' := compileNet_sd (W := W) cell hb _ _ _ hp_size hp_depth i
    have hm' := compileNet_max (W := W) cell _ _ hp_max i
    refine ⟨fun x => eval_rnnCirc cell hv n h0 x (T + 1) i, ?_, ?_, ?_⟩
    · simp only [rnnCirc, rnnSize]; exact hb'.1
    · simp only [rnnCirc]; have := hb'.2; rw [Nat.mul_succ]; omega
    · simp only [rnnCirc]; exact hm'

/-- rnnSize is polynomial in M for fixed W, L, T:
    rnnSize W M L T + 1 ≤ (2 (2W+3)^L (M+1)^(W L))^T · 2. -/
theorem sizeBound_mono_S (W M L : Nat) {S S' : Nat} (h : S ≤ S') :
    sizeBound W M S L ≤ sizeBound W M S' L := by
  induction L with
  | zero => simpa [sizeBound]
  | succ L ih => simp only [sizeBound]; exact Nat.mul_le_mul_left _ (by omega)

theorem rnnSize_closed (W M L T : Nat) :
    rnnSize W M L T + 1 ≤ 2 * ((2 * W + 3) ^ L * (M + 1) ^ (W * L)) ^ T := by
  induction T with
  | zero => simp [rnnSize]
  | succ T ih =>
    simp only [rnnSize]
    have h1 := sizeBound_affine W M L (rnnSize W M L T)
    generalize (2 * W + 3) ^ L * (M + 1) ^ (W * L) = X at *
    have h2 := Nat.mul_le_mul_right X ih
    rw [Nat.pow_succ]
    have e : 2 * X ^ T * X = 2 * (X ^ T * X) := Nat.mul_assoc _ _ _
    omega

#print axioms Circ.eval_input
#print axioms Circ.eval_const
#print axioms Circ.eval_not
#print axioms Circ.eval_and
#print axioms Circ.eval_or
#print axioms Circ.size_input
#print axioms Circ.size_const
#print axioms Circ.size_not
#print axioms Circ.size_and
#print axioms Circ.size_or
#print axioms Circ.depth_input
#print axioms Circ.depth_const
#print axioms Circ.depth_not
#print axioms Circ.depth_and
#print axioms Circ.depth_or
#print axioms Circ.maxInput_input
#print axioms Circ.maxInput_const
#print axioms Circ.maxInput_not
#print axioms Circ.maxInput_and
#print axioms Circ.maxInput_or
#print axioms Circ.subst_input
#print axioms Circ.subst_const
#print axioms Circ.subst_not
#print axioms Circ.subst_and
#print axioms Circ.subst_or
#print axioms Circ.le_listMax
#print axioms Circ.listMax_le
#print axioms Circ.all_congr_mem
#print axioms Circ.any_congr_mem
#print axioms Circ.sum_map_le_mem
#print axioms Circ.sum_map_mul_right
#print axioms Circ.eval_subst
#print axioms Circ.size_subst_le
#print axioms Circ.depth_subst_le
#print axioms Circ.size_leaf
#print axioms Circ.depth_leaf
#print axioms Circ.size_subst_leaf
#print axioms Circ.depth_subst_leaf
#print axioms Circ.maxInput_subst_le
#print axioms Circ.eval_congr_below
#print axioms rsum_natCast
#print axioms gate_rat_iff
#print axioms nsum_succ
#print axioms nsum_zero
#print axioms nsum_le
#print axioms nsum_congr
#print axioms nsum_mono
#print axioms nsum_cut
#print axioms length_filter_eq_nsum
#print axioms Gate.psum_succ
#print axioms Gate.psum_mono
#print axioms Gate.active_length_le
#print axioms Gate.exists_cut
#print axioms Gate.bounded_witness
#print axioms eval_litC
#print axioms mem_boards_of
#print axioms length_boards
#print axioms eval_termC
#print axioms eval_dnf
#print axioms size_termC
#print axioms depth_termC
#print axioms maxInput_termC
#print axioms size_dnf
#print axioms depth_dnf
#print axioms maxInput_dnf
#print axioms gate_ac0
#print axioms eval_compileLayer
#print axioms eval_compileNet
#print axioms compileLayer_size
#print axioms compileLayer_depth
#print axioms compileLayer_maxInput
#print axioms sizeBound_succ'
#print axioms compileNet_sd
#print axioms compileNet_max
#print axioms gfac_le
#print axioms pow_step
#print axioms sizeBound_pos
#print axioms sizeBound_affine
#print axioms sizeBound_closed
#print axioms network_ac0
#print axioms family_ac0
#print axioms eval_rnnCirc
#print axioms rnnSize_pos
#print axioms rnn_ac0
#print axioms sizeBound_mono_S
#print axioms rnnSize_closed

end AC0
end NimAudit
