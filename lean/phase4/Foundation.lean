import BitBridge

/- Phase 4, CLASSICAL FOUNDATION (separate, quantitative track).  Written by Claude
   (10 October 2026).  Lean 4.26.0, core/Std only.

   Target.  `Bridge.ParityCorrPremise d s m ε` (every depth-d, size-s formula on m
   inputs has correlation at most ε with parity) remains an explicit HYPOTHESIS of
   every application.  This file proves the finite, probabilistic ENDGAME of the
   random-restriction route and isolates exactly what is left:

   (1) decision trees of depth < m have correlation exactly 0 with parity of m bits
       (`dtree_corr_zero`, via a flip-pairing argument);
   (2) for a fixed star set (mask), the correlation of a formula is at most the
       fraction of fixings ρ for which the restricted formula is NOT certified to be
       a decision tree of depth < #stars (`mask_bound`);
   (3) FINITE PROBABILITY MODEL of p-random restrictions: mask weight
       p^#stars (1-p)^#fixed, ρ uniform; total weight 1 (`maskW_sum`);
   (4) RESTRICTION BOUND: |corr| ≤ Pr_{p-random ρ}[bad] for every p ∈ [0,1] and every
       certificate assignment (`restriction_bound`), hence
       `SwitchingBound d s m p ε → ParityCorrPremise d s m ε` (`premise_of_switching`).

   REMAINING CLASSICAL CONTENT (not proved): `SwitchingBound`, i.e. a bound on the
   probability that a p-random restriction fails to collapse a depth-d, size-s formula
   to a decision tree of depth below the number of surviving variables.  This is what
   Håstad's switching lemma (iterated d−1 times, with a Chernoff bound on the number of
   stars) supplies.  No external proof is imported or claimed. -/

namespace NimAudit
namespace Foundation

open Prob AC0 AC0.Circ Bridge

/-! ## Decision trees and their zero correlation with parity -/

inductive DTree where
  | leaf (b : Bool)
  | node (i : Nat) (t0 t1 : DTree)

namespace DTree

def eval (x : Nat → Bool) : DTree → Bool
  | leaf b => b
  | node i t0 t1 => if x i then eval x t1 else eval x t0

def depth : DTree → Nat
  | leaf _ => 0
  | node _ t0 t1 => max (depth t0) (depth t1) + 1

/-- Root-to-leaf paths (query, answer) with the leaf label. -/
def leaves : DTree → List (List (Nat × Bool) × Bool)
  | leaf b => [([], b)]
  | node i t0 t1 => (leaves t0).map (fun l => ((i, false) :: l.1, l.2)) ++
      (leaves t1).map (fun l => ((i, true) :: l.1, l.2))

end DTree

def sat (x : Nat → Bool) (π : List (Nat × Bool)) : Bool := π.all (fun c => x c.1 == c.2)

theorem rsum_zero' {α : Type} (l : List α) (f : α → Rat) (h : ∀ a ∈ l, f a = 0) : rsum l f = 0 := by
  rw [rsum_congr h, rsum_zero]

theorem ind_eval_leaves (x : Nat → Bool) : ∀ T : DTree,
    ind (T.eval x) = rsum T.leaves (fun l => ind (sat x l.1) * ind l.2)
  | .leaf b => by simp [DTree.eval, DTree.leaves, sat, ind, Rat.add_zero]
  | .node i t0 t1 => by
    simp only [DTree.eval, DTree.leaves, rsum_append, rsum_map]
    cases hx : x i
    · simp only [Bool.false_eq_true, if_false]
      rw [ind_eval_leaves x t0]
      have h1 : rsum t1.leaves (fun l => ind (sat x ((i, true) :: l.1)) * ind l.2) = 0 :=
        rsum_zero' _ _ (fun l _ => by simp [sat, hx, ind])
      rw [h1]
      have h2 : ∀ l ∈ t0.leaves, ind (sat x ((i, false) :: l.1)) * ind l.2 = ind (sat x l.1) * ind l.2 := by
        intro l _; simp [sat, hx]
      rw [rsum_congr h2]; grind
    · simp only [if_true]
      rw [ind_eval_leaves x t1]
      have h1 : rsum t0.leaves (fun l => ind (sat x ((i, false) :: l.1)) * ind l.2) = 0 :=
        rsum_zero' _ _ (fun l _ => by simp [sat, hx, ind])
      rw [h1]
      have h2 : ∀ l ∈ t1.leaves, ind (sat x ((i, true) :: l.1)) * ind l.2 = ind (sat x l.1) * ind l.2 := by
        intro l _; simp [sat, hx]
      rw [rsum_congr h2]; grind

theorem leaves_length : ∀ (T : DTree), ∀ l ∈ T.leaves, l.1.length ≤ T.depth
  | .leaf b => by intro l hl; simp [DTree.leaves] at hl; subst hl; simp
  | .node i t0 t1 => by
    intro l hl
    simp only [DTree.leaves, List.mem_append, List.mem_map] at hl
    rcases hl with ⟨l', hl', rfl⟩ | ⟨l', hl', rfl⟩
    · have := leaves_length t0 l' hl'; simp [DTree.depth]; omega
    · have := leaves_length t1 l' hl'; simp [DTree.depth]; omega

/-- Flip coordinate j. -/
def flipAt : Nat → List Bool → List Bool
  | _, [] => []
  | 0, b :: bs => (!b) :: bs
  | j + 1, b :: bs => b :: flipAt j bs

theorem rsum_flip : ∀ (m j : Nat) (h : List Bool → Rat), j < m →
    rsum (bitvecs m) (fun y => h (flipAt j y)) = rsum (bitvecs m) h
  | 0, _, _, hj => absurd hj (Nat.not_lt_zero _)
  | m + 1, 0, h, _ => by
    rw [rsum_bitvecs_succ, rsum_bitvecs_succ]
    simp only [flipAt, Bool.not_false, Bool.not_true]
    grind
  | m + 1, j + 1, h, hj => by
    rw [rsum_bitvecs_succ, rsum_bitvecs_succ]
    simp only [flipAt]
    rw [rsum_flip m j (fun v => h (false :: v)) (by omega), rsum_flip m j (fun v => h (true :: v)) (by omega)]

theorem par_flipAt : ∀ (j : Nat) (y : List Bool), j < y.length → par (flipAt j y) = !par y
  | _, [], h => by simp at h
  | 0, b :: bs, _ => by simp [flipAt, par]
  | j + 1, b :: bs, h => by
    simp only [flipAt, par]
    rw [par_flipAt j bs (by simpa using h)]
    cases b <;> cases par bs <;> rfl

theorem vfun_flipAt : ∀ (j : Nat) (y : List Bool) (i : Nat), i ≠ j → vfun (flipAt j y) i = vfun y i
  | j, [], _, _ => by cases j <;> rfl
  | 0, b :: bs, i, hij => by
    cases i with
    | zero => exact absurd rfl hij
    | succ i => simp [flipAt, vfun]
  | j + 1, b :: bs, i, hij => by
    cases i with
    | zero => simp [flipAt, vfun]
    | succ i =>
      have := vfun_flipAt j bs i (by omega)
      simpa [flipAt, vfun] using this

theorem sgn_not (b : Bool) : sgn (!b) = -sgn b := by cases b <;> decide

/-- PAIRING: a weight invariant under flipping a coordinate j < m has zero correlation
    with parity of m bits. -/
theorem pairing (m j : Nat) (hj : j < m) (g : List Bool → Rat) (hg : ∀ y, g (flipAt j y) = g y) :
    rsum (bitvecs m) (fun y => g y * sgn (par y)) = 0 := by
  have h1 := rsum_flip m j (fun y => g y * sgn (par y)) hj
  have h2 : rsum (bitvecs m) (fun y => g (flipAt j y) * sgn (par (flipAt j y))) =
      (-1) * rsum (bitvecs m) (fun y => g y * sgn (par y)) := by
    rw [← rsum_mul_left]
    apply rsum_congr; intro y hy
    rw [hg, par_flipAt j y (by rw [mem_bitvecs_length hy]; exact hj), sgn_not]
    grind
  rw [h2] at h1
  grind

theorem exists_not_mem : ∀ (m : Nat) (l : List Nat), l.length < m → ∃ j < m, j ∉ l
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | m + 1, l, h => by
    by_cases hm : m ∈ l
    · have hpos := List.length_pos_of_mem hm
      have hlen : (l.erase m).length < m := by rw [List.length_erase_of_mem hm]; omega
      obtain ⟨j, hj, hnot⟩ := exists_not_mem m (l.erase m) hlen
      refine ⟨j, by omega, fun hjl => hnot ?_⟩
      exact (List.mem_erase_of_ne (by omega)).mpr hjl
    · exact ⟨m, by omega, hm⟩

theorem sat_congr {x x' : Nat → Bool} : ∀ (π : List (Nat × Bool)), (∀ c ∈ π, x c.1 = x' c.1) → sat x π = sat x' π
  | [], _ => rfl
  | c :: π, h => by
    simp only [sat, List.all_cons]
    rw [h c (by simp)]
    have := sat_congr π (fun c' hc' => h c' (by simp [hc']))
    simp only [sat] at this
    rw [this]

/-- DECISION TREES ARE UNCORRELATED WITH PARITY: depth < m ⇒ correlation exactly 0. -/
theorem dtree_corr_zero (T : DTree) (m : Nat) (hT : T.depth < m) :
    rsum (bitvecs m) (fun y => ind (T.eval (vfun y)) * sgn (par y)) = 0 := by
  have e : ∀ y ∈ bitvecs m, ind (T.eval (vfun y)) * sgn (par y) =
      rsum T.leaves (fun l => (ind (sat (vfun y) l.1) * ind l.2) * sgn (par y)) := by
    intro y _
    rw [ind_eval_leaves]
    induction T.leaves with
    | nil => simp
    | cons a l ih => simp only [rsum_cons]; rw [← ih]; grind
  rw [rsum_congr e, rsum_comm]
  apply rsum_zero'
  intro l hl
  obtain ⟨j, hj, hnot⟩ := exists_not_mem m (l.1.map Prod.fst) (by
    rw [List.length_map]; exact Nat.lt_of_le_of_lt (leaves_length T l hl) hT)
  apply pairing m j hj (fun y => ind (sat (vfun y) l.1) * ind l.2)
  intro y
  rw [sat_congr l.1 (fun c hc => vfun_flipAt j y c.1 (by
    intro h; apply hnot; rw [← h]; exact List.mem_map_of_mem hc))]

/-! ## Restrictions: the per-mask bound -/

theorem par_merge : ∀ (mask y ρ : List Bool), y.length = ones mask → ρ.length = zeros mask →
    par (merge mask y ρ) = xor (par y) (par ρ)
  | [], y, ρ, hy, hρ => by
    simp [ones] at hy; simp [zeros] at hρ; subst hy; subst hρ; rfl
  | true :: ms, y, ρ, hy, hρ => by
    cases y with
    | nil => simp [ones] at hy
    | cons b y =>
      simp only [merge, List.headD_cons, List.tail_cons, par]
      rw [par_merge ms y ρ (by simpa [ones] using hy) (by simpa [zeros] using hρ)]
      cases b <;> cases par y <;> cases par ρ <;> rfl
  | false :: ms, y, ρ, hy, hρ => by
    cases ρ with
    | nil => simp [zeros] at hρ
    | cons r ρ =>
      simp only [merge, List.headD_cons, List.tail_cons, par]
      rw [par_merge ms y ρ (by simpa [ones] using hy) (by simpa [zeros] using hρ)]
      cases r <;> cases par y <;> cases par ρ <;> rfl

theorem sgn_xor (a b : Bool) : sgn (xor a b) = sgn a * sgn b := by cases a <;> cases b <;> simp [sgn] <;> grind

/-- A certified shallow decision tree for the restricted formula. -/
def agrees (k : Nat) (T : DTree) (C : Circ) : Bool :=
  decide (T.depth < k) && (bitvecs k).all (fun y => T.eval (vfun y) == eval (vfun y) C)

/-- The bad event for a certificate assignment τ: no certified tree of depth < #stars. -/
def badR (C : Circ) (τ : List Bool → List Bool → Option DTree) (mask ρ : List Bool) : Bool :=
  match τ mask ρ with
  | some T => !(agrees (ones mask) T (restrictC mask ρ C))
  | none => true

theorem inner_good {C : Circ} {k : Nat} {T : DTree} (h : agrees k T C = true) :
    rsum (bitvecs k) (fun y => ind (eval (vfun y) C) * sgn (par y)) = 0 := by
  simp only [agrees, Bool.and_eq_true, decide_eq_true_iff, List.all_eq_true, beq_iff_eq] at h
  rw [← dtree_corr_zero T k h.1]
  apply rsum_congr; intro y hy; rw [h.2 y hy]

theorem ind_bounds (b : Bool) (s : Bool) : -1 ≤ ind b * sgn s ∧ ind b * sgn s ≤ 1 := by
  cases b <;> cases s <;> simp [ind, sgn] <;> decide

/-- PER-MASK BOUND (unnormalised): |Σ_x ind(C x)·(−1)^{par x}| ≤ #bad · 2^#stars. -/
theorem mask_bound (mask : List Bool) (C : Circ) (hC : maxInput C ≤ mask.length)
    (τ : List Bool → List Bool → Option DTree) :
    -(rsum (bitvecs (zeros mask)) (fun ρ => ind (badR C τ mask ρ)) * (2 : Rat) ^ ones mask) ≤
      rsum (bitvecs mask.length) (fun x => ind (eval (vfun x) C) * sgn (par x)) ∧
    rsum (bitvecs mask.length) (fun x => ind (eval (vfun x) C) * sgn (par x)) ≤
      rsum (bitvecs (zeros mask)) (fun ρ => ind (badR C τ mask ρ)) * (2 : Rat) ^ ones mask := by
  rw [rsum_bitvecs_merge]
  have hT := two_pow_pos' (ones mask)
  have hin : ∀ ρ ∈ bitvecs (zeros mask),
      rsum (bitvecs (ones mask)) (fun y => ind (eval (vfun (merge mask y ρ)) C) * sgn (par (merge mask y ρ))) =
      sgn (par ρ) * rsum (bitvecs (ones mask)) (fun y => ind (eval (vfun y) (restrictC mask ρ C)) * sgn (par y)) := by
    intro ρ hρ
    rw [← rsum_mul_left]
    apply rsum_congr; intro y hy
    rw [eval_restrictC hC, par_merge mask y ρ (mem_bitvecs_length hy) (mem_bitvecs_length hρ), sgn_xor]
    grind
  rw [rsum_congr hin]
  have hb : ∀ ρ ∈ bitvecs (zeros mask),
      -(ind (badR C τ mask ρ) * (2 : Rat) ^ ones mask) ≤
        sgn (par ρ) * rsum (bitvecs (ones mask)) (fun y => ind (eval (vfun y) (restrictC mask ρ C)) * sgn (par y)) ∧
      sgn (par ρ) * rsum (bitvecs (ones mask)) (fun y => ind (eval (vfun y) (restrictC mask ρ C)) * sgn (par y)) ≤
        ind (badR C τ mask ρ) * (2 : Rat) ^ ones mask := by
    intro ρ _
    cases hbad : badR C τ mask ρ
    · -- good: a certified tree exists
      have hgood : ∃ T, agrees (ones mask) T (restrictC mask ρ C) = true := by
        unfold badR at hbad
        cases hτ : τ mask ρ with
        | none => rw [hτ] at hbad; cases hbad
        | some T => rw [hτ] at hbad; exact ⟨T, by simpa using hbad⟩
      obtain ⟨T, hT'⟩ := hgood
      rw [inner_good hT']
      refine ⟨?_, ?_⟩ <;> simp [ind] <;> first | decide | rfl
    · obtain ⟨b1, b2⟩ := rsum_bound (l := bitvecs (ones mask))
        (f := fun y => ind (eval (vfun y) (restrictC mask ρ C)) * sgn (par y)) (e := 1)
        (fun y _ => ind_bounds _ _)
      rw [length_bitvecs] at b1 b2
      have c1 : (((2 ^ ones mask : Nat) : Rat)) = (2 : Rat) ^ ones mask := by simp
      rw [c1] at b1 b2
      generalize rsum (bitvecs (ones mask)) (fun y => ind (eval (vfun y) (restrictC mask ρ C)) * sgn (par y)) = X
        at b1 b2 ⊢
      generalize (2 : Rat) ^ ones mask = W at b1 b2 ⊢
      simp only [ind, if_true]
      cases par ρ
      · simp only [sgn, Bool.false_eq_true, if_false]; constructor <;> grind
      · simp only [sgn, if_true]; constructor <;> grind
  have hl : rsum (bitvecs (zeros mask)) (fun ρ => ind (badR C τ mask ρ) * (2 : Rat) ^ ones mask) =
      rsum (bitvecs (zeros mask)) (fun ρ => ind (badR C τ mask ρ)) * (2 : Rat) ^ ones mask := by
    rw [show (fun ρ => ind (badR C τ mask ρ) * (2 : Rat) ^ ones mask) =
      (fun ρ => (2 : Rat) ^ ones mask * ind (badR C τ mask ρ)) from by funext ρ; grind, rsum_mul_left]
    grind
  have hl' : rsum (bitvecs (zeros mask)) (fun ρ => -(ind (badR C τ mask ρ) * (2 : Rat) ^ ones mask)) =
      -(rsum (bitvecs (zeros mask)) (fun ρ => ind (badR C τ mask ρ)) * (2 : Rat) ^ ones mask) := by
    rw [show (fun ρ => -(ind (badR C τ mask ρ) * (2 : Rat) ^ ones mask)) =
      (fun ρ => (-(2 : Rat) ^ ones mask) * ind (badR C τ mask ρ)) from by funext ρ; grind, rsum_mul_left]
    grind
  constructor
  · rw [← hl']; exact rsum_le (fun ρ hρ => (hb ρ hρ).1)
  · rw [← hl]; exact rsum_le (fun ρ hρ => (hb ρ hρ).2)

/-! ## The finite probability model of p-random restrictions -/

/-- Weight of a star set: p^#stars (1 − p)^#fixed. -/
def maskW (p : Rat) (mask : List Bool) : Rat := p ^ ones mask * (1 - p) ^ zeros mask

theorem maskW_sum (p : Rat) : ∀ m, rsum (bitvecs m) (maskW p) = 1
  | 0 => by simp [bitvecs, maskW, ones, zeros, rsum, Rat.add_zero]
  | m + 1 => by
    rw [rsum_bitvecs_succ]
    have h0 : ∀ v, maskW p (false :: v) = (1 - p) * maskW p v := by
      intro v; simp only [maskW, ones, zeros, List.filter_cons, Bool.not_false, if_true, Bool.false_eq_true,
        if_false, List.length_cons, Rat.pow_succ]; grind
    have h1 : ∀ v, maskW p (true :: v) = p * maskW p v := by
      intro v; simp only [maskW, ones, zeros, List.filter_cons, Bool.not_true, if_true, Bool.false_eq_true,
        if_false, List.length_cons, Rat.pow_succ, id]; grind
    simp only [h0, h1, rsum_mul_left, maskW_sum p m]
    grind

theorem pow_nonneg' {a : Rat} (ha : 0 ≤ a) : ∀ n : Nat, 0 ≤ a ^ n
  | 0 => by simp; decide
  | n + 1 => by rw [Rat.pow_succ]; exact Rat.mul_nonneg (pow_nonneg' ha n) ha

theorem maskW_nonneg {p : Rat} (h0 : 0 ≤ p) (h1 : p ≤ 1) (mask : List Bool) : 0 ≤ maskW p mask :=
  Rat.mul_nonneg (pow_nonneg' h0 _) (pow_nonneg' (by grind) _)

/-- Probability of an event E(mask, ρ) under the p-random restriction on m variables. -/
def restrProb (p : Rat) (m : Nat) (E : List Bool → List Bool → Bool) : Rat :=
  rsum (bitvecs m) (fun mask => maskW p mask *
    (rsum (bitvecs (zeros mask)) (fun ρ => ind (E mask ρ)) / (2 : Rat) ^ zeros mask))

/-- Normalised correlation with parity of m bits. -/
def corr (m : Nat) (C : Circ) : Rat :=
  rsum (bitvecs m) (fun x => ind (eval (vfun x) C) * sgn (par x)) / (2 : Rat) ^ m

theorem two_pow_split (mask : List Bool) :
    (2 : Rat) ^ mask.length = (2 : Rat) ^ zeros mask * (2 : Rat) ^ ones mask := by
  have h := ones_add_zeros mask
  have e : ∀ n : Nat, (2 : Rat) ^ n = ((2 ^ n : Nat) : Rat) := by intro n; simp
  rw [e, e, e, ← Rat.natCast_mul, ← Nat.pow_add, ← h, Nat.add_comm]

/-- Normalised per-mask bound. -/
theorem mask_bound_norm (mask : List Bool) (C : Circ) (hC : maxInput C ≤ mask.length)
    (τ : List Bool → List Bool → Option DTree) :
    -(rsum (bitvecs (zeros mask)) (fun ρ => ind (badR C τ mask ρ)) / (2 : Rat) ^ zeros mask) ≤
      corr mask.length C ∧
    corr mask.length C ≤ rsum (bitvecs (zeros mask)) (fun ρ => ind (badR C τ mask ρ)) / (2 : Rat) ^ zeros mask := by
  obtain ⟨b1, b2⟩ := mask_bound mask C hC τ
  unfold corr
  rw [two_pow_split]
  have hT := two_pow_pos' (ones mask)
  have hZ := two_pow_pos' (zeros mask)
  generalize rsum (bitvecs mask.length) (fun x => ind (eval (vfun x) C) * sgn (par x)) = S at b1 b2 ⊢
  generalize rsum (bitvecs (zeros mask)) (fun ρ => ind (badR C τ mask ρ)) = K at b1 b2 ⊢
  have hT' : (2 : Rat) ^ ones mask ≠ 0 := Rat.ne_of_gt hT
  have hZ' : (2 : Rat) ^ zeros mask ≠ 0 := Rat.ne_of_gt hZ
  constructor
  · apply Rat.le_of_mul_le_mul_right _ (Rat.mul_pos hZ hT)
    have e1 : S / ((2 : Rat) ^ zeros mask * (2 : Rat) ^ ones mask) *
        ((2 : Rat) ^ zeros mask * (2 : Rat) ^ ones mask) = S := by grind
    have e2 : -(K / (2 : Rat) ^ zeros mask) * ((2 : Rat) ^ zeros mask * (2 : Rat) ^ ones mask) =
        -(K * (2 : Rat) ^ ones mask) := by grind
    rw [e1, e2]; exact b1
  · apply Rat.le_of_mul_le_mul_right _ (Rat.mul_pos hZ hT)
    have e1 : S / ((2 : Rat) ^ zeros mask * (2 : Rat) ^ ones mask) *
        ((2 : Rat) ^ zeros mask * (2 : Rat) ^ ones mask) = S := by grind
    have e2 : K / (2 : Rat) ^ zeros mask * ((2 : Rat) ^ zeros mask * (2 : Rat) ^ ones mask) =
        K * (2 : Rat) ^ ones mask := by grind
    rw [e1, e2]; exact b2

/-- RESTRICTION BOUND: for every p ∈ [0,1] and every certificate assignment τ, the
    correlation of C with parity of m bits is at most the probability, under the
    p-random restriction, that τ fails to certify a decision tree of depth below the
    number of surviving variables. -/
theorem restriction_bound {p : Rat} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (m : Nat) (C : Circ) (hC : maxInput C ≤ m)
    (τ : List Bool → List Bool → Option DTree) :
    -restrProb p m (badR C τ) ≤ corr m C ∧ corr m C ≤ restrProb p m (badR C τ) := by
  have hsum := maskW_sum p m
  have hc : corr m C = rsum (bitvecs m) (fun mask => maskW p mask * corr m C) := by
    rw [show (fun mask => maskW p mask * corr m C) = (fun mask => corr m C * maskW p mask) from by
      funext mask; grind, rsum_mul_left, hsum]; grind
  have hb : ∀ mask ∈ bitvecs m,
      maskW p mask * -(rsum (bitvecs (zeros mask)) (fun ρ => ind (badR C τ mask ρ)) / (2 : Rat) ^ zeros mask) ≤
        maskW p mask * corr m C ∧
      maskW p mask * corr m C ≤
        maskW p mask * (rsum (bitvecs (zeros mask)) (fun ρ => ind (badR C τ mask ρ)) / (2 : Rat) ^ zeros mask) := by
    intro mask hmask
    have hlen := mem_bitvecs_length hmask
    obtain ⟨k1, k2⟩ := mask_bound_norm mask C (by rw [hlen]; exact hC) τ
    rw [hlen] at k1 k2
    have hw := maskW_nonneg hp0 hp1 mask
    exact ⟨Rat.mul_le_mul_of_nonneg_left k1 hw, Rat.mul_le_mul_of_nonneg_left k2 hw⟩
  have hneg : rsum (bitvecs m) (fun mask => maskW p mask *
      -(rsum (bitvecs (zeros mask)) (fun ρ => ind (badR C τ mask ρ)) / (2 : Rat) ^ zeros mask)) =
      -restrProb p m (badR C τ) := by
    unfold restrProb
    rw [show (fun mask => maskW p mask *
        -(rsum (bitvecs (zeros mask)) (fun ρ => ind (badR C τ mask ρ)) / (2 : Rat) ^ zeros mask)) =
      (fun mask => (-1) * (maskW p mask *
        (rsum (bitvecs (zeros mask)) (fun ρ => ind (badR C τ mask ρ)) / (2 : Rat) ^ zeros mask))) from by
      funext mask; grind, rsum_mul_left]
    grind
  constructor
  · rw [hc, ← hneg]; exact rsum_le (fun mask h => (hb mask h).1)
  · rw [hc]; exact rsum_le (fun mask h => (hb mask h).2)

/-! ## The remaining classical statement and the proved reduction -/

/-- SWITCHING BOUND (the remaining classical content, NOT proved): for every formula of
    depth ≤ d and size ≤ s on m inputs there is a certificate assignment whose failure
    probability under the p-random restriction is at most ε. -/
def SwitchingBound (d s m : Nat) (p ε : Rat) : Prop :=
  ∀ C : Circ, depth C ≤ d → size C ≤ s → maxInput C ≤ m →
    ∃ τ : List Bool → List Bool → Option DTree, restrProb p m (badR C τ) ≤ ε

/-- PROVED REDUCTION: a switching bound yields the parity-correlation premise. -/
theorem premise_of_switching {d s m : Nat} {p ε : Rat} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (h : SwitchingBound d s m p ε) : ParityCorrPremise d s m ε := by
  intro C hd hs hm
  obtain ⟨τ, hτ⟩ := h C hd hs hm
  obtain ⟨b1, b2⟩ := restriction_bound hp0 hp1 m C hm τ
  unfold corr at b1 b2
  constructor
  · exact Rat.le_trans (by grind) b1
  · exact Rat.le_trans b2 hτ

/-- Sanity check of the model: with p = 1 (no fixing) the bad event is "C itself has
    no certified tree of depth < m"; a decision-tree-certified formula has correlation 0. -/
theorem corr_zero_of_tree {m : Nat} {C : Circ} {T : DTree} (h : agrees m T C = true) : corr m C = 0 := by
  unfold corr; rw [inner_good h]; grind


/-! ## Axiom audit -/

#print axioms rsum_zero'
#print axioms ind_eval_leaves
#print axioms leaves_length
#print axioms rsum_flip
#print axioms par_flipAt
#print axioms vfun_flipAt
#print axioms sgn_not
#print axioms pairing
#print axioms exists_not_mem
#print axioms sat_congr
#print axioms dtree_corr_zero
#print axioms par_merge
#print axioms sgn_xor
#print axioms inner_good
#print axioms ind_bounds
#print axioms mask_bound
#print axioms maskW_sum
#print axioms pow_nonneg'
#print axioms maskW_nonneg
#print axioms two_pow_split
#print axioms mask_bound_norm
#print axioms restriction_bound
#print axioms premise_of_switching
#print axioms corr_zero_of_tree
end Foundation
end NimAudit
