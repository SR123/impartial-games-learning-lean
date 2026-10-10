import NimGame

/- Phase 2, target 3.  Written by Claude for the independent review
   (9 October 2026).  Lean 4.26.0, core/Std only (core `Rat`).

   Paper Appendix G(i) as a finite rational-probability theorem.
   Model: q = 2^B, N independent uniform B-bit heaps.  The uniform product
   distribution is the counting measure on `boards q N` (all q^N boards), so
   E[f] = (sum over boards of f) / q^N.

   EXTERNAL INPUT.  `CorrHyp B N F η` is the parity-correlation premise, stated as
   a theorem hypothesis: for every observed bit b, every value a < q and every
   nonzero u < q,  |E[H_{b,a}(P) * chi_u(P)]| <= η.  It is NOT an axiom, and it
   is NOT proved here.  The paper justifies it by AC0 membership of the fixed-b
   readout indicators together with the classical AC0 parity-correlation bound
   (Hastad); that circuit-to-correlation bridge is outside this file.

   Everything else is proved: uniformity of sigma, character orthogonality on
   F_2^B, the exact-value indicator expansion, the per-value error bound,
   disjointness, conditioning on sigma ≠ 0, and the link between legal success
   and g_{ell(sigma)} = sigma. -/

namespace NimAudit
namespace Prob

open Game Rollout

attribute [local simp] Rat.add_zero Rat.zero_add Rat.zero_mul Rat.mul_zero Rat.one_mul
  Rat.neg_mul Rat.mul_neg

/-! ## Finite sums over Rat -/

def rsum {α : Type} (l : List α) (f : α → Rat) : Rat := (l.map f).sum

@[simp] theorem rsum_nil {α : Type} (f : α → Rat) : rsum [] f = 0 := rfl

@[simp] theorem rsum_cons {α : Type} (a : α) (l : List α) (f : α → Rat) :
    rsum (a :: l) f = f a + rsum l f := by
  simp [rsum]

theorem rsum_append {α : Type} (l m : List α) (f : α → Rat) :
    rsum (l ++ m) f = rsum l f + rsum m f := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.cons_append, rsum_cons, ih]; grind

theorem rsum_congr {α : Type} {l : List α} {f g : α → Rat} (h : ∀ x ∈ l, f x = g x) :
    rsum l f = rsum l g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [rsum_cons]
    rw [h a (by simp), ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]

theorem rsum_zero {α : Type} (l : List α) : rsum l (fun _ => 0) = 0 := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

theorem rsum_add {α : Type} (l : List α) (f g : α → Rat) :
    rsum l (fun x => f x + g x) = rsum l f + rsum l g := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [rsum_cons, ih]; grind

theorem rsum_mul_left {α : Type} (l : List α) (c : Rat) (f : α → Rat) :
    rsum l (fun x => c * f x) = c * rsum l f := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [rsum_cons, ih]; grind

theorem rsum_le {α : Type} {l : List α} {f g : α → Rat} (h : ∀ x ∈ l, f x ≤ g x) :
    rsum l f ≤ rsum l g := by
  induction l with
  | nil => exact Rat.le_refl
  | cons a l ih =>
    simp only [rsum_cons]
    have h1 := h a (by simp)
    have h2 := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    grind

theorem rsum_const {α : Type} (l : List α) (c : Rat) :
    rsum l (fun _ => c) = (l.length : Rat) * c := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [rsum_cons, ih, List.length_cons]; grind

theorem rsum_comm {α β : Type} (l : List α) (m : List β) (f : α → β → Rat) :
    rsum l (fun x => rsum m (f x)) = rsum m (fun y => rsum l (fun x => f x y)) := by
  induction l with
  | nil => simp [rsum_zero]
  | cons a l ih => simp only [rsum_cons, ih, rsum_add]

theorem rsum_map {α β : Type} (l : List α) (g : α → β) (f : β → Rat) :
    rsum (l.map g) f = rsum l (fun x => f (g x)) := by
  simp only [rsum, List.map_map]; rfl

theorem rsum_flatMap {α β : Type} (l : List α) (g : α → List β) (f : β → Rat) :
    rsum (l.flatMap g) f = rsum l (fun x => rsum (g x) f) := by
  induction l with
  | nil => simp [rsum]
  | cons a l ih => simp only [List.flatMap_cons, rsum_append, rsum_cons, ih]

theorem rsum_bound {α : Type} {l : List α} {f : α → Rat} {e : Rat}
    (h : ∀ x ∈ l, -e ≤ f x ∧ f x ≤ e) :
    -((l.length : Rat) * e) ≤ rsum l f ∧ rsum l f ≤ (l.length : Rat) * e := by
  induction l with
  | nil => simp only [rsum_nil, List.length_nil]; constructor <;> grind
  | cons a l ih =>
    simp only [rsum_cons, List.length_cons]
    have h1 := h a (by simp)
    have h2 := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    constructor <;> grind

theorem rsum_range_ite (q c : Nat) (v : Nat → Rat) :
    rsum (List.range q) (fun a => if a = c then v a else 0) = if c < q then v c else 0 := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [List.range_succ, rsum_append, ih]
    simp only [rsum_cons, rsum_nil]
    by_cases h1 : c < q
    · have : q ≠ c := by omega
      simp [h1, this, show c < q + 1 by omega]
    · by_cases h2 : c = q
      · subst h2; simp
      · have : q ≠ c := fun e => h2 e.symm
        simp [h1, this, show ¬ c < q + 1 by omega]

/-- Sum over u ≠ 0 of g u, written over `range q` with the u = 0 term removed. -/
def offZero (g : Nat → Rat) (u : Nat) : Rat := if u = 0 then 0 else g u

theorem rsum_range_split0 {q : Nat} (hq : 0 < q) (g : Nat → Rat) :
    rsum (List.range q) g = g 0 + rsum (List.range q) (offZero g) := by
  have e : rsum (List.range q) g =
      rsum (List.range q) (fun u => (if u = 0 then g u else 0) + offZero g u) := by
    apply rsum_congr
    intro u _
    by_cases hu : u = 0 <;> simp [offZero, hu]
  rw [e, rsum_add, rsum_range_ite q 0 g]
  simp [hq]

theorem range_one_add (q : Nat) (hq : 0 < q) :
    List.range q = List.range 1 ++ (List.range (q - 1)).map (1 + ·) := by
  have : q = 1 + (q - 1) := by omega
  conv => lhs; rw [this]
  exact List.range_add

theorem rsum_offZero_bound {q : Nat} (hq : 0 < q) (g : Nat → Rat) (e : Rat)
    (h : ∀ u, 0 < u → u < q → -e ≤ g u ∧ g u ≤ e) :
    -(((q - 1 : Nat) : Rat) * e) ≤ rsum (List.range q) (offZero g) ∧
      rsum (List.range q) (offZero g) ≤ ((q - 1 : Nat) : Rat) * e := by
  rw [range_one_add q hq, rsum_append, rsum_map]
  have h0 : rsum (List.range 1) (offZero g) = 0 := by simp [offZero]
  rw [h0]
  have hb := rsum_bound (l := List.range (q - 1)) (f := fun x => offZero g (1 + x)) (e := e)
    (by
      intro x hx
      have hx' := List.mem_range.mp hx
      simp only [offZero, show 1 + x ≠ 0 by omega, if_false]
      exact h (1 + x) (by omega) (by omega))
  rw [List.length_range] at hb
  constructor <;> grind

theorem rsum_offZero_const {q : Nat} (hq : 0 < q) (c : Rat) :
    rsum (List.range q) (offZero (fun _ => c)) = ((q - 1 : Nat) : Rat) * c := by
  rw [range_one_add q hq, rsum_append, rsum_map]
  have h0 : rsum (List.range 1) (offZero (fun _ => c)) = 0 := by simp [offZero]
  rw [h0]
  have : rsum (List.range (q - 1)) (fun x => offZero (fun _ => c) (1 + x)) =
      rsum (List.range (q - 1)) (fun _ => c) := by
    apply rsum_congr; intro x _; simp [offZero]
  rw [this, rsum_const, List.length_range]
  grind

theorem rsum_offZero_add (q : Nat) (f g : Nat → Rat) :
    rsum (List.range q) (offZero (fun u => f u + g u)) =
      rsum (List.range q) (offZero f) + rsum (List.range q) (offZero g) := by
  rw [← rsum_add]
  apply rsum_congr; intro u _
  by_cases hu : u = 0 <;> simp [offZero, hu]

theorem rsum_offZero_le {q : Nat} {f g : Nat → Rat} (h : ∀ u, 0 < u → u < q → f u ≤ g u) :
    rsum (List.range q) (offZero f) ≤ rsum (List.range q) (offZero g) := by
  apply rsum_le
  intro u hu
  have hu' := List.mem_range.mp hu
  by_cases h0 : u = 0
  · simp [offZero, h0]; exact Rat.le_refl
  · simp only [offZero, h0, if_false]; exact h u (by omega) hu'

/-! ## The uniform model on boards -/

/-- All boards of N heaps with values below q (each exactly once). -/
def boards (q : Nat) : Nat → List (List Nat)
  | 0 => [[]]
  | N + 1 => (List.range q).flatMap (fun h => (boards q N).map (h :: ·))

theorem mem_boards {q N : Nat} {P : List Nat} (h : P ∈ boards q N) :
    P.length = N ∧ ∀ x ∈ P, x < q := by
  induction N generalizing P with
  | zero => simp [boards] at h; subst h; simp
  | succ N ih =>
    simp only [boards, List.mem_flatMap, List.mem_range, List.mem_map] at h
    obtain ⟨x, hx, P', hP', rfl⟩ := h
    obtain ⟨h1, h2⟩ := ih hP'
    refine ⟨by simp [h1], ?_⟩
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact hx
    · exact h2 y hy

theorem rsum_boards_succ (q N : Nat) (f : List Nat → Rat) :
    rsum (boards q (N + 1)) f =
      rsum (List.range q) (fun h => rsum (boards q N) (fun P => f (h :: P))) := by
  simp only [boards, rsum_flatMap, rsum_map]

/-- There are q^N boards. -/
theorem count_boards (q N : Nat) : rsum (boards q N) (fun _ => 1) = (q : Rat) ^ N := by
  induction N with
  | zero => simp [boards]
  | succ N ih =>
    rw [rsum_boards_succ, rsum_congr (g := fun _ => (q : Rat) ^ N) (fun h _ => ih),
      rsum_const, List.length_range]
    grind

theorem xor_eq_iff (h s a : Nat) : (h ^^^ s = a) ↔ (s = h ^^^ a) := by
  constructor
  · intro e; rw [← e, xor_cancel_left]
  · intro e; rw [e, xor_cancel_left]

/-- UNIFORMITY OF SIGMA: for N ≥ 1 (written N + 1) and every a < 2^B, exactly
    q^N of the q^(N+1) boards have nim-sum a. -/
theorem sigma_uniform (B N a : Nat) (ha : a < 2 ^ B) :
    rsum (boards (2 ^ B) (N + 1)) (fun P => if nimSum P = a then 1 else 0) =
      ((2 ^ B : Nat) : Rat) ^ N := by
  induction N generalizing a with
  | zero =>
    rw [rsum_boards_succ]
    simp only [boards, rsum_cons, rsum_nil, nimSum, Nat.xor_zero, Rat.add_zero]
    rw [rsum_range_ite (2 ^ B) a (fun _ => 1)]
    simp [ha]
  | succ N ih =>
    rw [rsum_boards_succ]
    have : ∀ h ∈ List.range (2 ^ B),
        rsum (boards (2 ^ B) (N + 1)) (fun P => if nimSum (h :: P) = a then 1 else 0) =
          ((2 ^ B : Nat) : Rat) ^ N := by
      intro h hh
      have hlt : h ^^^ a < 2 ^ B := Nat.xor_lt_two_pow (List.mem_range.mp hh) ha
      rw [← ih (h ^^^ a) hlt]
      apply rsum_congr
      intro P _
      simp only [nimSum, xor_eq_iff]
    rw [rsum_congr this, rsum_const, List.length_range]
    grind

/-! ## Characters on F_2^B -/

/-- The F_2 inner product of the first B bits of u and v. -/
def dotB : Nat → Nat → Nat → Bool
  | 0, _, _ => false
  | B + 1, u, v => xor (dotB B u v) (u.testBit B && v.testBit B)

/-- chi_u(v) = (-1)^<u,v>. -/
def chi (B u v : Nat) : Rat := if dotB B u v then -1 else 1

theorem dotB_xor_right (B u v w : Nat) :
    dotB B u (v ^^^ w) = xor (dotB B u v) (dotB B u w) := by
  induction B with
  | zero => rfl
  | succ B ih =>
    simp only [dotB, ih, Nat.testBit_xor]
    cases dotB B u v <;> cases dotB B u w <;> cases u.testBit B <;>
      cases v.testBit B <;> cases w.testBit B <;> rfl

theorem dotB_xor_left (B u w v : Nat) :
    dotB B (u ^^^ w) v = xor (dotB B u v) (dotB B w v) := by
  induction B with
  | zero => rfl
  | succ B ih =>
    simp only [dotB, ih, Nat.testBit_xor]
    cases dotB B u v <;> cases dotB B w v <;> cases u.testBit B <;>
      cases w.testBit B <;> cases v.testBit B <;> rfl

theorem dotB_zero_left (B v : Nat) : dotB B 0 v = false := by
  induction B with
  | zero => rfl
  | succ B ih => simp [dotB, ih]

theorem dotB_congr_left {B u u' : Nat} (v : Nat) (h : ∀ i < B, u.testBit i = u'.testBit i) :
    dotB B u v = dotB B u' v := by
  induction B with
  | zero => rfl
  | succ B ih =>
    simp only [dotB]
    rw [ih (fun i hi => h i (by omega)), h B (by omega)]

theorem chi_xor_right (B u v w : Nat) : chi B u (v ^^^ w) = chi B u v * chi B u w := by
  unfold chi
  rw [dotB_xor_right]
  cases dotB B u v <;> cases dotB B u w <;> simp <;> grind

theorem chi_zero_left (B v : Nat) : chi B 0 v = 1 := by
  simp [chi, dotB_zero_left]

theorem chi_cases (B u v : Nat) : chi B u v = 1 ∨ chi B u v = -1 := by
  unfold chi; split <;> simp

/-- Bits 0..B-1 of v are all zero. -/
def lowZero : Nat → Nat → Bool
  | 0, _ => true
  | B + 1, v => lowZero B v && !v.testBit B

theorem lowZero_spec (B v : Nat) : lowZero B v = true ↔ ∀ i < B, v.testBit i = false := by
  induction B with
  | zero => simp [lowZero]
  | succ B ih =>
    show (lowZero B v && !v.testBit B) = true ↔ _
    cases h2 : v.testBit B
    · simp only [Bool.not_false, Bool.and_true]
      rw [ih]
      constructor
      · intro h i hi
        by_cases hiB : i = B
        · subst hiB; exact h2
        · exact h i (by omega)
      · intro h i hi; exact h i (by omega)
    · simp only [Bool.not_true, Bool.and_false]
      constructor
      · intro h; cases h
      · intro h; have := h B (by omega); rw [h2] at this; cases this

theorem lowZero_iff {B v : Nat} (hv : v < 2 ^ B) : lowZero B v = true ↔ v = 0 := by
  rw [lowZero_spec]
  constructor
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.zero_testBit]
    by_cases hi : i < B
    · exact h i hi
    · exact Nat.testBit_lt_two_pow
        (Nat.lt_of_lt_of_le hv (Nat.pow_le_pow_right (by decide) (by omega)))
  · rintro rfl i _; exact Nat.zero_testBit i

/-- CHARACTER ORTHOGONALITY on F_2^B. -/
theorem orthogonality (B v : Nat) :
    rsum (List.range (2 ^ B)) (fun u => chi B u v) =
      if lowZero B v then ((2 ^ B : Nat) : Rat) else 0 := by
  induction B with
  | zero => simp [chi, dotB, lowZero]
  | succ B ih =>
    have hsplit : List.range (2 ^ (B + 1)) =
        List.range (2 ^ B) ++ (List.range (2 ^ B)).map (2 ^ B + ·) := by
      rw [show 2 ^ (B + 1) = 2 ^ B + 2 ^ B by rw [Nat.pow_succ]; omega]
      exact List.range_add
    rw [hsplit, rsum_append, rsum_map]
    have e1 : rsum (List.range (2 ^ B)) (fun u => chi (B + 1) u v) =
        rsum (List.range (2 ^ B)) (fun u => chi B u v) := by
      apply rsum_congr
      intro u hu
      have hu' : u.testBit B = false := Nat.testBit_lt_two_pow (List.mem_range.mp hu)
      simp [chi, dotB, hu']
    have e2 : rsum (List.range (2 ^ B)) (fun u => chi (B + 1) (2 ^ B + u) v) =
        rsum (List.range (2 ^ B)) (fun u => (if v.testBit B then -1 else 1) * chi B u v) := by
      apply rsum_congr
      intro u hu
      have hu' : u.testBit B = false := Nat.testBit_lt_two_pow (List.mem_range.mp hu)
      have hc : dotB B (2 ^ B + u) v = dotB B u v :=
        dotB_congr_left v (fun i hi => Nat.testBit_two_pow_add_gt hi u)
      have ht : (2 ^ B + u).testBit B = true := by
        rw [Nat.testBit_two_pow_add_eq, hu']; rfl
      simp only [chi, dotB, hc, ht, Bool.true_and]
      cases dotB B u v <;> cases v.testBit B <;> simp <;> grind
    rw [e1, e2, rsum_mul_left, ih]
    show _ = if (lowZero B v && !v.testBit B) = true then _ else _
    by_cases hb : v.testBit B = true <;> by_cases hl : lowZero B v = true <;>
      simp [hb, hl, Nat.pow_succ] <;> grind

/-- EXACT-VALUE INDICATOR EXPANSION: q * 1[s = a] = sum_u chi_u(a) chi_u(s). -/
theorem indicator_expansion {B a s : Nat} (ha : a < 2 ^ B) (hs : s < 2 ^ B) :
    rsum (List.range (2 ^ B)) (fun u => chi B u a * chi B u s) =
      if s = a then ((2 ^ B : Nat) : Rat) else 0 := by
  rw [rsum_congr (g := fun u => chi B u (a ^^^ s)) (fun u _ => (chi_xor_right B u a s).symm),
    orthogonality]
  have hlt : a ^^^ s < 2 ^ B := Nat.xor_lt_two_pow ha hs
  by_cases h : s = a
  · subst h
    have h0 : lowZero B 0 = true := (lowZero_iff (Nat.two_pow_pos B)).2 rfl
    simp [h0]
  · have : lowZero B (a ^^^ s) = false := by
      cases hl : lowZero B (a ^^^ s)
      · rfl
      · exact absurd ((xor_eq_zero_imp ((lowZero_iff hlt).1 hl)).symm) h
    simp [this, h]

/-! ## Readouts, legal success and g_b -/

/-- A readout: from board P and observed bit b, a proposed move (heap index i, new
    value v), or `none` (invalid output).  No circuit restriction is imposed here;
    the only property ever used is the correlation premise `CorrHyp`. -/
abbrev Readout := List Nat → Bool → Option (Nat × Nat)

/-- g_b(P): old heap XOR new value for a legal proposed move; 0 for invalid output. -/
def gval (F : Readout) (b : Bool) (P : List Nat) : Nat :=
  match F P b with
  | some (i, v) =>
    match P[i]? with
    | some x => if v < x then x ^^^ v else 0
    | none => 0
  | none => 0

/-- H_{b,a}(P) = 1[g_b(P) = a]. -/
def H (F : Readout) (b : Bool) (a : Nat) (P : List Nat) : Rat :=
  if gval F b P = a then 1 else 0

/-- Legal success: the proposed move is legal and leaves nim-sum zero. -/
def Success (F : Readout) (b : Bool) (P : List Nat) : Prop :=
  ∃ i v x, F P b = some (i, v) ∧ P[i]? = some x ∧ v < x ∧ nimSum (P.set i v) = 0

/-- Decidable form of `Success`. -/
def successB (F : Readout) (b : Bool) (P : List Nat) : Bool :=
  match F P b with
  | some (i, v) =>
    match P[i]? with
    | some x => decide (v < x) && decide (nimSum (P.set i v) = 0)
    | none => false
  | none => false

theorem successB_iff (F : Readout) (b : Bool) (P : List Nat) :
    successB F b P = true ↔ Success F b P := by
  unfold successB Success
  cases hF : F P b with
  | none => simp
  | some iv =>
    obtain ⟨i, v⟩ := iv
    cases hx : P[i]? with
    | none =>
      simp only [hx]
      constructor
      · intro h; cases h
      · rintro ⟨i', v', x', h1, h2, _⟩
        simp only [Option.some.injEq, Prod.mk.injEq] at h1
        obtain ⟨rfl, rfl⟩ := h1
        rw [hx] at h2; cases h2
    | some x =>
      simp only [hx, Bool.and_eq_true, decide_eq_true_eq]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨i, v, x, rfl, hx, h1, h2⟩
      · rintro ⟨i', v', x', h1, h2, h3, h4⟩
        simp only [Option.some.injEq, Prod.mk.injEq] at h1
        obtain ⟨rfl, rfl⟩ := h1
        rw [hx, Option.some.injEq] at h2
        subst h2
        exact ⟨h3, h4⟩

theorem nimSum_set {P : List Nat} {i x : Nat} (v : Nat) (h : P[i]? = some x) :
    nimSum (P.set i v) = nimSum P ^^^ x ^^^ v := by
  induction P generalizing i with
  | nil => simp at h
  | cons y t ih =>
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      simpa using one_heap_update [] t y v
    | succ k =>
      simp only [List.getElem?_cons_succ] at h
      simp only [List.set_cons_succ, nimSum, ih h, Nat.xor_assoc]

/-- A legally proposed (index, value) is an ordinary legal Nim move. -/
theorem set_move {P : List Nat} {i x v : Nat} (h : P[i]? = some x) (hv : v < x) :
    Move P (P.set i v) := by
  induction P generalizing i with
  | nil => simp at h
  | cons y t ih =>
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      exact ⟨[], y, t, v, rfl, rfl, hv⟩
    | succ k =>
      simp only [List.getElem?_cons_succ] at h
      obtain ⟨pre, z, post, w, h1, h2, h3⟩ := ih h
      refine ⟨y :: pre, z, post, w, by simp [h1], ?_, h3⟩
      simp [h2]

/-- Success is a legal Nim move to a zero-nim-sum board. -/
theorem success_legal {F : Readout} {b : Bool} {P : List Nat} (h : Success F b P) :
    ∃ Q, Move P Q ∧ nimSum Q = 0 := by
  obtain ⟨i, v, x, _, hx, hv, hz⟩ := h
  exact ⟨_, set_move hx hv, hz⟩

/-- Invalid outputs are never successes and have g = 0. -/
theorem invalid_output {F : Readout} {b : Bool} {P : List Nat} (h : F P b = none) :
    successB F b P = false ∧ gval F b P = 0 := by
  simp [successB, gval, h]

/-- SUCCESS ↔ g_b(P) = sigma(P), on boards with sigma ≠ 0. -/
theorem success_iff_gval {F : Readout} {b : Bool} {P : List Nat} (hs : nimSum P ≠ 0) :
    successB F b P = true ↔ gval F b P = nimSum P := by
  unfold successB gval
  cases hF : F P b with
  | none =>
    constructor
    · intro h; cases h
    · intro h; exact absurd h.symm hs
  | some iv =>
    obtain ⟨i, v⟩ := iv
    cases hx : P[i]? with
    | none =>
      simp only [hx]
      constructor
      · intro h; cases h
      · intro h; exact absurd h.symm hs
    | some x =>
      simp only [hx]
      by_cases hv : v < x
      · simp only [hv, decide_true, Bool.true_and, if_true, decide_eq_true_eq]
        rw [nimSum_set v hx, Nat.xor_assoc]
        constructor
        · intro h; exact (xor_eq_zero_imp h).symm
        · intro h; rw [h]; exact Nat.xor_self _
      · simp only [hv, decide_false, Bool.false_and, if_false]
        constructor
        · intro h; cases h
        · intro h; exact absurd h.symm hs

/-! ## Expectations and the correlation premise -/

/-- Number of boards, q^N. -/
def T (B N : Nat) : Rat := ((2 ^ B : Nat) : Rat) ^ N

/-- Expectation under N independent uniform B-bit heaps. -/
def expect (B N : Nat) (f : List Nat → Rat) : Rat := rsum (boards (2 ^ B) N) f / T B N

/-- E[H_{b,a}(P) chi_u(P)], where chi_u(P) = (-1)^<u, sigma(P)>. -/
def corr (B N : Nat) (F : Readout) (b : Bool) (a u : Nat) : Rat :=
  expect B N (fun P => H F b a P * chi B u (nimSum P))

/-- THE IMPORTED PARITY-CORRELATION PREMISE, as a predicate used only as a theorem
    hypothesis: |E[H_{b,a} chi_u]| ≤ η for every b, every a < q and every nonzero
    u < q.  (Not an axiom; not proved here.) -/
def CorrHyp (B N : Nat) (F : Readout) (η : Rat) : Prop :=
  ∀ (b : Bool) (a u : Nat), a < 2 ^ B → 0 < u → u < 2 ^ B →
    -η ≤ corr B N F b a u ∧ corr B N F b a u ≤ η

theorem q_pos (B : Nat) : (0 : Rat) < ((2 ^ B : Nat) : Rat) :=
  Rat.natCast_pos.mpr (Nat.two_pow_pos B)

theorem T_eq (B N : Nat) : T B N = (((2 ^ B) ^ N : Nat) : Rat) := by
  simp [T]

theorem T_pos (B N : Nat) : 0 < T B N := by
  rw [T_eq]; exact Rat.natCast_pos.mpr (Nat.pow_pos (Nat.two_pow_pos B))

theorem rsum_boards_eq_T (B N : Nat) : rsum (boards (2 ^ B) N) (fun _ => 1) = T B N := by
  rw [count_boards]; rfl

theorem div_mul_cancel' {x d : Rat} (hd : d ≠ 0) : x / d * d = x := by grind

theorem div_le_div_of_le {x y d : Rat} (hd : 0 < d) (h : x ≤ y) : x / d ≤ y / d := by
  have hd' : d ≠ 0 := by grind
  apply Rat.le_of_mul_le_mul_right _ hd
  rw [div_mul_cancel' hd', div_mul_cancel' hd']
  exact h

theorem le_div_of_mul_le {x y d : Rat} (hd : 0 < d) (h : x ≤ y * d) : x / d ≤ y := by
  have hd' : d ≠ 0 := by grind
  apply Rat.le_of_mul_le_mul_right _ hd
  rw [div_mul_cancel' hd']
  exact h

theorem sigma_lt {B N : Nat} {P : List Nat} (h : P ∈ boards (2 ^ B) N) : nimSum P < 2 ^ B :=
  nimSum_lt (mem_boards h).2

/-- Raw character sums C_{b,a,u} = sum_P H_{b,a}(P) chi_u(P). -/
def Csum (B N : Nat) (F : Readout) (b : Bool) (a u : Nat) : Rat :=
  rsum (boards (2 ^ B) N) (fun P => H F b a P * chi B u (nimSum P))

theorem Csum_bound {B N : Nat} {F : Readout} {η : Rat} (hyp : CorrHyp B N F η)
    (b : Bool) {a u : Nat} (ha : a < 2 ^ B) (hu0 : 0 < u) (hu : u < 2 ^ B) :
    -(η * T B N) ≤ Csum B N F b a u ∧ Csum B N F b a u ≤ η * T B N := by
  obtain ⟨h1, h2⟩ := hyp b a u ha hu0 hu
  have hT := T_pos B N
  have hT' : T B N ≠ 0 := by grind
  have e : corr B N F b a u * T B N = Csum B N F b a u := by
    unfold corr expect Csum; exact div_mul_cancel' hT'
  have k1 := Rat.mul_le_mul_of_nonneg_right h1 (Rat.le_of_lt hT)
  have k2 := Rat.mul_le_mul_of_nonneg_right h2 (Rat.le_of_lt hT)
  rw [e] at k1 k2
  constructor <;> grind

/-- A_{b,a} = sum_P H_{b,a}(P) 1[sigma(P) = a]. -/
def Aval (B N : Nat) (F : Readout) (b : Bool) (a : Nat) : Rat :=
  rsum (boards (2 ^ B) N) (fun P => H F b a P * (if nimSum P = a then 1 else 0))

/-- C0_{b,a} = sum_P H_{b,a}(P). -/
def C0val (B N : Nat) (F : Readout) (b : Bool) (a : Nat) : Rat :=
  rsum (boards (2 ^ B) N) (fun P => H F b a P)

theorem natCast_pred (B : Nat) : (((2 ^ B - 1 : Nat) : Rat)) = ((2 ^ B : Nat) : Rat) - 1 := by
  have h : 2 ^ B - 1 + 1 = 2 ^ B := by have := Nat.two_pow_pos B; omega
  have h' : (((2 ^ B - 1 + 1 : Nat)) : Rat) = ((2 ^ B : Nat) : Rat) := by rw [h]
  rw [Rat.natCast_add] at h'
  grind

/-- EXACT-VALUE ERROR (counting form):
    |q * A_{b,a} - C0_{b,a}| ≤ (q-1) * η * q^N. -/
theorem exact_value_count {B N : Nat} {F : Readout} {η : Rat} (hyp : CorrHyp B N F η)
    (b : Bool) {a : Nat} (ha : a < 2 ^ B) :
    -(((2 ^ B - 1 : Nat) : Rat) * (η * T B N)) ≤
        ((2 ^ B : Nat) : Rat) * Aval B N F b a - C0val B N F b a ∧
      ((2 ^ B : Nat) : Rat) * Aval B N F b a - C0val B N F b a ≤
        ((2 ^ B - 1 : Nat) : Rat) * (η * T B N) := by
  have hq : 0 < 2 ^ B := Nat.two_pow_pos B
  -- step 1: expand the exact-value indicator into characters
  have step1 : ((2 ^ B : Nat) : Rat) * Aval B N F b a =
      rsum (boards (2 ^ B) N) (fun P => rsum (List.range (2 ^ B))
        (fun u => chi B u a * (H F b a P * chi B u (nimSum P)))) := by
    unfold Aval
    rw [← rsum_mul_left]
    apply rsum_congr
    intro P hP
    have hexp := indicator_expansion ha (sigma_lt hP)
    have e : rsum (List.range (2 ^ B)) (fun u => chi B u a * (H F b a P * chi B u (nimSum P))) =
        H F b a P * rsum (List.range (2 ^ B)) (fun u => chi B u a * chi B u (nimSum P)) := by
      rw [← rsum_mul_left]; apply rsum_congr; intro u _; grind
    rw [e, hexp]
    by_cases h : nimSum P = a <;> simp [h] <;> grind
  -- step 2: swap sums
  have step2 : ((2 ^ B : Nat) : Rat) * Aval B N F b a =
      rsum (List.range (2 ^ B)) (fun u => chi B u a * Csum B N F b a u) := by
    rw [step1, rsum_comm]
    apply rsum_congr; intro u _
    unfold Csum; rw [rsum_mul_left]
  -- step 3: separate u = 0
  have hC0 : Csum B N F b a 0 = C0val B N F b a := by
    unfold Csum C0val; apply rsum_congr; intro P _; simp [chi_zero_left]
  rw [step2, rsum_range_split0 hq, chi_zero_left, hC0]
  -- step 4: bound the nonzero characters
  have hb := rsum_offZero_bound hq (fun u => chi B u a * Csum B N F b a u) (η * T B N)
    (by
      intro u hu0 hu
      obtain ⟨k1, k2⟩ := Csum_bound hyp b ha hu0 hu
      show -(η * T B N) ≤ chi B u a * Csum B N F b a u ∧ chi B u a * Csum B N F b a u ≤ η * T B N
      rcases chi_cases B u a with hc | hc <;> rw [hc] <;> constructor <;> grind)
  constructor <;> grind

/-- EXACT-VALUE ERROR (expectation form, as in the brief), with q = 2^B:
    |E[H_{b,a} 1[sigma = a]] - (1/q) E[H_{b,a}]| ≤ ((q-1)/q) η. -/
theorem exact_value_error {B N : Nat} {F : Readout} {η : Rat} (hyp : CorrHyp B N F η)
    (b : Bool) {a : Nat} (ha : a < 2 ^ B) :
    -((((2 ^ B : Nat) : Rat) - 1) / ((2 ^ B : Nat) : Rat) * η) ≤
        expect B N (fun P => H F b a P * (if nimSum P = a then 1 else 0)) -
          (1 / ((2 ^ B : Nat) : Rat)) * expect B N (fun P => H F b a P) ∧
      expect B N (fun P => H F b a P * (if nimSum P = a then 1 else 0)) -
          (1 / ((2 ^ B : Nat) : Rat)) * expect B N (fun P => H F b a P) ≤
        (((2 ^ B : Nat) : Rat) - 1) / ((2 ^ B : Nat) : Rat) * η := by
  obtain ⟨k1, k2⟩ := exact_value_count hyp b ha
  rw [natCast_pred] at k1 k2
  have hq := q_pos B
  have hT := T_pos B N
  have hqT : 0 < ((2 ^ B : Nat) : Rat) * T B N := Rat.mul_pos hq hT
  have hq' : ((2 ^ B : Nat) : Rat) ≠ 0 := Rat.ne_of_gt hq
  have hT' : T B N ≠ 0 := Rat.ne_of_gt hT
  have d1 := div_le_div_of_le hqT k1
  have d2 := div_le_div_of_le hqT k2
  unfold expect
  unfold Aval C0val at d1 d2
  generalize rsum (boards (2 ^ B) N) (fun P => H F b a P * (if nimSum P = a then 1 else 0)) = A
    at d1 d2 ⊢
  generalize rsum (boards (2 ^ B) N) (fun P => H F b a P) = C at d1 d2 ⊢
  generalize T B N = t at *
  generalize ((2 ^ B : Nat) : Rat) = q at *
  have e1 : (q * A - C) / (q * t) = A / t - 1 / q * (C / t) := by grind
  have e2 : (q - 1) * (η * t) / (q * t) = (q - 1) / q * η := by grind
  have e3 : -((q - 1) * (η * t)) / (q * t) = -((q - 1) / q * η) := by grind
  rw [e1, e2] at d2
  rw [e1, e3] at d1
  exact ⟨d1, d2⟩

/-! ## Success, disjointness and conditioning -/

/-- Number of boards with sigma ≠ 0 on which the readout, fed b = ell_w(sigma),
    makes a legal move to nim-sum zero. -/
def succCount (B N : Nat) (F : Readout) (w : Nat) : Rat :=
  rsum (boards (2 ^ B) N)
    (fun P => if nimSum P ≠ 0 ∧ successB F (dotB B w (nimSum P)) P = true then 1 else 0)

/-- Number of boards with sigma ≠ 0. -/
def nonzeroCount (B N : Nat) : Rat :=
  rsum (boards (2 ^ B) N) (fun P => if nimSum P ≠ 0 then 1 else 0)

theorem offZero_rsum {α : Type} (l : List α) (X : Nat → α → Rat) (a : Nat) :
    offZero (fun a => rsum l (X a)) a = rsum l (fun P => offZero (fun a => X a P) a) := by
  by_cases h : a = 0
  · simp [offZero, h, rsum_zero]
  · simp [offZero, h]

theorem rsum_offZero_indicator {q σ : Nat} (hσ : σ < q) (f : Nat → Rat) :
    rsum (List.range q) (offZero (fun a => f a * (if σ = a then 1 else 0))) = offZero f σ := by
  rw [rsum_congr (g := fun a => if a = σ then offZero f a else 0)]
  · rw [rsum_range_ite]; simp [hσ]
  · intro a _
    by_cases h : a = σ
    · subst h; by_cases h0 : a = 0 <;> simp [offZero, h0]
    · have : σ ≠ a := fun e => h e.symm
      by_cases h0 : a = 0 <;> simp [offZero, h0, h, this]

theorem rsum_range_indicator_le (q c : Nat) :
    rsum (List.range q) (fun a => if a = c then 1 else 0) ≤ 1 := by
  rw [rsum_range_ite q c (fun _ => 1)]
  split <;> grind

/-- (S1) The success count as a sum of exact-value terms. -/
theorem succCount_eq (B N : Nat) (F : Readout) (w : Nat) :
    succCount B N F w =
      rsum (List.range (2 ^ B)) (offZero (fun a => Aval B N F (dotB B w a) a)) := by
  unfold Aval
  rw [rsum_congr (fun a _ => offZero_rsum _ _ a), ← rsum_comm]
  unfold succCount
  apply rsum_congr
  intro P hP
  have hσ := sigma_lt hP
  have e := rsum_offZero_indicator hσ (fun a => H F (dotB B w a) a P)
  have e' : rsum (List.range (2 ^ B))
        (fun a => offZero (fun a => H F (dotB B w a) a P *
          (if nimSum P = a then 1 else 0)) a) =
      rsum (List.range (2 ^ B))
        (offZero (fun a => H F (dotB B w a) a P * (if nimSum P = a then 1 else 0))) := rfl
  rw [e', e]
  by_cases h0 : nimSum P = 0
  · simp [offZero, h0]
  · have hs := success_iff_gval (F := F) (b := dotB B w (nimSum P)) h0
    simp only [offZero, h0, if_false, H, ne_eq, not_false_eq_true, true_and]
    by_cases hg : gval F (dotB B w (nimSum P)) P = nimSum P
    · simp [hg, hs.2 hg]
    · have : ¬ successB F (dotB B w (nimSum P)) P = true := fun h => hg (hs.1 h)
      simp [hg, this]

/-- (S3) Disjointness: for each board, at most two values a ≠ 0 satisfy
    g_{ell(a)}(P) = a (one for each observed bit). -/
theorem disjoint_le_two (B : Nat) (F : Readout) (w : Nat) (P : List Nat) :
    rsum (List.range (2 ^ B)) (offZero (fun a => H F (dotB B w a) a P)) ≤ 2 := by
  have hle : rsum (List.range (2 ^ B)) (offZero (fun a => H F (dotB B w a) a P)) ≤
      rsum (List.range (2 ^ B)) (fun a => (if a = gval F false P then 1 else 0) +
        (if a = gval F true P then 1 else 0)) := by
    apply rsum_le
    intro a _
    have n1 : (0 : Rat) ≤ if a = gval F false P then 1 else 0 := by split <;> grind
    have n2 : (0 : Rat) ≤ if a = gval F true P then 1 else 0 := by split <;> grind
    by_cases h0 : a = 0
    · simp only [offZero, h0, if_true]; grind
    · simp only [offZero, h0, if_false, H]
      by_cases hg : gval F (dotB B w a) P = a
      · simp only [hg, if_true]
        cases hd : dotB B w a
        · rw [hd] at hg; simp [hg.symm]; grind
        · rw [hd] at hg; simp [hg.symm]; grind
      · simp only [hg, if_false]; grind
  rw [rsum_add] at hle
  have h1 := rsum_range_indicator_le (2 ^ B) (gval F false P)
  have h2 := rsum_range_indicator_le (2 ^ B) (gval F true P)
  grind

theorem C0_sum_le (B N : Nat) (F : Readout) (w : Nat) :
    rsum (List.range (2 ^ B)) (offZero (fun a => C0val B N F (dotB B w a) a)) ≤ 2 * T B N := by
  unfold C0val
  rw [rsum_congr (fun a _ => offZero_rsum _ _ a), ← rsum_comm]
  have : rsum (boards (2 ^ B) N) (fun P => rsum (List.range (2 ^ B))
      (fun a => offZero (fun a => H F (dotB B w a) a P) a)) ≤
      rsum (boards (2 ^ B) N) (fun _ => 2 * 1) := by
    apply rsum_le; intro P _
    have := disjoint_le_two B F w P
    show rsum (List.range (2 ^ B)) (offZero (fun a => H F (dotB B w a) a P)) ≤ 2 * 1
    grind
  rw [rsum_mul_left, rsum_boards_eq_T] at this
  exact this

/-- JOINT BOUND (counting form): q * #success ≤ 2 q^N + (q-1)^2 η q^N. -/
theorem succCount_bound {B N : Nat} (F : Readout) (w : Nat) {η : Rat}
    (hyp : CorrHyp B N F η) :
    ((2 ^ B : Nat) : Rat) * succCount B N F w ≤
      2 * T B N + ((2 ^ B - 1 : Nat) : Rat) * (((2 ^ B - 1 : Nat) : Rat) * (η * T B N)) := by
  have hq : 0 < 2 ^ B := Nat.two_pow_pos B
  rw [succCount_eq, ← rsum_mul_left]
  have e : rsum (List.range (2 ^ B))
        (fun a => ((2 ^ B : Nat) : Rat) * offZero (fun a => Aval B N F (dotB B w a) a) a) =
      rsum (List.range (2 ^ B))
        (offZero (fun a => ((2 ^ B : Nat) : Rat) * Aval B N F (dotB B w a) a)) := by
    apply rsum_congr; intro a _; by_cases h : a = 0 <;> simp [offZero, h]
  rw [e]
  have hle := rsum_offZero_le (q := 2 ^ B)
    (f := fun a => ((2 ^ B : Nat) : Rat) * Aval B N F (dotB B w a) a)
    (g := fun a => C0val B N F (dotB B w a) a + ((2 ^ B - 1 : Nat) : Rat) * (η * T B N))
    (by
      intro a _ ha
      have := (exact_value_count hyp (dotB B w a) ha).2
      grind)
  rw [rsum_offZero_add, rsum_offZero_const hq] at hle
  have h2 := C0_sum_le B N F w
  grind

/-- Pr[sigma ≠ 0] = (q-1)/q, in counting form, for N ≥ 1. -/
theorem nonzeroCount_eq (B N : Nat) :
    nonzeroCount B (N + 1) = T B (N + 1) - ((2 ^ B : Nat) : Rat) ^ N := by
  unfold nonzeroCount
  have e : rsum (boards (2 ^ B) (N + 1)) (fun P => if nimSum P ≠ 0 then 1 else 0) =
      rsum (boards (2 ^ B) (N + 1)) (fun _ => 1) -
        rsum (boards (2 ^ B) (N + 1)) (fun P => if nimSum P = 0 then 1 else 0) := by
    have := rsum_add (boards (2 ^ B) (N + 1)) (fun P => if nimSum P ≠ 0 then (1 : Rat) else 0)
      (fun P => if nimSum P = 0 then 1 else 0)
    rw [rsum_congr (g := fun _ => (1 : Rat)) (by
      intro P _; by_cases h : nimSum P = 0 <;> simp [h])] at this
    grind
  rw [e, rsum_boards_eq_T, sigma_uniform B N 0 (Nat.two_pow_pos B)]

theorem prob_sigma_ne_zero (B N : Nat) :
    nonzeroCount B (N + 1) / T B (N + 1) =
      (((2 ^ B : Nat) : Rat) - 1) / ((2 ^ B : Nat) : Rat) := by
  rw [nonzeroCount_eq]
  have hq := q_pos B
  have hq' : ((2 ^ B : Nat) : Rat) ≠ 0 := Rat.ne_of_gt hq
  have ht : (0 : Rat) < ((2 ^ B : Nat) : Rat) ^ N := by
    rw [← Rat.natCast_pow]; exact Rat.natCast_pos.mpr (Nat.pow_pos (Nat.two_pow_pos B))
  have ht' : ((2 ^ B : Nat) : Rat) ^ N ≠ 0 := Rat.ne_of_gt ht
  unfold T
  rw [Rat.pow_succ]
  generalize ((2 ^ B : Nat) : Rat) ^ N = t at *
  generalize ((2 ^ B : Nat) : Rat) = q at *
  grind

/-- MAIN THEOREM (Appendix G(i), finite form).  For every B ≥ 1, N ≥ 1 (written
    N + 1), every readout F, every vector w (the head's linear functional
    ell(sigma) = <w, sigma>), and every η, the parity-correlation premise implies
      Pr[legal winning move | sigma ≠ 0] ≤ 2/(q-1) + (q-1) η,   q = 2^B. -/
theorem success_bound {B N : Nat} (hB : 1 ≤ B) (F : Readout) (w : Nat) {η : Rat}
    (hyp : CorrHyp B (N + 1) F η) :
    succCount B (N + 1) F w / nonzeroCount B (N + 1) ≤
      2 / (((2 ^ B : Nat) : Rat) - 1) + (((2 ^ B : Nat) : Rat) - 1) * η := by
  have hqge : 2 ≤ 2 ^ B := by
    have := Nat.pow_le_pow_right (show 0 < 2 by decide) hB; simpa using this
  have hq2 : (2 : Rat) ≤ ((2 ^ B : Nat) : Rat) := by
    have := Rat.natCast_le_natCast.mpr hqge; simpa using this
  have hjoint := succCount_bound F w hyp
  rw [natCast_pred] at hjoint
  have ht : (0 : Rat) < ((2 ^ B : Nat) : Rat) ^ N := by
    rw [← Rat.natCast_pow]; exact Rat.natCast_pos.mpr (Nat.pow_pos (Nat.two_pow_pos B))
  have hT : T B (N + 1) = ((2 ^ B : Nat) : Rat) * ((2 ^ B : Nat) : Rat) ^ N := by
    unfold T; rw [Rat.pow_succ]; grind
  have hZ : nonzeroCount B (N + 1) =
      (((2 ^ B : Nat) : Rat) - 1) * ((2 ^ B : Nat) : Rat) ^ N := by
    rw [nonzeroCount_eq, hT]; grind
  rw [hT] at hjoint
  rw [hZ]
  generalize succCount B (N + 1) F w = S at *
  generalize ((2 ^ B : Nat) : Rat) ^ N = t at *
  generalize ((2 ^ B : Nat) : Rat) = q at *
  have h1 : (0 : Rat) < q - 1 := by grind
  have hZpos : 0 < (q - 1) * t := Rat.mul_pos h1 ht
  apply le_div_of_mul_le hZpos
  have hqpos : (0 : Rat) < q := by grind
  have hS : S ≤ 2 * t + (q - 1) * ((q - 1) * (η * t)) := by
    apply Rat.le_of_mul_le_mul_left _ hqpos
    grind
  have hq1 : q - 1 ≠ 0 := Rat.ne_of_gt h1
  have eR : (2 / (q - 1) + (q - 1) * η) * ((q - 1) * t) =
      2 * t + (q - 1) * ((q - 1) * (η * t)) := by grind
  rw [eR]
  exact hS

/-! ## The structured heads are nonzero linear functionals -/

/-- The vector w_j with RO_{pi_j}(P) = <w_j, sigma(P)>: w_0 = 1, w_j = 2^j XOR 1. -/
def headVec (j : Nat) : Nat := if j = 0 then 1 else 2 ^ j ^^^ 1

theorem dotB_two_pow (B j v : Nat) : dotB B (2 ^ j) v = (decide (j < B) && v.testBit j) := by
  induction B with
  | zero => simp [dotB]
  | succ B ih =>
    simp only [dotB, ih, Nat.testBit_two_pow]
    by_cases h1 : j < B
    · have : ¬ j = B := by omega
      simp [h1, this, show j < B + 1 by omega]
    · by_cases h2 : j = B
      · subst h2; simp
      · have : ¬ j < B + 1 := by omega
        simp [h1, h2, this]

theorem head_linear {B j : Nat} (hj : j < B) (v : Nat) :
    channel j v = dotB B (headVec j) v := by
  unfold headVec channel
  by_cases h0 : j = 0
  · subst h0
    have : (1 : Nat) = 2 ^ 0 := rfl
    simp only [if_true]
    rw [this, dotB_two_pow]; simp [hj]
  · simp only [h0, if_false]
    rw [dotB_xor_left, show (1 : Nat) = 2 ^ 0 from rfl, dotB_two_pow, dotB_two_pow]
    simp [hj, show 0 < B by omega]

theorem headVec_ne_zero (j : Nat) : headVec j ≠ 0 := by
  unfold headVec
  by_cases h0 : j = 0
  · simp [h0]
  · simp only [h0, if_false]
    intro h
    have := xor_eq_zero_imp h
    have := Nat.one_lt_two_pow h0
    omega

theorem headVec_lt {B j : Nat} (hj : j < B) : headVec j < 2 ^ B := by
  unfold headVec
  by_cases h0 : j = 0
  · simp only [h0, if_true]; exact Nat.one_lt_two_pow (by omega)
  · simp only [h0, if_false]
    exact Nat.xor_lt_two_pow (Nat.pow_lt_pow_right (by decide) hj) (Nat.one_lt_two_pow (by omega))

/-- RO_{pi_j}(P), the executed rollout outcome, is the linear functional <w_j, sigma(P)>. -/
theorem rollout_outcome_linear {B j : Nat} (hj : j < B) (P : List Nat) :
    rolloutWinner j P = dotB B (headVec j) (nimSum P) := by
  rw [rolloutWinner_channel, head_linear hj]

/-- SINGLE-POLICY INFORMATION BOUND (paper Prop. single-policy-bound): if P' differs
    from P in one heap h -> h', then RO_{pi_j}(P') = RO_{pi_j}(P) XOR <w_j, h XOR h'>,
    a correction bit computable from the known heap values. -/
theorem single_policy_affine {B j : Nat} (hj : j < B) (pre post : List Nat) (h h' : Nat) :
    rolloutWinner j (pre ++ h' :: post) =
      xor (rolloutWinner j (pre ++ h :: post)) (dotB B (headVec j) (h ^^^ h')) := by
  rw [rollout_outcome_linear hj, rollout_outcome_linear hj, nimSum_move, dotB_xor_right]

/-- Success count when the readout is fed the ACTUAL rollout outcome RO_{pi_j}(P). -/
def succCountRO (B N : Nat) (F : Readout) (j : Nat) : Rat :=
  rsum (boards (2 ^ B) N)
    (fun P => if nimSum P ≠ 0 ∧ successB F (rolloutWinner j P) P = true then 1 else 0)

/-- MAIN THEOREM FOR ONE STRUCTURED HEAD: a readout F_N(P, RO_{pi_j}(P)) that
    satisfies the correlation premise wins with conditional probability at most
    2/(q-1) + (q-1) η. -/
theorem structured_head_bound {B N j : Nat} (hj : j < B) (F : Readout) {η : Rat}
    (hyp : CorrHyp B (N + 1) F η) :
    succCountRO B (N + 1) F j / nonzeroCount B (N + 1) ≤
      2 / (((2 ^ B : Nat) : Rat) - 1) + (((2 ^ B : Nat) : Rat) - 1) * η := by
  have e : succCountRO B (N + 1) F j = succCount B (N + 1) F (headVec j) := by
    unfold succCountRO succCount
    apply rsum_congr; intro P _
    rw [rollout_outcome_linear hj]
  rw [e]
  exact success_bound (by omega) F (headVec j) hyp

/-! ## Asymptotic corollary for fixed B -/

/-- f is negligible: below every inverse polynomial eventually (N+1 avoids 1/0). -/
def Negligible (f : Nat → Rat) : Prop :=
  ∀ c : Nat, ∃ N0 : Nat, ∀ N ≥ N0, f N ≤ 1 / (((N + 1 : Nat) : Rat)) ^ c

theorem negligible_const_mul (K : Nat) {f : Nat → Rat} (hf : Negligible f) :
    Negligible (fun N => (K : Rat) * f N) := by
  intro c
  obtain ⟨N0, hN0⟩ := hf (c + 1)
  refine ⟨max N0 K, fun N hN => ?_⟩
  have h1 := hN0 N (by omega)
  show (K : Rat) * f N ≤ 1 / (((N + 1 : Nat) : Rat)) ^ c
  have hXpos : (0 : Rat) < ((N + 1 : Nat) : Rat) := Rat.natCast_pos.mpr (by omega)
  have hXc : (0 : Rat) < ((N + 1 : Nat) : Rat) ^ c := by
    rw [← Rat.natCast_pow]; exact Rat.natCast_pos.mpr (Nat.pow_pos (by omega))
  have hKX : (K : Rat) ≤ ((N + 1 : Nat) : Rat) := Rat.natCast_le_natCast.mpr (by omega)
  have hK0 : (0 : Rat) ≤ K := Rat.natCast_nonneg
  rw [Rat.pow_succ] at h1
  generalize f N = y at *
  generalize ((N + 1 : Nat) : Rat) ^ c = Y at *
  generalize ((N + 1 : Nat) : Rat) = X at *
  have k1 := Rat.mul_le_mul_of_nonneg_left h1 hK0
  have hY' : Y ≠ 0 := Rat.ne_of_gt hXc
  have hX' : X ≠ 0 := Rat.ne_of_gt hXpos
  have hd : 0 < Y * X := Rat.mul_pos hXc hXpos
  have k2 : (K : Rat) * (1 / (Y * X)) ≤ 1 / Y := by
    apply Rat.le_of_mul_le_mul_right _ hd
    have e1 : (K : Rat) * (1 / (Y * X)) * (Y * X) = K := by grind
    have e2 : 1 / Y * (Y * X) = X := by grind
    rw [e1, e2]; exact hKX
  exact Rat.le_trans k1 k2

/-- ASYMPTOTIC COROLLARY: for fixed B ≥ 1 and readouts F_N satisfying the
    correlation premise with negligible η_N, the conditional success probability
    is at most 2/(q-1) + ε_N with ε_N negligible. -/
theorem asymptotic_bound {B : Nat} (hB : 1 ≤ B) (F : Nat → Readout) (w : Nat)
    (η : Nat → Rat) (hη : Negligible η) (hyp : ∀ N, CorrHyp B (N + 1) (F N) (η N)) :
    ∃ ε : Nat → Rat, Negligible ε ∧ ∀ N,
      succCount B (N + 1) (F N) w / nonzeroCount B (N + 1) ≤
        2 / (((2 ^ B : Nat) : Rat) - 1) + ε N := by
  refine ⟨fun N => ((2 ^ B - 1 : Nat) : Rat) * η N, negligible_const_mul _ hη, fun N => ?_⟩
  have := success_bound hB (F N) w (hyp N)
  rw [natCast_pred]
  exact this


#print axioms rsum_nil
#print axioms rsum_cons
#print axioms rsum_append
#print axioms rsum_congr
#print axioms rsum_zero
#print axioms rsum_add
#print axioms rsum_mul_left
#print axioms rsum_le
#print axioms rsum_const
#print axioms rsum_comm
#print axioms rsum_map
#print axioms rsum_flatMap
#print axioms rsum_bound
#print axioms rsum_range_ite
#print axioms rsum_range_split0
#print axioms range_one_add
#print axioms rsum_offZero_bound
#print axioms rsum_offZero_const
#print axioms rsum_offZero_add
#print axioms rsum_offZero_le
#print axioms mem_boards
#print axioms rsum_boards_succ
#print axioms count_boards
#print axioms xor_eq_iff
#print axioms sigma_uniform
#print axioms dotB_xor_right
#print axioms dotB_xor_left
#print axioms dotB_zero_left
#print axioms dotB_congr_left
#print axioms chi_xor_right
#print axioms chi_zero_left
#print axioms chi_cases
#print axioms lowZero_spec
#print axioms lowZero_iff
#print axioms orthogonality
#print axioms indicator_expansion
#print axioms successB_iff
#print axioms nimSum_set
#print axioms set_move
#print axioms success_legal
#print axioms invalid_output
#print axioms success_iff_gval
#print axioms q_pos
#print axioms T_eq
#print axioms T_pos
#print axioms rsum_boards_eq_T
#print axioms div_mul_cancel'
#print axioms div_le_div_of_le
#print axioms le_div_of_mul_le
#print axioms sigma_lt
#print axioms Csum_bound
#print axioms natCast_pred
#print axioms exact_value_count
#print axioms exact_value_error
#print axioms offZero_rsum
#print axioms rsum_offZero_indicator
#print axioms rsum_range_indicator_le
#print axioms succCount_eq
#print axioms disjoint_le_two
#print axioms C0_sum_le
#print axioms succCount_bound
#print axioms nonzeroCount_eq
#print axioms prob_sigma_ne_zero
#print axioms success_bound
#print axioms dotB_two_pow
#print axioms head_linear
#print axioms headVec_ne_zero
#print axioms headVec_lt
#print axioms rollout_outcome_linear
#print axioms single_policy_affine
#print axioms structured_head_bound
#print axioms negligible_const_mul
#print axioms asymptotic_bound

end Prob
end NimAudit
