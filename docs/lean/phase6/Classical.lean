import Bypass

/- Phase 6, Priority 3a: the classical external boundary and its paper-specific
   consequences.  Written by Claude (10 October 2026).  Lean 4.26.0, core/Std only.

   EXTERNAL INPUT (a theorem PARAMETER, never an axiom), as authorised by Søren Riis:
   Håstad, "On the correlation of parity and small-depth circuits", SIAM J. Comput.
   43(5):1699–1708 (2014), Corollary 3.2 (DOI 10.1137/120897432): a depth-d circuit of
   size S agrees with parity on n inputs on a fraction (1 + c)/2 of inputs with
   |c| ≤ 2^{−Ω(n/(log S)^{d−1})} (exponent n/(log S)^{d−1}, not (n/log S)^{d−1}).  For
   fixed d and S polynomial in n this is negligible in n.  We take the negligible FAMILY
   form, quantified over ALL bounded-depth polynomial-size circuits, in the CLASSICAL
   convention, as the single external input `HastadNegl`.

   CONVENTION ADAPTERS PROVED HERE.
   * Circuit conventions: classical depth counts AND/OR levels only (aoDepth), classical
     size counts AND/OR gates only (aoGates), negations sit on inputs (negLeaf).  Our
     formulas count NOT in depth and every node in size, so aoDepth ≤ depth and
     aoGates ≤ size; nnf pushes negations to the inputs preserving the function, aoDepth,
     aoGates and inputs.  The hypothesis is stated for FORMULAS (trees), which are special
     circuits: a formula with g AND/OR gates is a circuit with g gates, so the classical
     DAG theorem implies it (phase 4 SharedCircuit relates formulas and DAGs in our
     convention).  Trivial depths/sizes need no special case: the statement is monotone.
   * Correlation conventions: Håstad's signed correlation scorr = 2·Pr[C = PAR] − 1 versus
     our indicator correlation E[1_C · (−1)^PAR]; for m ≥ 1 inputs the latter equals
     −scorr/2 (indicator_signed), so |scorr| ≤ δ gives the indicator premise with δ/2.
     For m = 0 the parity is constant and the conventions do not agree (not used).
   CONSEQUENCES PROVED HERE.
   * HastadNegl ⇒ ParityNotAC0 (the worst-case premise of the single-frame barrier and of
     the bypass barriers).
   * The asymptotic Theorem thm:search-gap(i): for fixed B ≥ 2 and any binary readout
     family of fixed depth and polynomial size, success ≤ 2/(2^B − 1) + η_N with η
     negligible, including the uniformity over restriction supports N+1 ≤ m ≤ B(N+1). -/

namespace NimAudit
namespace ClassicalBoundary

open Game Rollout Prob Attain Recurrent AC0 AC0.Circ CorrBridge AttainCircuit Bridge SelectCircuit
  BinReadout Controller ControllerBits PriorityEncoder ThresholdNet ThresholdInst FiniteNet WholeGame
  Family Barrier ParityCircuit

/-! ## Classical circuit conventions -/

/-- AND/OR depth: NOT nodes and leaves contribute nothing. -/
def aoDepth : Circ → Nat
  | .input _ => 0
  | .const _ => 0
  | .not c => aoDepth c
  | .and cs => listMax (cs.attach.map (fun ⟨c, _⟩ => aoDepth c)) + 1
  | .or cs => listMax (cs.attach.map (fun ⟨c, _⟩ => aoDepth c)) + 1

/-- Number of AND/OR gates. -/
def aoGates : Circ → Nat
  | .input _ => 0
  | .const _ => 0
  | .not c => aoGates c
  | .and cs => (cs.attach.map (fun ⟨c, _⟩ => aoGates c)).sum + 1
  | .or cs => (cs.attach.map (fun ⟨c, _⟩ => aoGates c)).sum + 1

/-- Negation normal form: NOT is applied only to inputs and constants. -/
def negLeaf : Circ → Bool
  | .input _ => true
  | .const _ => true
  | .not (.input _) => true
  | .not (.const _) => true
  | .not _ => false
  | .and cs => cs.attach.all (fun ⟨c, _⟩ => negLeaf c)
  | .or cs => cs.attach.all (fun ⟨c, _⟩ => negLeaf c)

/-- Push negations to the leaves; p = true means "negate". -/
def nnf (p : Bool) : Circ → Circ
  | .input i => if p then .not (.input i) else .input i
  | .const b => .const (xor p b)
  | .not c => nnf (!p) c
  | .and cs => if p then .or (cs.attach.map (fun ⟨c, _⟩ => nnf p c)) else .and (cs.attach.map (fun ⟨c, _⟩ => nnf p c))
  | .or cs => if p then .and (cs.attach.map (fun ⟨c, _⟩ => nnf p c)) else .or (cs.attach.map (fun ⟨c, _⟩ => nnf p c))

@[simp] theorem aoDepth_and (cs : List Circ) : aoDepth (.and cs) = listMax (cs.map aoDepth) + 1 := by simp [aoDepth]
@[simp] theorem aoDepth_or (cs : List Circ) : aoDepth (.or cs) = listMax (cs.map aoDepth) + 1 := by simp [aoDepth]
@[simp] theorem aoGates_and (cs : List Circ) : aoGates (.and cs) = (cs.map aoGates).sum + 1 := by simp [aoGates]
@[simp] theorem aoGates_or (cs : List Circ) : aoGates (.or cs) = (cs.map aoGates).sum + 1 := by simp [aoGates]
@[simp] theorem negLeaf_and (cs : List Circ) : negLeaf (.and cs) = cs.all negLeaf := by simp [negLeaf]
@[simp] theorem negLeaf_or (cs : List Circ) : negLeaf (.or cs) = cs.all negLeaf := by simp [negLeaf]
@[simp] theorem nnf_and (p : Bool) (cs : List Circ) :
    nnf p (.and cs) = if p then .or (cs.map (nnf p)) else .and (cs.map (nnf p)) := by simp [nnf]
@[simp] theorem nnf_or (p : Bool) (cs : List Circ) :
    nnf p (.or cs) = if p then .and (cs.map (nnf p)) else .or (cs.map (nnf p)) := by simp [nnf]

theorem any_not_eq (l : List Circ) (f : Circ → Bool) : l.any (fun c => !f c) = !(l.all f) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [List.any_cons, List.all_cons, ih]

theorem all_not_eq (l : List Circ) (f : Circ → Bool) : l.all (fun c => !f c) = !(l.any f) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [List.any_cons, List.all_cons, ih]

/-- nnf computes the (possibly negated) function. -/
theorem eval_nnf (x : Nat → Bool) : ∀ (p : Bool) (c : Circ), eval x (nnf p c) = xor p (eval x c)
  | p, .input i => by cases p <;> simp [nnf]
  | p, .const b => by cases p <;> simp [nnf]
  | p, .not c => by simp only [nnf, eval_not, eval_nnf x (!p) c]; cases p <;> simp
  | p, .and cs => by
    rw [nnf_and]
    cases p
    · simp only [Bool.false_eq_true, if_false, eval_and, List.all_map, Bool.false_xor]
      exact all_congr_mem (fun c _ => by simp [eval_nnf x false c])
    · simp only [if_true, eval_or, eval_and, List.any_map, Bool.true_xor]
      rw [← any_not_eq]
      exact any_congr_mem (fun c _ => by simp [eval_nnf x true c])
  | p, .or cs => by
    rw [nnf_or]
    cases p
    · simp only [Bool.false_eq_true, if_false, eval_or, List.any_map, Bool.false_xor]
      exact any_congr_mem (fun c _ => by simp [eval_nnf x false c])
    · simp only [if_true, eval_and, eval_or, List.all_map, Bool.true_xor]
      rw [← all_not_eq]
      exact all_congr_mem (fun c _ => by simp [eval_nnf x true c])

theorem negLeaf_nnf : ∀ (p : Bool) (c : Circ), negLeaf (nnf p c) = true
  | p, .input i => by cases p <;> simp [nnf, negLeaf]
  | p, .const b => by simp [nnf, negLeaf]
  | p, .not c => by simp only [nnf]; exact negLeaf_nnf (!p) c
  | p, .and cs => by
    rw [nnf_and]
    have h : ∀ c ∈ cs, negLeaf (nnf p c) = true := fun c _ => negLeaf_nnf p c
    cases p <;> simp [List.all_eq_true] <;> exact h
  | p, .or cs => by
    rw [nnf_or]
    have h : ∀ c ∈ cs, negLeaf (nnf p c) = true := fun c _ => negLeaf_nnf p c
    cases p <;> simp [List.all_eq_true] <;> exact h

theorem listMax_map_congr {l : List Circ} {f g : Circ → Nat} (h : ∀ c ∈ l, f c = g c) :
    listMax (l.map f) = listMax (l.map g) := by rw [List.map_congr_left h]

theorem sum_map_congr' {l : List Circ} {f g : Circ → Nat} (h : ∀ c ∈ l, f c = g c) :
    (l.map f).sum = (l.map g).sum := by rw [List.map_congr_left h]

theorem aoDepth_nnf : ∀ (p : Bool) (c : Circ), aoDepth (nnf p c) = aoDepth c
  | p, .input i => by cases p <;> simp [nnf, aoDepth]
  | p, .const b => by simp [nnf, aoDepth]
  | p, .not c => by simp only [nnf, aoDepth]; exact aoDepth_nnf (!p) c
  | p, .and cs => by
    rw [nnf_and]
    have h := listMax_map_congr (l := cs) (f := fun c => aoDepth (nnf p c)) (g := aoDepth) (fun c _ => aoDepth_nnf p c)
    cases p <;> simp [List.map_map, Function.comp_def, h]
  | p, .or cs => by
    rw [nnf_or]
    have h := listMax_map_congr (l := cs) (f := fun c => aoDepth (nnf p c)) (g := aoDepth) (fun c _ => aoDepth_nnf p c)
    cases p <;> simp [List.map_map, Function.comp_def, h]

theorem aoGates_nnf : ∀ (p : Bool) (c : Circ), aoGates (nnf p c) = aoGates c
  | p, .input i => by cases p <;> simp [nnf, aoGates]
  | p, .const b => by simp [nnf, aoGates]
  | p, .not c => by simp only [nnf, aoGates]; exact aoGates_nnf (!p) c
  | p, .and cs => by
    rw [nnf_and]
    have h := sum_map_congr' (l := cs) (f := fun c => aoGates (nnf p c)) (g := aoGates) (fun c _ => aoGates_nnf p c)
    cases p <;> simp [List.map_map, Function.comp_def, h]
  | p, .or cs => by
    rw [nnf_or]
    have h := sum_map_congr' (l := cs) (f := fun c => aoGates (nnf p c)) (g := aoGates) (fun c _ => aoGates_nnf p c)
    cases p <;> simp [List.map_map, Function.comp_def, h]

theorem maxInput_nnf : ∀ (p : Bool) (c : Circ), maxInput (nnf p c) = maxInput c
  | p, .input i => by cases p <;> simp [nnf]
  | p, .const b => by simp [nnf]
  | p, .not c => by simp only [nnf, maxInput_not]; exact maxInput_nnf (!p) c
  | p, .and cs => by
    rw [nnf_and]
    have h := listMax_map_congr (l := cs) (f := fun c => maxInput (nnf p c)) (g := maxInput) (fun c _ => maxInput_nnf p c)
    cases p <;> simp [List.map_map, Function.comp_def, h]
  | p, .or cs => by
    rw [nnf_or]
    have h := listMax_map_congr (l := cs) (f := fun c => maxInput (nnf p c)) (g := maxInput) (fun c _ => maxInput_nnf p c)
    cases p <;> simp [List.map_map, Function.comp_def, h]

theorem aoDepth_le : ∀ c : Circ, aoDepth c ≤ depth c
  | .input i => by simp [aoDepth]
  | .const b => by simp [aoDepth]
  | .not c => by simp only [aoDepth, depth_not]; have := aoDepth_le c; omega
  | .and cs => by
    simp only [aoDepth_and, depth_and]
    have : listMax (cs.map aoDepth) ≤ listMax (cs.map depth) := by
      apply listMax_le; intro a ha
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ha
      exact Nat.le_trans (aoDepth_le c) (le_listMax (List.mem_map_of_mem hc))
    omega
  | .or cs => by
    simp only [aoDepth_or, depth_or]
    have : listMax (cs.map aoDepth) ≤ listMax (cs.map depth) := by
      apply listMax_le; intro a ha
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ha
      exact Nat.le_trans (aoDepth_le c) (le_listMax (List.mem_map_of_mem hc))
    omega

theorem aoGates_le : ∀ c : Circ, aoGates c ≤ size c
  | .input i => by simp [aoGates]
  | .const b => by simp [aoGates]
  | .not c => by simp only [aoGates, size_not]; have := aoGates_le c; omega
  | .and cs => by
    simp only [aoGates_and, size_and]
    have := sum_map_le_mem (l := cs) (f := aoGates) (g := size) (fun c _ => aoGates_le c)
    omega
  | .or cs => by
    simp only [aoGates_or, size_or]
    have := sum_map_le_mem (l := cs) (f := aoGates) (g := size) (fun c _ => aoGates_le c)
    omega

/-- Lemma lem:unit-ac0 in the paper's convention: one fixed-scale gate is a DEPTH-2 DNF
    when negations on inputs are not counted (our NOT-counting depth bound was 3). -/
theorem dnf_aoDepth (W : Nat) (g : Gate) : aoDepth (dnf W g) ≤ 2 := by
  unfold dnf
  rw [aoDepth_or]
  have : listMax ((((boards (g.fanin + 1) W).filter (fun t => decide (g.thr ≤ selSum g t))).map (termC g)).map aoDepth) ≤ 1 := by
    apply listMax_le; intro a ha
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ha
    obtain ⟨t, _, rfl⟩ := List.mem_map.mp hc
    unfold termC; rw [aoDepth_and]
    have : listMax ((t.filterMap (fun j => if j < g.fanin then some (litC g j) else none)).map aoDepth) ≤ 0 := by
      apply listMax_le; intro b hb
      obtain ⟨c', hc', rfl⟩ := List.mem_map.mp hb
      obtain ⟨j, _, hj⟩ := List.mem_filterMap.mp hc'
      split at hj
      · cases hj; unfold litC; split <;> simp [aoDepth]
      · cases hj
    omega
  omega

/-! ## Correlation conventions -/

/-- Agreement count of a formula with parity on m bits. -/
def agree (m : Nat) (C : Circ) : Rat := rsum (bitvecs m) (fun y => if eval (vfun y) C = par y then 1 else 0)

/-- Håstad's signed correlation c, defined by Pr[C = PAR] = (1 + c)/2. -/
def scorr (m : Nat) (C : Circ) : Rat := 2 * agree m C / (2 : Rat) ^ m - 1

theorem sgn_not' (b : Bool) : sgn (!b) = -sgn b := by cases b <;> decide

theorem sgn_par_sum {m : Nat} (hm : 1 ≤ m) : rsum (bitvecs m) (fun y => sgn (par y)) = 0 := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  rw [rsum_bitvecs_succ]
  have e : rsum (bitvecs n) (fun v => sgn (par (true :: v))) = rsum (bitvecs n) (fun v => (-1) * sgn (par v)) := by
    apply rsum_congr; intro v _; simp only [par, Bool.true_xor]; rw [sgn_not']; grind
  rw [e, rsum_mul_left]
  have e2 : rsum (bitvecs n) (fun v => sgn (par (false :: v))) = rsum (bitvecs n) (fun v => sgn (par v)) := by
    apply rsum_congr; intro v _; simp [par]
  rw [e2]; grind

/-- CONVENTION ADAPTER: for m ≥ 1, E[1_C · (−1)^PAR] = −scorr/2. -/
theorem indicator_signed {m : Nat} (hm : 1 ≤ m) (C : Circ) :
    rsum (bitvecs m) (fun y => ind (eval (vfun y) C) * sgn (par y)) / (2 : Rat) ^ m = -(scorr m C) / 2 := by
  have hpt : ∀ y : List Bool, ind (eval (vfun y) C) * sgn (par y) =
      (1 / 2) * sgn (par y) + ((-1) * (if eval (vfun y) C = par y then 1 else 0) + 1 / 2) := by
    intro y
    cases eval (vfun y) C <;> cases par y <;> simp [ind, sgn] <;> grind
  rw [rsum_congr (fun y _ => hpt y), rsum_add, rsum_add, rsum_mul_left, rsum_mul_left, rsum_const,
    sgn_par_sum hm, length_bitvecs]
  unfold scorr agree
  have hT : (0 : Rat) < (2 : Rat) ^ m := two_pow_pos' m
  have hc : (((2 ^ m : Nat) : Rat)) = (2 : Rat) ^ m := by simp
  rw [hc]
  generalize rsum (bitvecs m) (fun y => if eval (vfun y) C = par y then (1 : Rat) else 0) = A
  generalize (2 : Rat) ^ m = T at hT ⊢
  have hT' : T ≠ 0 := Rat.ne_of_gt hT
  grind

/-! ## The external input and its consequences -/

/-- Negligible nonnegative rational sequence: below every inverse polynomial eventually. -/
def Negligible (f : Nat → Rat) : Prop :=
  (∀ n, 0 ≤ f n) ∧ ∀ k : Nat, ∃ n0 : Nat, ∀ n, n0 ≤ n → f n * ((n : Rat) + 1) ^ k ≤ 1

/-- Classical-convention correlation bound for given depth, gate count and input length:
    every negation-normal formula with AND/OR depth ≤ d and ≤ S AND/OR gates reading m ≥ 1
    inputs has |signed correlation with parity| ≤ δ. -/
def ClassicalCorr (d S m : Nat) (δ : Rat) : Prop :=
  ∀ C : Circ, negLeaf C = true → aoDepth C ≤ d → aoGates C ≤ S → maxInput C ≤ m →
    -δ ≤ scorr m C ∧ scorr m C ≤ δ

/-- THE EXTERNAL CLASSICAL THEOREM (Håstad 2014, Cor. 3.2, negligible family form), a
    hypothesis: for every depth d and polynomial gate bound c·m^k there is a negligible δ
    with ClassicalCorr d (c·m^k) m (δ m) for all m ≥ 1. -/
def HastadNegl : Prop :=
  ∀ d c k : Nat, ∃ δ : Nat → Rat, Negligible δ ∧ ∀ m, 1 ≤ m → ClassicalCorr d (c * m ^ k) m (δ m)

theorem classicalCorr_mono {d S S' m : Nat} {δ : Rat} (h : ClassicalCorr d S' m δ) (hS : S ≤ S') :
    ClassicalCorr d S m δ :=
  fun C h1 h2 h3 h4 => h C h1 h2 (Nat.le_trans h3 hS) h4

theorem classicalCorr_mono_d {d d' S m : Nat} {δ : Rat} (h : ClassicalCorr d' S m δ) (hd : d ≤ d') :
    ClassicalCorr d S m δ :=
  fun C h1 h2 h3 h4 => h C h1 (Nat.le_trans h2 hd) h3 h4

/-- TRIVIAL DEPTH/SIZE CASES: Håstad's corollary is stated for depth d ≥ 2 and nontrivial
    size; the family form HastadNegl follows from the instances with d ≥ 2, c ≥ 1, k ≥ 1
    alone, since ClassicalCorr is monotone in depth and size. -/
theorem hastadNegl_of_deep
    (h : ∀ d c k : Nat, 2 ≤ d → 1 ≤ c → 1 ≤ k →
      ∃ δ : Nat → Rat, Negligible δ ∧ ∀ m, 1 ≤ m → ClassicalCorr d (c * m ^ k) m (δ m)) :
    HastadNegl := by
  intro d c k
  obtain ⟨δ, hδ, hc⟩ := h (d + 2) (c + 1) (k + 1) (by omega) (by omega) (by omega)
  refine ⟨δ, hδ, fun m hm => ?_⟩
  have hS : c * m ^ k ≤ (c + 1) * m ^ (k + 1) :=
    Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right hm (by omega))
  exact classicalCorr_mono_d (classicalCorr_mono (hc m hm) hS) (by omega)

/-- ADAPTER: the classical-convention bound gives the phase-3 indicator premise with δ/2. -/
theorem premise_of_classical {d S m : Nat} {δ : Rat} (hm : 1 ≤ m) (h : ClassicalCorr d S m δ) :
    ParityCorrPremise d S m (δ / 2) := by
  intro C hd hs hmx
  have hC := h (nnf false C) (negLeaf_nnf false C) (by rw [aoDepth_nnf]; exact Nat.le_trans (aoDepth_le C) hd)
    (by rw [aoGates_nnf]; exact Nat.le_trans (aoGates_le C) hs) (by rw [maxInput_nnf]; exact hmx)
  have he : scorr m (nnf false C) = scorr m C := by
    unfold scorr agree
    rw [rsum_congr (fun y _ => by rw [eval_nnf, Bool.false_xor])]
  rw [he] at hC
  rw [indicator_signed hm C]
  obtain ⟨h1, h2⟩ := hC
  have two : (0 : Rat) < 2 := by decide
  have a1 := div_le_div_of_le two (show -scorr m C ≤ δ by grind)
  have a2 := div_le_div_of_le two (show -δ ≤ -scorr m C by grind)
  have e1 : -(δ / 2) = -δ / 2 := by grind
  rw [e1]
  exact ⟨a2, a1⟩

theorem premise_mono {d S m : Nat} {ε ε' : Rat} (h : ParityCorrPremise d S m ε) (he : ε ≤ ε') :
    ParityCorrPremise d S m ε' := by
  intro C h1 h2 h3; obtain ⟨a, b⟩ := h C h1 h2 h3; constructor <;> grind

/-- WORST-CASE HARDNESS FROM THE EXTERNAL INPUT: HastadNegl ⇒ ParityNotAC0. -/
theorem parityNotAC0_of_hastad (hH : HastadNegl) : ParityNotAC0 := by
  intro d c k
  obtain ⟨δ, ⟨hnn, hneg⟩, hcorr⟩ := hH d c k
  obtain ⟨n0, hn0⟩ := hneg 1
  refine ⟨max n0 1, fun m hm => hard_of_premise (ε := 1 / 4) (by omega) (by grind)
    (premise_mono (premise_of_classical (by omega) (hcorr m (by omega))) ?_)⟩
  have h1 := hn0 m (by omega)
  have hm1 : (1 : Rat) ≤ (m : Rat) := by exact_mod_cast (show 1 ≤ m by omega)
  have hpos := hnn m
  simp only [Rat.pow_one] at h1
  -- δ m · (m + 1) ≤ 1 with m ≥ 1 gives δ m ≤ 1/2 < 1
  have : δ m ≤ 1 / 2 := by
    have h2 : δ m * 2 ≤ δ m * ((m : Rat) + 1) := Rat.mul_le_mul_of_nonneg_left (by grind) hpos
    grind
  have h3 := div_le_div_of_le (show (0 : Rat) < 2 by decide) this
  have e : (1 / 2 : Rat) / 2 = 1 / 4 := by grind
  rw [e] at h3; exact h3

/-! ## The asymptotic single-channel bound (Theorem thm:search-gap (i)) -/

/-- Sum of δ(m) over the restriction supports N+1 ≤ m ≤ B(N+1) (an upper bound for each
    δ(m)/2, uniform over the supports). -/
def etaSum (δ : Nat → Rat) (B N : Nat) : Rat :=
  rsum ((List.range (B * (N + 1) + 1)).filter (fun m => decide (N + 1 ≤ m))) δ

theorem rsum_nonneg' {l : List Nat} {f : Nat → Rat} (h : ∀ x ∈ l, 0 ≤ f x) : 0 ≤ rsum l f := by
  induction l with
  | nil => rw [rsum_nil]; exact Rat.le_refl
  | cons a l ih =>
    simp only [rsum_cons]
    have := h a (by simp); have := ih (fun x hx => h x (List.mem_cons_of_mem _ hx)); grind

theorem term_le_rsum {l : List Nat} {f : Nat → Rat} (h : ∀ x ∈ l, 0 ≤ f x) {a : Nat} (ha : a ∈ l) :
    f a ≤ rsum l f := by
  induction l with
  | nil => cases ha
  | cons b l ih =>
    simp only [rsum_cons]
    rcases List.mem_cons.mp ha with rfl | h'
    · have := rsum_nonneg' (fun x hx => h x (List.mem_cons_of_mem _ hx)); grind
    · have := ih (fun x hx => h x (List.mem_cons_of_mem _ hx)) h'; have := h b (by simp); grind

theorem pow_cast_le {N m k : Nat} (h : N ≤ m) : ((N : Rat) + 1) ^ k ≤ ((m : Rat) + 1) ^ k := by
  have : ((N + 1 : Nat) : Rat) ^ k ≤ ((m + 1 : Nat) : Rat) ^ k := by
    rw [← Rat.natCast_pow, ← Rat.natCast_pow]; exact_mod_cast Nat.pow_le_pow_left (show N + 1 ≤ m + 1 by omega) k
  simpa using this

theorem term_shift {x : Rat} {N m k : Nat} (hx : 0 ≤ x) (h : x * ((m : Rat) + 1) ^ k ≤ 1) (hNm : N ≤ m) :
    x * ((N : Rat) + 1) ^ k ≤ 1 :=
  Rat.le_trans (Rat.mul_le_mul_of_nonneg_left (pow_cast_le hNm) hx) h

theorem rsum_count_le {L : List Nat} {δ : Nat → Rat} {Q : Rat} (h : ∀ m ∈ L, δ m * Q ≤ 1) :
    rsum L δ * Q ≤ (L.length : Rat) := by
  induction L with
  | nil => rw [rsum_nil, Rat.zero_mul]; simp; exact Rat.le_refl
  | cons a L ih =>
    simp only [rsum_cons, List.length_cons]
    have h1 := h a (by simp)
    have h2 := ih (fun m hm => h m (List.mem_cons_of_mem _ hm))
    generalize rsum L δ = R at h2 ⊢
    generalize δ a = x at h1 ⊢
    have e : (x + R) * Q = x * Q + R * Q := by grind
    rw [e]
    push_cast
    grind

theorem half_le_self {x : Rat} (hx : 0 ≤ x) : x / 2 ≤ x :=
  le_div_of_mul_le (by decide) (by grind)

theorem le_one_of_mul {Y Q : Rat} (hQ : 0 < Q) (h : Y * Q ≤ Q) : Y ≤ 1 :=
  Rat.le_of_mul_le_mul_right (by rw [Rat.one_mul]; exact h) hQ

theorem pow_two_split (a e x : Rat) (k : Nat) : a * e * x ^ k * (x * x) = a * (e * x ^ (k + 2)) := by
  rw [Rat.pow_succ, Rat.pow_succ]; grind

/-- Negligibility of the support-uniform error for fixed B (any constant factor a). -/
theorem etaSum_negligible {δ : Nat → Rat} (hδ : Negligible δ) (B : Nat) (a : Nat) :
    Negligible (fun N => (a : Rat) * etaSum δ B N) := by
  obtain ⟨hnn, hneg⟩ := hδ
  have ha0 : (0 : Rat) ≤ (a : Rat) := by exact_mod_cast Nat.zero_le a
  have hη : ∀ N, 0 ≤ etaSum δ B N := fun N => rsum_nonneg' (fun m _ => hnn m)
  refine ⟨fun N => Rat.mul_nonneg ha0 (hη N), fun k => ?_⟩
  obtain ⟨n1, hn1⟩ := hneg (k + 2)
  refine ⟨n1 + a * (B + 1), fun N hN => ?_⟩
  have hNpos : (0 : Rat) < (N : Rat) + 1 := by
    have : (0 : Rat) ≤ (N : Rat) := by exact_mod_cast Nat.zero_le N
    grind
  have hQ : (0 : Rat) ≤ ((N : Rat) + 1) ^ (k + 2) := Rat.le_of_lt (Rat.pow_pos hNpos)
  -- sum bound
  have hsum : etaSum δ B N * ((N : Rat) + 1) ^ (k + 2) ≤
      (((List.range (B * (N + 1) + 1)).filter (fun m => decide (N + 1 ≤ m))).length : Rat) := by
    unfold etaSum
    apply rsum_count_le
    intro m hm
    simp only [List.mem_filter, List.mem_range, decide_eq_true_eq] at hm
    exact term_shift (hnn m) (hn1 m (by omega)) (by omega)
  have hlen : ((List.range (B * (N + 1) + 1)).filter (fun m => decide (N + 1 ≤ m))).length ≤ (B + 1) * (N + 1) := by
    have h1 := List.length_filter_le (fun m => decide (N + 1 ≤ m)) (List.range (B * (N + 1) + 1))
    rw [List.length_range] at h1
    have : B * (N + 1) + 1 ≤ (B + 1) * (N + 1) := by rw [Nat.add_mul, Nat.one_mul]; omega
    omega
  have hcount : a * ((B + 1) * (N + 1)) ≤ (N + 1) * (N + 1) := by
    rw [← Nat.mul_assoc]; exact Nat.mul_le_mul_right _ (by omega)
  have hlenR : (a : Rat) * ((((List.range (B * (N + 1) + 1)).filter (fun m => decide (N + 1 ≤ m))).length : Rat)) ≤
      ((N : Rat) + 1) * ((N : Rat) + 1) := by
    have h1 : ((a * (((List.range (B * (N + 1) + 1)).filter (fun m => decide (N + 1 ≤ m))).length) : Nat) : Rat) ≤
        (((N + 1) * (N + 1) : Nat) : Rat) := by
      exact_mod_cast Nat.le_trans (Nat.mul_le_mul_left a hlen) hcount
    push_cast at h1
    exact h1
  apply le_one_of_mul (Rat.mul_pos hNpos hNpos)
  show (a : Rat) * etaSum δ B N * ((N : Rat) + 1) ^ k * (((N : Rat) + 1) * ((N : Rat) + 1)) ≤ _
  rw [pow_two_split]
  exact Rat.le_trans (Rat.mul_le_mul_of_nonneg_left hsum ha0) hlenR

def uparE (B c k : Nat) : PE Nat :=
  12 * ((vB + 2) * PE.c (B + 2) * ((PE.c c * vB ^ k + 1) * (PE.c c * vB ^ k + 1) + 2)) ^ 10

theorem uparE_eval (B c k N : Nat) : PE.eval (fun _ N => N + 1) (uparE B c k) N =
    12 * (((N + 1) + 2) * (B + 2) * ((c * (N + 1) ^ k + 1) * (c * (N + 1) ^ k + 1) + 2)) ^ 10 := rfl

/-- The premise size of the correlation bridge is polynomial in N + 1 for fixed B. -/
theorem upar_poly (B c k : Nat) : PolyIn (fun _ : Nat => True) (fun N => N + 1)
    (fun N => 12 * (((N + 1) + 2) * (B + 2) * ((c * (N + 1) ^ k + 1) * (c * (N + 1) ^ k + 1) + 2)) ^ 10) :=
  polyE (ι := Nat) (fun i _ => Nat.succ_le_succ (Nat.zero_le i)) (fun _ N => N + 1) (fun _ _ _ => Nat.le_refl _)
    (uparE B c k) _ (fun N => (uparE_eval B c k N).symm)

def netE (W L c k : Nat) : PE Nat := 2 * (PE.c (2 * W + 3) ^ L * (PE.c c * vB ^ k + 1) ^ (W * L)) + PE.c c * vB ^ k

theorem netE_eval (W L c k N : Nat) : PE.eval (fun _ N => N + 1) (netE W L c k) N =
    2 * ((2 * W + 3) ^ L * (c * (N + 1) ^ k + 1) ^ (W * L)) + c * (N + 1) ^ k := rfl

/-- The network readout size is polynomial in N + 1. -/
theorem netsize_poly (W L c k : Nat) : PolyIn (fun _ : Nat => True) (fun N => N + 1)
    (fun N => 2 * ((2 * W + 3) ^ L * (c * (N + 1) ^ k + 1) ^ (W * L)) + c * (N + 1) ^ k) :=
  polyE (ι := Nat) (fun i _ => Nat.succ_le_succ (Nat.zero_le i)) (fun _ N => N + 1) (fun _ _ _ => Nat.le_refl _)
    (netE W L c k) _ (fun N => (netE_eval W L c k N).symm)

/-- ASYMPTOTIC SINGLE-CHANNEL THEOREM (thm:search-gap (i), asymptotic form), conditional
    only on the external classical input.  Fix B ≥ 2 and j < B.  Let R N b be binary
    readout formulas for N+1 heaps with BBound of FIXED depth d and size s N, index width
    r N, where s and r are polynomially bounded in N+1.  Then there is a negligible η with
      success_N ≤ 2/(2^B − 1) + η N   for every N. -/
theorem search_gap_asymptotic (hH : HastadNegl) {B j : Nat} (hj : j < B)
    (R : Nat → Bool → BCirc) (r s : Nat → Nat) (d : Nat)
    (hb : ∀ N b, BBound (R N b) (N + 1) B (r N) d (s N))
    (hpoly : ∃ c k, ∀ N, s N ≤ c * (N + 1) ^ k ∧ r N ≤ c * (N + 1) ^ k) :
    ∃ η : Nat → Rat, Negligible η ∧ ∀ N,
      succCountRO B (N + 1) (binReadoutOf B (N + 1) (R N)) j / nonzeroCount B (N + 1) ≤
        2 / (((2 ^ B : Nat) : Rat) - 1) + η N := by
  obtain ⟨c, k, hck⟩ := hpoly
  -- the premise size: 12 Upar(N+1) B ((r+1)(s+1))^10 is polynomial in N+1, hence in m ≥ N+1
  let S' : Nat → Nat := fun N => 12 * Upar (N + 1) B ((r N + 1) * (s N + 1)) ^ 10
  obtain ⟨C, K, hCK⟩ := upar_poly B c k
  have hS'le : ∀ N, S' N ≤ C * (N + 1) ^ K := by
    intro N
    refine Nat.le_trans ?_ (hCK N trivial)
    show 12 * Upar (N + 1) B ((r N + 1) * (s N + 1)) ^ 10 ≤ _
    unfold Upar
    apply Nat.mul_le_mul_left
    apply Nat.pow_le_pow_left
    apply Nat.mul_le_mul_left
    have h1 := (hck N).1; have h2 := (hck N).2
    have := Nat.mul_le_mul (show r N + 1 ≤ c * (N + 1) ^ k + 1 by omega) (show s N + 1 ≤ c * (N + 1) ^ k + 1 by omega)
    omega
  obtain ⟨δ, hδ, hcorr⟩ := hH (d + 2 + 11) C K
  refine ⟨fun N => (((2 ^ B - 1 : Nat) : Rat)) * etaSum δ B N, ?_, fun N => ?_⟩
  · exact etaSum_negligible hδ B (2 ^ B - 1)
  · have hbound := binary_readout_bound hj (R N) (hb N) (ε := etaSum δ B N) (fun m hm1 hm2 => by
      have hcl := classicalCorr_mono (hcorr m (by omega)) (show S' N ≤ C * m ^ K from
        Nat.le_trans (hS'le N) (Nat.mul_le_mul_left C (Nat.pow_le_pow_left hm1 K)))
      refine premise_mono (premise_of_classical (by omega) hcl) (Rat.le_trans (half_le_self (hδ.1 m)) ?_)
      apply term_le_rsum (fun x _ => hδ.1 x)
      simp only [List.mem_filter, List.mem_range, decide_eq_true_eq]; omega)
    have e : (((2 ^ B : Nat) : Rat) - 1) = (((2 ^ B - 1 : Nat) : Rat)) := (natCast_pred B).symm
    rw [e] at hbound ⊢
    exact hbound

/-- The same for readouts computed by fixed-scale threshold networks (W, L fixed,
    polynomial widths), compiled by the finite-input compiler. -/
theorem search_gap_asymptotic_net (hH : HastadNegl) {B j W L : Nat} (hj : j < B)
    (nets : Nat → Bool → List Layer) (r : Nat → Nat) (hlen : ∀ N b, (nets N b).length ≤ L)
    (hv : ∀ N b, NetValid W (nets N b)) (hr : ∀ N, N + 1 ≤ 2 ^ r N)
    (hpoly : ∃ c k, ∀ N b, NetBounded (c * (N + 1) ^ k) (nets N b) ∧ r N ≤ c * (N + 1) ^ k) :
    ∃ η : Nat → Rat, Negligible η ∧ ∀ N,
      succCountRO B (N + 1) (binReadoutOf B (N + 1) (fun b => netBCirc W B (N + 1) (r N) (nets N b))) j /
          nonzeroCount B (N + 1) ≤ 2 / (((2 ^ B : Nat) : Rat) - 1) + η N := by
  obtain ⟨c, k, hck⟩ := hpoly
  let s : Nat → Nat := fun N => 2 * ((2 * W + 3) ^ L * (c * (N + 1) ^ k + 1) ^ (W * L))
  apply search_gap_asymptotic hH hj (fun N b => netBCirc W B (N + 1) (r N) (nets N b)) r s (3 * L)
  · intro N b
    have hb := netBCirc_BBound (B := B) (N := N + 1) (r := r N) (nets N b) (hv N b) (hck N b).1 (hr N)
    have hl := hlen N b
    refine bbound_mono hb (Nat.mul_le_mul_left 3 hl) ?_
    have e1 : (2 * W + 3) ^ (nets N b).length ≤ (2 * W + 3) ^ L := Nat.pow_le_pow_right (by omega) hl
    have e2 : (c * (N + 1) ^ k + 1) ^ (W * (nets N b).length) ≤ (c * (N + 1) ^ k + 1) ^ (W * L) :=
      Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_left W hl)
    have := Nat.mul_le_mul e1 e2
    show 2 * ((2 * W + 3) ^ (nets N b).length * (c * (N + 1) ^ k + 1) ^ (W * (nets N b).length)) ≤ s N
    simp only [s]; omega
  · obtain ⟨C, K, hCK⟩ := netsize_poly W L c k
    refine ⟨C, K, fun N => ⟨?_, ?_⟩⟩
    · have h1 := hCK N trivial; dsimp only at h1
      show 2 * ((2 * W + 3) ^ L * (c * (N + 1) ^ k + 1) ^ (W * L)) ≤ C * (N + 1) ^ K; omega
    · have h1 := hCK N trivial; have h2 := (hck N false).2; dsimp only at h1; omega

/-! ## Axiom audit -/

#print axioms aoDepth_and
#print axioms aoDepth_or
#print axioms aoGates_and
#print axioms aoGates_or
#print axioms negLeaf_and
#print axioms negLeaf_or
#print axioms nnf_and
#print axioms nnf_or
#print axioms any_not_eq
#print axioms all_not_eq
#print axioms eval_nnf
#print axioms negLeaf_nnf
#print axioms listMax_map_congr
#print axioms sum_map_congr'
#print axioms aoDepth_nnf
#print axioms aoGates_nnf
#print axioms maxInput_nnf
#print axioms aoDepth_le
#print axioms aoGates_le
#print axioms dnf_aoDepth
#print axioms sgn_not'
#print axioms sgn_par_sum
#print axioms indicator_signed
#print axioms classicalCorr_mono
#print axioms classicalCorr_mono_d
#print axioms hastadNegl_of_deep
#print axioms premise_of_classical
#print axioms premise_mono
#print axioms parityNotAC0_of_hastad
#print axioms rsum_nonneg'
#print axioms term_le_rsum
#print axioms pow_cast_le
#print axioms term_shift
#print axioms rsum_count_le
#print axioms half_le_self
#print axioms le_one_of_mul
#print axioms pow_two_split
#print axioms etaSum_negligible
#print axioms uparE_eval
#print axioms upar_poly
#print axioms netE_eval
#print axioms netsize_poly
#print axioms search_gap_asymptotic
#print axioms search_gap_asymptotic_net


