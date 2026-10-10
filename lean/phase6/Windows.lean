import Bypass

/- Phase 6, Priority 3c: the remaining parts of Theorem thm:sim-ac0 and two small local
   claims.  Written by Claude (10 October 2026).  Lean 4.26.0, core/Std only.

   * FIXED MULTI-STATE RECURRENCE WINDOWS (Definition def:RNN-formal): an update may read
     the current input block and the w most recent states (input-independent initial
     states before time 0).  T updates unroll to formulas of depth ≤ 3·L·T, size ≤
     rnnSize W M L T + 1 ≤ 2·((2W+3)^L (M+1)^{WL})^T, reading only the T input blocks.  For
     constant T (and W, L) and polynomial M this is an AC0 family.
   * GATE-REALISED ATTENTION-STYLE COMPOSITION (Definition def:LTST-formal): a model given
     as a constant number K of stages (score computation, coefficient selection,
     aggregation, over the T window positions), EACH realised by a valid fixed-scale gate
     network, is one network (layers concatenated); the simulation theorem applies.  No
     claim about standard softmax attention is made.  A finite coefficient set alone is
     not the model's premise: the {0,1}-coefficient majority gate violates the bounded
     threshold premise for every fixed W once the fan-in exceeds 2W.
   * Remark rem:local-vs-global-parity: XOR of a constant number of formulas (e.g. of t
     B-bit blocks, bitwise) has constant depth and constant-factor size.
   * The literal-representation remark of Section 2: s − a·x ≥ θ ⇔ s + a(1−x) ≥ θ + a. -/

namespace NimAudit
namespace Windows

open AC0 AC0.Circ FiniteNet Family

/-! ## Fixed recurrence windows -/

/-- Update input layout: the current block (n bits), then the w most recent states
    (m bits each, most recent first); zero elsewhere. -/
def winIn (n m w : Nat) (x : Nat → Bool) (hs : Nat → Nat → Bool) : Nat → Bool := fun j =>
  if j < n then x j else if j < n + w * m then hs ((j - n) / m) ((j - n) % m) else false

/-- State after t updates (h0 before time 0 and as the initial state). -/
def wState (cell : List Layer) (n m w : Nat) (h0 : Nat → Bool) (x : Nat → Bool) : Nat → Nat → Bool
  | 0 => h0
  | t + 1 => evalNet cell (winIn n m w (fun j => x (t * n + j))
      (fun δ => if δ ≤ t then wState cell n m w h0 x (t - δ) else h0))
termination_by t => t
decreasing_by exact Nat.lt_succ_of_le (Nat.sub_le _ _)

/-- The unrolled formulas. -/
def wCirc (W : Nat) (cell : List Layer) (n m w : Nat) (h0 : Nat → Bool) : Nat → Nat → Circ
  | 0 => fun i => const (h0 i)
  | t + 1 => compileNet W cell (fun j => if j < n then input (t * n + j) else if j < n + w * m then
      (if (j - n) / m ≤ t then wCirc W cell n m w h0 (t - (j - n) / m) ((j - n) % m) else const (h0 ((j - n) % m)))
      else const false)
termination_by t => t
decreasing_by exact Nat.lt_succ_of_le (Nat.sub_le _ _)

theorem wState_succ (cell : List Layer) (n m w : Nat) (h0 x : Nat → Bool) (t : Nat) :
    wState cell n m w h0 x (t + 1) = evalNet cell (winIn n m w (fun j => x (t * n + j))
      (fun δ => if δ ≤ t then wState cell n m w h0 x (t - δ) else h0)) := wState.eq_2 cell n m w h0 x t

theorem wCirc_succ (W : Nat) (cell : List Layer) (n m w : Nat) (h0 : Nat → Bool) (t : Nat) :
    wCirc W cell n m w h0 (t + 1) = compileNet W cell (fun j => if j < n then input (t * n + j) else if j < n + w * m then
      (if (j - n) / m ≤ t then wCirc W cell n m w h0 (t - (j - n) / m) ((j - n) % m) else const (h0 ((j - n) % m)))
      else const false) := wCirc.eq_2 W cell n m w h0 t

theorem sizeBound_ge (W M S L : Nat) : S ≤ sizeBound W M S L := by
  induction L with
  | zero => simp [sizeBound]
  | succ L ih =>
    simp only [sizeBound]
    have : 1 ≤ gfac W M := by unfold gfac; omega
    have := Nat.le_mul_of_pos_left (sizeBound W M S L + 1) (show 0 < gfac W M by omega)
    omega

theorem rnnSize_mono (W M L : Nat) {t t' : Nat} (h : t ≤ t') : rnnSize W M L t ≤ rnnSize W M L t' := by
  induction t' with
  | zero => have : t = 0 := by omega
            subst this; exact Nat.le_refl _
  | succ t' ih =>
    rcases Nat.lt_or_ge t (t' + 1) with h1 | h1
    · exact Nat.le_trans (ih (by omega)) (by simp only [rnnSize]; exact sizeBound_ge W M _ L)
    · have : t = t' + 1 := by omega
      subst this; exact Nat.le_refl _

/-- WINDOW SIMULATION THEOREM.  For a valid L-layer cell with fan-ins/widths ≤ M reading
    the input block and the w most recent states, the state after T updates is computed by
    formulas with depth ≤ 3·L·T, size ≤ rnnSize W M L T, reading only the T input blocks. -/
theorem window_ac0 {W M : Nat} (cell : List Layer) (hv : NetValid W cell) (hb : NetBounded M cell)
    (n m w : Nat) (h0 : Nat → Bool) : ∀ T i,
    (∀ x : Nat → Bool, eval x (wCirc W cell n m w h0 T i) = wState cell n m w h0 x T i) ∧
    size (wCirc W cell n m w h0 T i) ≤ rnnSize W M cell.length T ∧
    depth (wCirc W cell n m w h0 T i) ≤ 3 * cell.length * T ∧
    maxInput (wCirc W cell n m w h0 T i) ≤ T * n := by
  intro T
  induction T using Nat.strongRecOn with
  | ind T ih =>
    intro i
    cases T with
    | zero => simp [wCirc.eq_1, wState.eq_1, rnnSize]
    | succ t =>
      -- the leaves of the last update
      let prev : Nat → Circ := fun j => if j < n then input (t * n + j) else if j < n + w * m then
        (if (j - n) / m ≤ t then wCirc W cell n m w h0 (t - (j - n) / m) ((j - n) % m) else const (h0 ((j - n) % m)))
        else const false
      have hprev : ∀ j, size (prev j) ≤ rnnSize W M cell.length t ∧ depth (prev j) ≤ 3 * cell.length * t ∧
          maxInput (prev j) ≤ (t + 1) * n := by
        intro j
        simp only [prev]
        split
        · simp; refine ⟨rnnSize_pos _ _ _ _, ?_⟩; rw [Nat.succ_mul]; omega
        · split
          · split
            · next hδ =>
              have hlt : t - (j - n) / m < t + 1 := Nat.lt_succ_of_le (Nat.sub_le _ _)
              have hle : t - (j - n) / m ≤ t := Nat.sub_le _ _
              obtain ⟨_, h2, h3, h4⟩ := ih (t - (j - n) / m) hlt ((j - n) % m)
              refine ⟨Nat.le_trans h2 (rnnSize_mono W M _ hle), Nat.le_trans h3 (Nat.mul_le_mul_left _ hle),
                Nat.le_trans h4 ?_⟩
              rw [Nat.succ_mul]; exact Nat.le_trans (Nat.mul_le_mul_right n hle) (Nat.le_add_right _ _)
            · simp; exact rnnSize_pos _ _ _ _
          · simp; exact rnnSize_pos _ _ _ _
      have hsd := compileNet_sd (W := W) cell hb prev (rnnSize W M cell.length t) (3 * cell.length * t)
        (fun j => (hprev j).1) (fun j => (hprev j).2.1) i
      have hmx := compileNet_max (W := W) cell prev ((t + 1) * n) (fun j => (hprev j).2.2) i
      refine ⟨fun x => ?_, ?_, ?_, ?_⟩
      · rw [wCirc_succ, wState_succ, eval_compileNet cell hv]
        congr 1
        funext j
        unfold winIn
        split
        · simp
        · split
          · split
            · next hδ => simp only [if_pos hδ]; exact (ih (t - (j - n) / m) (Nat.lt_succ_of_le (Nat.sub_le _ _)) ((j - n) % m)).1 x
            · next hδ => simp [hδ]
          · simp
      · rw [wCirc_succ]; simp only [rnnSize]; exact hsd.1
      · rw [wCirc_succ]; have := hsd.2; rw [Nat.mul_succ]; omega
      · rw [wCirc_succ]; exact hmx

/-- Closed polynomial size bound for a fixed number T of updates. -/
theorem window_size_closed (W M L T : Nat) :
    rnnSize W M L T + 1 ≤ 2 * ((2 * W + 3) ^ L * (M + 1) ^ (W * L)) ^ T := rnnSize_closed W M L T

/-! ## Gate-realised attention-style composition -/

theorem evalNet_append (ls1 ls2 : List Layer) (x : Nat → Bool) :
    evalNet (ls1 ++ ls2) x = evalNet ls2 (evalNet ls1 x) := by
  induction ls1 generalizing x with
  | nil => rfl
  | cons l ls ih => simp only [List.cons_append, evalNet]; exact ih _

/-- Staged evaluation: stages applied in order. -/
def runStages : List (List Layer) → (Nat → Bool) → (Nat → Bool)
  | [], x => x
  | st :: sts, x => runStages sts (evalNet st x)

theorem evalNet_flatten (sts : List (List Layer)) (x : Nat → Bool) : evalNet sts.flatten x = runStages sts x := by
  induction sts generalizing x with
  | nil => rfl
  | cons st sts ih => simp only [List.flatten_cons, evalNet_append, runStages]; exact ih _

theorem flatten_length_le {sts : List (List Layer)} {L : Nat} (h : ∀ st ∈ sts, st.length ≤ L) :
    sts.flatten.length ≤ sts.length * L := by
  induction sts with
  | nil => simp
  | cons st sts ih =>
    simp only [List.flatten_cons, List.length_append, List.length_cons, Nat.succ_mul]
    have := h st (by simp); have := ih (fun s hs => h s (by simp [hs])); omega

/-- GATE-REALISED COMPOSITION THEOREM.  If every stage is a W-valid network with at most L
    layers and widths/fan-ins ≤ M, the K-stage model is computed (on zero-extended n-bit
    inputs) by formulas of depth ≤ 3·K·L, size ≤ 2 (2W+3)^{KL} (M+1)^{W·KL}, reading only
    the n inputs; the formulas compute the staged evaluation. -/
theorem staged_ac0 {W M L : Nat} (sts : List (List Layer)) (hv : ∀ st ∈ sts, NetValid W st)
    (hb : ∀ st ∈ sts, NetBounded M st) (hl : ∀ st ∈ sts, st.length ≤ L) (n i : Nat) :
    (∀ x : Nat → Bool, eval x (netFormula W n sts.flatten i) = runStages sts (pad n x) i) ∧
    depth (netFormula W n sts.flatten i) ≤ 3 * (sts.length * L) ∧
    size (netFormula W n sts.flatten i) ≤ 2 * ((2 * W + 3) ^ (sts.length * L) * (M + 1) ^ (W * (sts.length * L))) ∧
    maxInput (netFormula W n sts.flatten i) ≤ n := by
  have hv' : NetValid W sts.flatten := by
    intro l hl' g hg
    obtain ⟨st, hst, hlst⟩ := List.mem_flatten.mp hl'
    exact hv st hst l hlst g hg
  have hb' : NetBounded M sts.flatten := by
    intro l hl'
    obtain ⟨st, hst, hlst⟩ := List.mem_flatten.mp hl'
    exact hb st hst l hlst
  obtain ⟨h1, h2, h3, h4⟩ := netFormula_spec n sts.flatten hv' hb' i
  have hlen := flatten_length_le hl
  refine ⟨fun x => by rw [h1, evalNet_flatten], Nat.le_trans h2 (Nat.mul_le_mul_left 3 hlen), Nat.le_trans h3 ?_, h4⟩
  apply Nat.mul_le_mul_left
  exact Nat.mul_le_mul (Nat.pow_le_pow_right (by omega) hlen)
    (Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_left W hlen))

/-- A {0,1}-coefficient majority gate on m inputs (threshold ⌈m/2⌉). -/
def majGate (m : Nat) : Gate := ⟨List.replicate m 1, List.replicate m false, (m + 1) / 2⟩

/-- Finite coefficients are not enough: the majority gate's threshold exceeds every fixed
    W once m > 2W, so it is outside the fixed-scale model although all its coefficients
    lie in {0,1}. -/
theorem majGate_not_valid (W m : Nat) (hm : 2 * W < m) : ¬ Gate.Valid W (majGate m) := by
  intro h; have := h.1; simp [majGate] at this; omega

theorem majGate_coeffs (m : Nat) : ∀ a ∈ (majGate m).coeffs, a ≤ 1 := by
  intro a ha; simp [majGate] at ha; omega

/-! ## Constant-size XOR and the literal remark -/

/-- XOR of a list of formulas (by repeated two-input XOR). -/
def xorChain : List Circ → Circ
  | [] => const false
  | c :: cs => CorrBridge.xor2 c (xorChain cs)

theorem xorChain_eval (z : Nat → Bool) : ∀ cs : List Circ, eval z (xorChain cs) = cs.foldr (fun c b => xor (eval z c) b) false
  | [] => by simp [xorChain]
  | c :: cs => by simp [xorChain, CorrBridge.eval_xor2, xorChain_eval z cs]

/-- XOR of t formulas of depth ≤ d and size ≤ s (s ≥ 1): depth ≤ d + 3t, size ≤ 6^t (s + 1). -/
theorem xorChain_res {d s : Nat} (hs : 1 ≤ s) : ∀ cs : List Circ, (∀ c ∈ cs, depth c ≤ d ∧ size c ≤ s) →
    depth (xorChain cs) ≤ d + 3 * cs.length ∧ size (xorChain cs) ≤ 6 ^ cs.length * (s + 1)
  | [], _ => by simp [xorChain]
  | c :: cs, h => by
    obtain ⟨ih1, ih2⟩ := xorChain_res hs cs (fun c' hc' => h c' (by simp [hc']))
    obtain ⟨hd, hsz⟩ := h c (by simp)
    obtain ⟨x1, x2, _⟩ := RolloutExec.xor2_res c (xorChain cs)
    simp only [xorChain, List.length_cons]
    refine ⟨by omega, ?_⟩
    rw [x2, Nat.pow_succ]
    have hp : 1 ≤ 6 ^ cs.length := Nat.one_le_pow _ _ (by decide)
    have : s + 1 ≤ 6 ^ cs.length * (s + 1) := Nat.le_mul_of_pos_left _ (by omega)
    have e : 6 ^ cs.length * 6 * (s + 1) = 6 * (6 ^ cs.length * (s + 1)) := by
      rw [Nat.mul_comm (6 ^ cs.length) 6, Nat.mul_assoc]
    rw [e]; omega

/-- Bitwise XOR of t blocks of B bits (block k occupies inputs B·k .. B·k + B − 1). -/
def blockXor (B t q : Nat) : Circ := xorChain ((List.range t).map (fun k => input (B * k + q)))

theorem blockXor_res (B t q : Nat) : depth (blockXor B t q) ≤ 3 * t ∧ size (blockXor B t q) ≤ 6 ^ t * 2 := by
  have := xorChain_res (d := 0) (s := 1) (by decide) ((List.range t).map (fun k => input (B * k + q)))
    (fun c hc => by obtain ⟨k, _, rfl⟩ := List.mem_map.mp hc; simp)
  simpa [blockXor] using this

/-- The literal-representation remark: replacing −a·x by a·(1 − x) adds a to the threshold. -/
theorem literal_shift (s a x θ : Int) : (θ ≤ s - a * x) ↔ (θ + a ≤ s + a * (1 - x)) := by
  rw [Int.mul_sub, Int.mul_one]; omega

/-! ## Axiom audit -/

#print axioms wState_succ
#print axioms wCirc_succ
#print axioms sizeBound_ge
#print axioms rnnSize_mono
#print axioms window_ac0
#print axioms window_size_closed
#print axioms evalNet_append
#print axioms evalNet_flatten
#print axioms flatten_length_le
#print axioms staged_ac0
#print axioms majGate_not_valid
#print axioms majGate_coeffs
#print axioms xorChain_eval
#print axioms xorChain_res
#print axioms blockXor_res
#print axioms literal_shift


