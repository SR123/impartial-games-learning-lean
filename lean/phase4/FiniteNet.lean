import Circuit

/- Phase 4, Priority 1: finite-input network simulation.  Written by Claude
   (10 October 2026).  Lean 4.26.0, core/Std only.

   Repair of the phase-3 specification gap found by the audit: `network_ac0` bounded
   the inputs of a clipped formula, while correctness/depth/size were proved for the
   unclipped one.  Here ONE formula, `netFormula W n ls i = compileNet W ls (clip n) i`,
   carries all four properties:
     * semantics: it computes the network on the n-bit input, zero-extended
       (explicit finite-input semantics `pad n x`);
     * depth ≤ 3L, size ≤ 2 (2W+3)^L (M+1)^(WL);
     * it reads only inputs 0..n-1 (maxInput ≤ n).
   For WIRED networks (first-layer fan-in ≤ n) the zero-extension is irrelevant and
   the same formula computes the unpadded network (outputs i < n for zero layers).
   The audit's one-layer counterexample violates the wiring premise and is handled
   by the padded semantics (`audit_example`).  Families with polynomially many output
   bits get per-output and total formula-size bounds. -/

namespace NimAudit
namespace FiniteNet

open AC0 AC0.Circ

/-- Zero-extension of an n-bit assignment. -/
def pad (n : Nat) (x : Nat → Bool) : Nat → Bool := fun j => if j < n then x j else false

/-- Input leaves for an n-bit input: variables 0..n-1, constant false beyond. -/
def clip (n : Nat) : Nat → Circ := fun j => if j < n then input j else const false

/-- THE compiled formula for output i of network ls on n inputs. -/
def netFormula (W n : Nat) (ls : List Layer) (i : Nat) : Circ := compileNet W ls (clip n) i

theorem eval_clip (x : Nat → Bool) (n j : Nat) : eval x (clip n j) = pad n x j := by
  unfold clip pad; split <;> simp

theorem clip_size (n j : Nat) : size (clip n j) ≤ 1 := by unfold clip; split <;> simp
theorem clip_depth (n j : Nat) : depth (clip n j) ≤ 0 := by unfold clip; split <;> simp
theorem clip_max (n j : Nat) : maxInput (clip n j) ≤ n := by
  unfold clip; split <;> simp <;> omega

/-- FINITE-INPUT SIMULATION THEOREM (same formula for all four properties).
    For a valid network of L = ls.length layers with fan-ins and widths ≤ M and any
    input length n, output i is computed (on zero-extended n-bit inputs) by
    netFormula W n ls i, which has depth ≤ 3L, size ≤ 2 (2W+3)^L (M+1)^(WL) and reads
    only inputs < n. -/
theorem netFormula_spec {W M : Nat} (n : Nat) (ls : List Layer) (hv : NetValid W ls)
    (hb : NetBounded M ls) (i : Nat) :
    (∀ x : Nat → Bool, eval x (netFormula W n ls i) = evalNet ls (pad n x) i) ∧
    depth (netFormula W n ls i) ≤ 3 * ls.length ∧
    size (netFormula W n ls i) ≤ 2 * ((2 * W + 3) ^ ls.length * (M + 1) ^ (W * ls.length)) ∧
    maxInput (netFormula W n ls i) ≤ n := by
  have hsd := compileNet_sd (W := W) ls hb (clip n) 1 0 (clip_size n) (clip_depth n) i
  refine ⟨?_, ?_, ?_, compileNet_max ls (clip n) n (clip_max n) i⟩
  · intro x
    unfold netFormula
    rw [eval_compileNet ls hv]
    congr 1
    funext j
    exact eval_clip x n j
  · have := hsd.2; unfold netFormula; omega
  · have h1 := sizeBound_closed W M ls.length
    have h2 := hsd.1
    unfold netFormula; omega

/-- The formula depends only on the first n input bits. -/
theorem netFormula_local {W M : Nat} (n : Nat) (ls : List Layer) (hb : NetBounded M ls) (i : Nat)
    (x y : Nat → Bool) (hxy : ∀ j, j < n → x j = y j) :
    eval x (netFormula W n ls i) = eval y (netFormula W n ls i) :=
  eval_congr_below x y _ (fun j hj =>
    hxy j (Nat.lt_of_lt_of_le hj (compileNet_max ls (clip n) n (clip_max n) i)))

/-! ## Wired networks: unpadded semantics -/

/-- First-layer gates read only the n input bits. -/
def Wired (n : Nat) : List Layer → Prop
  | [] => True
  | l :: _ => ∀ g ∈ l, g.fanin ≤ n

theorem gate_eval_congr (g : Gate) (z z' : Nat → Bool) (h : ∀ j, j < g.fanin → z j = z' j) :
    g.eval z = g.eval z' := by
  unfold Gate.eval Gate.wsum Gate.psum
  congr 2
  have : ∀ j ∈ List.range g.fanin, g.coeff j * (if g.lit z j then 1 else 0) =
      g.coeff j * (if g.lit z' j then 1 else 0) := by
    intro j hj
    unfold Gate.lit
    rw [h j (List.mem_range.mp hj)]
  rw [List.map_congr_left this]

theorem evalLayer_congr (l : Layer) (n : Nat) (hl : ∀ g ∈ l, g.fanin ≤ n) (z z' : Nat → Bool)
    (h : ∀ j, j < n → z j = z' j) : evalLayer l z = evalLayer l z' := by
  funext i
  unfold evalLayer
  cases hi : l[i]? with
  | none => rfl
  | some g =>
    simp only
    exact gate_eval_congr g z z' (fun j hj =>
      h j (Nat.lt_of_lt_of_le hj (hl g (List.mem_of_getElem? hi))))

/-- For wired networks the zero-extension does not change any output (outputs
    i < n in the zero-layer case). -/
theorem wired_pad (n : Nat) (ls : List Layer) (hw : Wired n ls) (x : Nat → Bool) (i : Nat)
    (hi : ls = [] → i < n) : evalNet ls (pad n x) i = evalNet ls x i := by
  cases ls with
  | nil => simp [evalNet, pad, hi rfl]
  | cons l ls =>
    simp only [evalNet]
    rw [evalLayer_congr l n hw (pad n x) x (fun j hj => by simp [pad, hj])]

/-- WIRED SIMULATION THEOREM: for a wired valid network the SAME formula computes
    the unpadded network on every assignment, with the same depth/size/input bounds. -/
theorem netFormula_wired {W M : Nat} (n : Nat) (ls : List Layer) (hv : NetValid W ls)
    (hb : NetBounded M ls) (hw : Wired n ls) (i : Nat) (hi : ls = [] → i < n) :
    (∀ x : Nat → Bool, eval x (netFormula W n ls i) = evalNet ls x i) ∧
    depth (netFormula W n ls i) ≤ 3 * ls.length ∧
    size (netFormula W n ls i) ≤ 2 * ((2 * W + 3) ^ ls.length * (M + 1) ^ (W * ls.length)) ∧
    maxInput (netFormula W n ls i) ≤ n := by
  obtain ⟨h1, h2, h3, h4⟩ := netFormula_spec n ls hv hb i
  exact ⟨fun x => by rw [h1, wired_pad n ls hw x i hi], h2, h3, h4⟩

/-! ## The audit counterexample -/

def probeNet : List Layer := [[⟨[0, 1], [false, false], 1⟩]]

/-- The audit's network is not wired for n = 1 (it reads input 1). -/
theorem probe_not_wired : ¬ Wired 1 probeNet := by
  intro h
  have := h ⟨[0, 1], [false, false], 1⟩ (by simp [probeNet])
  simp [Gate.fanin] at this

/-- Under the explicit finite-input semantics the audit network on n = 1 inputs is
    the constant-false function, and netFormula computes exactly that while reading
    only input 0. -/
theorem audit_example (x : Nat → Bool) :
    eval x (netFormula 1 1 probeNet 0) = false ∧ maxInput (netFormula 1 1 probeNet 0) ≤ 1 := by
  have hv : NetValid 1 probeNet := by simp [NetValid, probeNet, Gate.Valid]
  have hb : NetBounded 2 probeNet := by simp [NetBounded, probeNet, Gate.fanin]
  obtain ⟨h1, _, _, h4⟩ := netFormula_spec 1 probeNet hv hb 0
  refine ⟨?_, h4⟩
  rw [h1]
  have : pad 1 x 1 = false := by simp [pad]
  simp only [probeNet, evalNet, evalLayer, List.getElem?_cons_zero, Gate.eval, Gate.wsum,
    Gate.psum, Gate.fanin, Gate.coeff, Gate.lit]
  simp [List.range_succ, this]

/-! ## Families with polynomially many output bits -/

/-- Total formula size of the first K outputs (no sharing between outputs). -/
def totalSize (W n : Nat) (ls : List Layer) (K : Nat) : Nat :=
  ((List.range K).map (fun i => size (netFormula W n ls i))).sum

theorem totalSize_le {W M : Nat} (n : Nat) (ls : List Layer) (hv : NetValid W ls)
    (hb : NetBounded M ls) (K : Nat) :
    totalSize W n ls K ≤ K * (2 * ((2 * W + 3) ^ ls.length * (M + 1) ^ (W * ls.length))) := by
  unfold totalSize
  have h := sum_map_le_mem (l := List.range K) (f := fun i => size (netFormula W n ls i))
    (g := fun _ => 2 * ((2 * W + 3) ^ ls.length * (M + 1) ^ (W * ls.length)))
    (fun i _ => (netFormula_spec n ls hv hb i).2.2.1)
  rw [List.map_const', List.sum_replicate_nat, List.length_range] at h
  exact h

/-- FINITE-INPUT FAMILY THEOREM.  Fix W, L, c, k, c', k'.  For each input length n let
    net n be a valid network with exactly L layers whose fan-ins and widths are
    ≤ c (n+1)^k, with K n ≤ c' (n+1)^k' designated output bits.  Then each output i
    is computed (zero-extended n-bit semantics) by one formula that reads only
    inputs < n, has depth ≤ 3L and size ≤ 2 (2W+3)^L (c+1)^(WL) (n+1)^(kWL); the
    total size of the K n output formulas is ≤ c'(n+1)^k' times that bound. -/
theorem family_finite {W L c k c' k' : Nat} (net : Nat → List Layer) (K : Nat → Nat)
    (hlen : ∀ n, (net n).length = L) (hv : ∀ n, NetValid W (net n))
    (hb : ∀ n, NetBounded (c * (n + 1) ^ k) (net n)) (hK : ∀ n, K n ≤ c' * (n + 1) ^ k')
    (n : Nat) :
    (∀ i, (∀ x : Nat → Bool, eval x (netFormula W n (net n) i) = evalNet (net n) (pad n x) i) ∧
      depth (netFormula W n (net n) i) ≤ 3 * L ∧
      size (netFormula W n (net n) i) ≤
        2 * ((2 * W + 3) ^ L * ((c + 1) ^ (W * L) * (n + 1) ^ (k * (W * L)))) ∧
      maxInput (netFormula W n (net n) i) ≤ n) ∧
    totalSize W n (net n) (K n) ≤
      c' * (n + 1) ^ k' * (2 * ((2 * W + 3) ^ L * ((c + 1) ^ (W * L) * (n + 1) ^ (k * (W * L))))) := by
  have hM : (c * (n + 1) ^ k + 1) ^ (W * L) ≤ (c + 1) ^ (W * L) * (n + 1) ^ (k * (W * L)) := by
    have hp : c * (n + 1) ^ k + 1 ≤ (c + 1) * (n + 1) ^ k := by
      have : 1 ≤ (n + 1) ^ k := Nat.pow_pos (by omega)
      generalize (n + 1) ^ k = p at *
      have e : (c + 1) * p = c * p + p := by rw [Nat.add_mul, Nat.one_mul]
      rw [e]; omega
    calc (c * (n + 1) ^ k + 1) ^ (W * L) ≤ ((c + 1) * (n + 1) ^ k) ^ (W * L) :=
          Nat.pow_le_pow_left hp _
      _ = (c + 1) ^ (W * L) * (n + 1) ^ (k * (W * L)) := by
          rw [Nat.mul_pow, ← Nat.pow_mul, Nat.mul_comm k]
  have hbound : 2 * ((2 * W + 3) ^ (net n).length * (c * (n + 1) ^ k + 1) ^ (W * (net n).length)) ≤
      2 * ((2 * W + 3) ^ L * ((c + 1) ^ (W * L) * (n + 1) ^ (k * (W * L)))) := by
    rw [hlen]
    exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hM)
  refine ⟨fun i => ?_, ?_⟩
  · obtain ⟨h1, h2, h3, h4⟩ := netFormula_spec n (net n) (hv n) (hb n) i
    rw [hlen] at h2
    exact ⟨h1, h2, Nat.le_trans h3 hbound, h4⟩
  · have := totalSize_le n (net n) (hv n) (hb n) (K n)
    exact Nat.le_trans this (Nat.mul_le_mul (hK n) hbound)


/-! ## Axiom audit -/

#print axioms eval_clip
#print axioms clip_size
#print axioms clip_depth
#print axioms clip_max
#print axioms netFormula_spec
#print axioms netFormula_local
#print axioms gate_eval_congr
#print axioms evalLayer_congr
#print axioms wired_pad
#print axioms netFormula_wired
#print axioms probe_not_wired
#print axioms audit_example
#print axioms totalSize_le
#print axioms family_finite
end FiniteNet
end NimAudit
