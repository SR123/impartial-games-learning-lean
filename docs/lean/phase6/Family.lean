import WholeGame

/- Phase 6, Priority 1a: family-level resource certificates.  Written by Claude
   (10 October 2026).  Lean 4.26.0, core/Std only.

   CONVENTIONS (stated once, used throughout phase 6).
   * A FAMILY is indexed by a type ι with an admissibility predicate `adm` (here: B ≥ 1,
     N ≥ 1, and j < B for policies; degenerate indices B = 0 or N = 0 are excluded from
     the asymptotic statements and remain covered by the finite phase-5 theorems).
   * `len i` is the ACTUAL supplied Boolean input length of member i: 2·B·N for the two
     frames, B·N for one board, B·N + B for a board with B outcome bits, and the
     per-update width 6 + 6B + 3r (state plus one token) for the recurrent controller.
   * Formulas are `AC0.Circ` trees: size counts every node (leaves, NOT, AND, OR); depth
     counts NOT.  A MULTI-OUTPUT member is a list of output formulas in a fixed order;
     its size is the TOTAL size of the list (no sharing between outputs), so the number
     of outputs is also polynomially bounded.
   * AC0Fam is NONUNIFORM: it asserts existence of the formulas for each member with a
     fixed depth bound d and a total-size bound c·len^k whose c, k do not depend on the
     member.  (The phase-6 members are given by explicit Lean definitions, but no
     DLOGTIME-uniformity claim is made.)
   * NetFam is the corresponding statement for fixed-scale threshold networks: fixed W,
     fixed layer bound L, valid gates, first layer wired to the len inputs, polynomial
     widths/fan-ins and gate count.
   Every certificate below is stated for the SAME object as its semantics theorem. -/

namespace NimAudit
namespace Family

open Game Rollout Prob Attain Recurrent AC0 AC0.Circ CorrBridge AttainCircuit Bridge SelectCircuit
  BinReadout Controller ControllerBits PriorityEncoder ThresholdNet ThresholdInst FiniteNet WholeGame

/-! ## Polynomial bounds over an indexed family -/

section Poly
variable {ι : Type}

/-- f is bounded by c·(len i)^k on admissible indices, with c and k fixed. -/
def PolyIn (adm : ι → Prop) (len : ι → Nat) (f : ι → Nat) : Prop :=
  ∃ c k : Nat, ∀ i, adm i → f i ≤ c * len i ^ k

theorem polyIn_const (adm : ι → Prop) (len : ι → Nat) (a : Nat) : PolyIn adm len (fun _ => a) :=
  ⟨a, 0, fun i _ => by simp⟩

theorem polyIn_leaf {adm : ι → Prop} {len : ι → Nat} {f : ι → Nat} (h : ∀ i, adm i → f i ≤ len i) :
    PolyIn adm len f :=
  ⟨1, 1, fun i hi => by simpa using h i hi⟩

theorem polyIn_add {adm : ι → Prop} {len : ι → Nat} (hpos : ∀ i, adm i → 1 ≤ len i) {f g : ι → Nat}
    (hf : PolyIn adm len f) (hg : PolyIn adm len g) : PolyIn adm len (fun i => f i + g i) := by
  obtain ⟨c1, k1, h1⟩ := hf
  obtain ⟨c2, k2, h2⟩ := hg
  refine ⟨c1 + c2, max k1 k2, fun i hi => ?_⟩
  have p1 : len i ^ k1 ≤ len i ^ max k1 k2 := Nat.pow_le_pow_right (hpos i hi) (Nat.le_max_left _ _)
  have p2 : len i ^ k2 ≤ len i ^ max k1 k2 := Nat.pow_le_pow_right (hpos i hi) (Nat.le_max_right _ _)
  have := h1 i hi
  have := h2 i hi
  have := Nat.mul_le_mul_left c1 p1
  have := Nat.mul_le_mul_left c2 p2
  show f i + g i ≤ (c1 + c2) * len i ^ max k1 k2
  rw [Nat.add_mul]
  omega

theorem polyIn_mul {adm : ι → Prop} {len : ι → Nat} {f g : ι → Nat}
    (hf : PolyIn adm len f) (hg : PolyIn adm len g) : PolyIn adm len (fun i => f i * g i) := by
  obtain ⟨c1, k1, h1⟩ := hf
  obtain ⟨c2, k2, h2⟩ := hg
  refine ⟨c1 * c2, k1 + k2, fun i hi => ?_⟩
  calc f i * g i ≤ (c1 * len i ^ k1) * (c2 * len i ^ k2) := Nat.mul_le_mul (h1 i hi) (h2 i hi)
    _ = c1 * c2 * len i ^ (k1 + k2) := by rw [Nat.mul_mul_mul_comm, Nat.pow_add]

theorem polyIn_pow {adm : ι → Prop} {len : ι → Nat} (m : Nat) {f : ι → Nat}
    (hf : PolyIn adm len f) : PolyIn adm len (fun i => f i ^ m) := by
  obtain ⟨c, k, h⟩ := hf
  refine ⟨c ^ m, k * m, fun i hi => ?_⟩
  calc f i ^ m ≤ (c * len i ^ k) ^ m := Nat.pow_le_pow_left (h i hi) m
    _ = c ^ m * len i ^ (k * m) := by rw [Nat.mul_pow, Nat.pow_mul]

theorem polyIn_mono {adm : ι → Prop} {len : ι → Nat} {f g : ι → Nat} (h : ∀ i, adm i → f i ≤ g i)
    (hg : PolyIn adm len g) : PolyIn adm len f := by
  obtain ⟨c, k, hk⟩ := hg
  exact ⟨c, k, fun i hi => Nat.le_trans (h i hi) (hk i hi)⟩

/-! Polynomial expressions by reflection (leaves are functions bounded by len). -/

inductive PE (ι : Type) where
  | c : Nat → PE ι
  | v : Nat → PE ι
  | add : PE ι → PE ι → PE ι
  | mul : PE ι → PE ι → PE ι
  | pow : PE ι → Nat → PE ι

instance : Add (PE ι) := ⟨PE.add⟩
instance : Mul (PE ι) := ⟨PE.mul⟩
instance : Pow (PE ι) Nat := ⟨PE.pow⟩
instance (n : Nat) : OfNat (PE ι) n := ⟨PE.c n⟩

def PE.eval (L : Nat → ι → Nat) : PE ι → ι → Nat
  | .c a, _ => a
  | .v k, i => L k i
  | .add a b, i => PE.eval L a i + PE.eval L b i
  | .mul a b, i => PE.eval L a i * PE.eval L b i
  | .pow a m, i => PE.eval L a i ^ m

/-- Every polynomial expression whose leaves are bounded by len is PolyIn. -/
theorem PE.poly {adm : ι → Prop} {len : ι → Nat} (hpos : ∀ i, adm i → 1 ≤ len i) (L : Nat → ι → Nat)
    (hL : ∀ k i, adm i → L k i ≤ len i) : ∀ e : PE ι, PolyIn adm len (PE.eval L e)
  | .c a => polyIn_const adm len a
  | .v k => polyIn_leaf (fun i hi => hL k i hi)
  | .add a b => polyIn_add hpos (PE.poly hpos L hL a) (PE.poly hpos L hL b)
  | .mul a b => polyIn_mul (PE.poly hpos L hL a) (PE.poly hpos L hL b)
  | .pow a m => polyIn_pow m (PE.poly hpos L hL a)

end Poly

/-! ## Family certificates -/

/-- Total formula size of a list of output formulas (no sharing). -/
def tsize (cs : List Circ) : Nat := (cs.map size).sum

theorem length_le_tsize (cs : List Circ) : cs.length ≤ tsize cs := by
  unfold tsize
  induction cs with
  | nil => simp
  | cons c cs ih => simp only [List.length_cons, List.map_cons, List.sum_cons]; have := Shared.size_pos' c; omega

/-- AC0 FAMILY CERTIFICATE (nonuniform, multi-output).  For every admissible member:
    the input length is positive, every output formula has depth ≤ d and reads only
    the first len inputs, and the total size of the outputs is ≤ c·len^k with c, k
    independent of the member. -/
structure AC0Fam {ι : Type} (adm : ι → Prop) (len : ι → Nat) (outs : ι → List Circ) (d : Nat) : Prop where
  pos : ∀ i, adm i → 1 ≤ len i
  depth_le : ∀ i, adm i → ∀ c ∈ outs i, depth c ≤ d
  reads : ∀ i, adm i → ∀ c ∈ outs i, maxInput c ≤ len i
  size_poly : PolyIn adm len (fun i => tsize (outs i))

/-- The number of outputs of an AC0 family is polynomially bounded as well. -/
theorem AC0Fam.outs_poly {ι : Type} {adm : ι → Prop} {len : ι → Nat} {outs : ι → List Circ} {d : Nat}
    (h : AC0Fam adm len outs d) : PolyIn adm len (fun i => (outs i).length) :=
  polyIn_mono (fun i _ => length_le_tsize (outs i)) h.size_poly

/-- NETWORK FAMILY CERTIFICATE: fixed grid W, at most L layers, valid gates, first layer
    reading only the len inputs, polynomial widths/fan-ins and polynomial gate count. -/
structure NetFam {ι : Type} (adm : ι → Prop) (len : ι → Nat) (net : ι → List Layer) (W L : Nat) : Prop where
  pos : ∀ i, adm i → 1 ≤ len i
  valid : ∀ i, adm i → NetValid W (net i)
  wired : ∀ i, adm i → Wired (len i) (net i)
  layers : ∀ i, adm i → (net i).length ≤ L
  bounded : ∃ c k, ∀ i, adm i → NetBounded (c * len i ^ k) (net i)
  gates : PolyIn adm len (fun i => gateCount (net i))

/-! ## Network families compile to AC0 families (same networks) -/

theorem netBounded_mono {M M' : Nat} {ls : List Layer} (h : NetBounded M ls) (hM : M ≤ M') : NetBounded M' ls :=
  fun l hl => ⟨Nat.le_trans (h l hl).1 hM, fun g hg => Nat.le_trans ((h l hl).2 g hg) hM⟩

/-- NETWORK-TO-AC0 AT FAMILY LEVEL.  If a network family satisfies NetFam with fixed W and
    L, then its first K i outputs (K polynomial) are computed by the compiled formulas
    netFormula W (len i) (net i), which form an AC0 family of depth ≤ 3L reading only the
    len inputs; on unpadded inputs the formulas equal the networks (Wired, nonempty). -/
theorem netFam_ac0 {ι : Type} {adm : ι → Prop} {len : ι → Nat} {net : ι → List Layer} {W L : Nat}
    (h : NetFam adm len net W L) (K : ι → Nat) (hK : PolyIn adm len K) :
    AC0Fam adm len (fun i => (List.range (K i)).map (netFormula W (len i) (net i))) (3 * L) ∧
    (∀ i, adm i → net i ≠ [] → ∀ o (x : Nat → Bool), eval x (netFormula W (len i) (net i) o) = evalNet (net i) x o) := by
  obtain ⟨c, k, hb⟩ := h.bounded
  have spec := fun i (hi : adm i) o => netFormula_spec (len i) (net i) (h.valid i hi) (hb i hi) o
  refine ⟨⟨h.pos, ?_, ?_, ?_⟩, ?_⟩
  · intro i hi c' hc
    obtain ⟨o, _, rfl⟩ := List.mem_map.mp hc
    have := (spec i hi o).2.1; have := h.layers i hi; omega
  · intro i hi c' hc
    obtain ⟨o, _, rfl⟩ := List.mem_map.mp hc
    exact (spec i hi o).2.2.2
  · -- each formula ≤ 2 (2W+3)^L (c len^k + 1)^(W L)
    have hpos := h.pos
    have hone : ∀ i, adm i → ∀ o, size (netFormula W (len i) (net i) o) ≤
        2 * ((2 * W + 3) ^ L * (c * len i ^ k + 1) ^ (W * L)) := by
      intro i hi o
      have h1 := (spec i hi o).2.2.1
      have hl := h.layers i hi
      have e1 : (2 * W + 3) ^ (net i).length ≤ (2 * W + 3) ^ L := Nat.pow_le_pow_right (by omega) hl
      have e2 : (c * len i ^ k + 1) ^ (W * (net i).length) ≤ (c * len i ^ k + 1) ^ (W * L) :=
        Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_left W hl)
      have := Nat.mul_le_mul e1 e2
      omega
    apply polyIn_mono (g := fun i => K i * (2 * ((2 * W + 3) ^ L * (c * len i ^ k + 1) ^ (W * L))))
    · intro i hi
      unfold tsize
      have := sum_map_le_mem (l := List.range (K i)) (f := fun o => size (netFormula W (len i) (net i) o))
        (g := fun _ => 2 * ((2 * W + 3) ^ L * (c * len i ^ k + 1) ^ (W * L))) (fun o _ => hone i hi o)
      rw [List.map_const', List.sum_replicate_nat, List.length_range] at this
      rw [List.map_map]
      exact this
    · apply polyIn_mul hK
      apply polyIn_mul (polyIn_const _ _ 2)
      apply polyIn_mul (polyIn_const _ _ _)
      apply polyIn_pow
      apply polyIn_add hpos _ (polyIn_const _ _ 1)
      apply polyIn_mul (polyIn_const _ _ c)
      apply polyIn_pow
      exact polyIn_leaf (fun i _ => Nat.le_refl _)
  · intro i hi hne o x
    exact (netFormula_wired (len i) (net i) (h.valid i hi) (hb i hi) (h.wired i hi) o
      (fun he => absurd he hne)).1 x

/-! ## Index width and parameter bounds -/

theorem log2_lt_self {N : Nat} (hN : 1 ≤ N) : N.log2 < N :=
  Nat.lt_of_lt_of_le Nat.lt_two_pow_self (Nat.log2_self_le (by omega))

theorem rIdx_le {N : Nat} (hN : 1 ≤ N) : rIdx N ≤ N := by
  have := log2_lt_self hN; unfold rIdx; omega

theorem rIdx_width (N : Nat) : N ≤ 2 ^ rIdx N := width_log N

theorem rIdx_counter (N : Nat) : N < 2 ^ rIdx N := Nat.lt_log2_self

/-- The output list of a binary selector has exactly 1 + r + B formulas and total size
    equal to `PriorityEncoder.totalSize`. -/
theorem tsize_bForms (S : BCirc) : tsize (bForms S) = PriorityEncoder.totalSize S := by
  simp [tsize, bForms, PriorityEncoder.totalSize, List.sum_append_nat]
  omega

theorem bForms_mem {S : BCirc} {N B r D Sz M : Nat} (h : BinBound S N B r D Sz M) :
    ∀ c ∈ bForms S, depth c ≤ D ∧ size c ≤ Sz ∧ maxInput c ≤ M := fun c hc => h.all c hc

/-- Generic certificate assembly for binary selectors with a BinBound. -/
theorem bin_cert {ι : Type} {adm : ι → Prop} {len : ι → Nat} {S : ι → BCirc}
    {N B r D Sz M : ι → Nat} {d : Nat}
    (hpos : ∀ i, adm i → 1 ≤ len i) (hb : ∀ i, adm i → BinBound (S i) (N i) (B i) (r i) (D i) (Sz i) (M i))
    (hD : ∀ i, adm i → D i ≤ d) (hM : ∀ i, adm i → M i ≤ len i)
    (hsize : PolyIn adm len (fun i => (1 + r i + B i) * Sz i)) :
    AC0Fam adm len (fun i => bForms (S i)) d := by
  refine ⟨hpos, fun i hi c hc => ?_, fun i hi c hc => ?_, ?_⟩
  · have := (bForms_mem (hb i hi) c hc).1; have := hD i hi; omega
  · have := (bForms_mem (hb i hi) c hc).2.2; have := hM i hi; omega
  · exact polyIn_mono (fun i hi => by rw [tsize_bForms]; exact PriorityEncoder.totalSize_le (hb i hi)) hsize

theorem wired_mono {n n' : Nat} {ls : List Layer} (h : Wired n ls) (hn : n ≤ n') : Wired n' ls := by
  cases ls with
  | nil => trivial
  | cons l _ => exact fun g hg => Nat.le_trans (h g hg) hn

/-- Generic network certificate for compiled binary selectors. -/
theorem binNet_cert {ι : Type} {adm : ι → Prop} {len : ι → Nat} {S : ι → BCirc}
    {N B r D Sz M : ι → Nat} {L : Nat}
    (hpos : ∀ i, adm i → 1 ≤ len i) (hb : ∀ i, adm i → BinBound (S i) (N i) (B i) (r i) (D i) (Sz i) (M i))
    (hD : ∀ i, adm i → 2 * D i + 2 ≤ L) (hM : ∀ i, adm i → M i ≤ len i)
    (hbd : ∃ c k, ∀ i, adm i → (1 + r i + B i) * Sz i + M i ≤ c * len i ^ k)
    (hg : PolyIn adm len (fun i => (2 * D i + 1) * ((1 + r i + B i) * Sz i) + (1 + r i + B i))) :
    NetFam adm len (fun i => binNet (S i)) 1 L := by
  refine ⟨hpos, fun i hi => (binNet_res (hb i hi)).1, fun i hi => ?_, fun i hi => ?_, ?_, ?_⟩
  · exact wired_mono (binNet_res (hb i hi)).2.1 (hM i hi)
  · have := (binNet_res (hb i hi)).2.2.1; have := hD i hi; omega
  · obtain ⟨c, k, h⟩ := hbd
    exact ⟨c, k, fun i hi => netBounded_mono (binNet_res (hb i hi)).2.2.2.1 (h i hi)⟩
  · exact polyIn_mono (fun i hi => (binNet_res (hb i hi)).2.2.2.2) hg

/-- PolyIn from a reflected polynomial expression (pointwise equality by computation). -/
theorem polyE {ι : Type} {adm : ι → Prop} {len : ι → Nat} (hpos : ∀ i, adm i → 1 ≤ len i)
    (L : Nat → ι → Nat) (hL : ∀ k i, adm i → L k i ≤ len i) (e : PE ι) (f : ι → Nat)
    (h : ∀ i, f i = PE.eval L e i) : PolyIn adm len f :=
  polyIn_mono (fun i _ => Nat.le_of_eq (h i)) (PE.poly hpos L hL e)

/-- Leaves for (B, N)-indexed families: 0 ↦ B, 1 ↦ N, otherwise ↦ r = log₂N + 1. -/
def leafBN : Nat → Nat × Nat → Nat
  | 0, i => i.1
  | 1, i => i.2
  | _, i => rIdx i.2

/-- Leaves for (B, (N, j))-indexed families. -/
def leafBNj : Nat → Nat × (Nat × Nat) → Nat
  | 0, i => i.1
  | 1, i => i.2.1
  | _, i => rIdx i.2.1

def vB {ι : Type} : PE ι := PE.v 0
def vN {ι : Type} : PE ι := PE.v 1
def vr {ι : Type} : PE ι := PE.v 2

/-! ## (i) Two-frame restoration: formulas and network -/

def restAdm : Nat × Nat → Prop := fun i => 1 ≤ i.1 ∧ 1 ≤ i.2
/-- Supplied input: the two frames, 2·B·N bits. -/
def restLen : Nat × Nat → Nat := fun i => 2 * (i.1 * i.2)
def restS (i : Nat × Nat) : BCirc := restBin i.1 i.2 (rIdx i.2)

theorem restLen_pos (i : Nat × Nat) (hi : restAdm i) : 1 ≤ restLen i := by
  have := Nat.mul_le_mul hi.1 hi.2; unfold restLen; omega
theorem rest_B (i : Nat × Nat) (hi : restAdm i) : i.1 ≤ restLen i := by
  have := Nat.mul_le_mul_left i.1 hi.2; unfold restLen; simp at this; omega
theorem rest_N (i : Nat × Nat) (hi : restAdm i) : i.2 ≤ restLen i := by
  have := Nat.mul_le_mul_right i.2 hi.1; unfold restLen; simp at this; omega
theorem rest_leaves (k : Nat) (i : Nat × Nat) (hi : restAdm i) : leafBN k i ≤ restLen i := by
  match k with
  | 0 => exact rest_B i hi
  | 1 => exact rest_N i hi
  | _ + 2 => exact Nat.le_trans (rIdx_le hi.2) (rest_N i hi)

/-- The size polynomial of the restoration selector (phase 5, restBin_bound). -/
def restSz (B N : Nat) : Nat :=
  4 * ((N + 2) * (12 * ((N + 2) * (B + 2) * (B * (2 * B + 3) + 9 + 2)) ^ 8 * (10 * N + 1 + 1) + 2)) ^ 3
def restSzE {ι : Type} : PE ι :=
  4 * ((vN + 2) * (12 * ((vN + 2) * (vB + 2) * (vB * (2 * vB + 3) + 9 + 2)) ^ 8 * (10 * vN + 1 + 1) + 2)) ^ 3

theorem rest_bound (i : Nat × Nat) :
    BinBound (restS i) i.2 i.1 (rIdx i.2) 20 (restSz i.1 i.2) (2 * (i.1 * i.2)) :=
  restBin_bound (rIdx_width i.2)

theorem rest_sizePoly : PolyIn restAdm restLen (fun i => (1 + rIdx i.2 + i.1) * restSz i.1 i.2) :=
  polyE restLen_pos leafBN rest_leaves ((1 + vr + vB) * restSzE) _ (fun _ => rfl)

/-- TWO-FRAME FORMULA FAMILY CERTIFICATE (depth ≤ 20, total size polynomial in 2BN,
    reading only the two frames). -/
theorem rest_ac0 : AC0Fam restAdm restLen (fun i => bForms (restS i)) 20 :=
  bin_cert restLen_pos (fun i _ => rest_bound i) (fun _ _ => Nat.le_refl _)
    (fun i _ => Nat.le_refl _) rest_sizePoly

def restN (i : Nat × Nat) : List Layer := restNet i.1 i.2 (rIdx i.2)

/-- TWO-FRAME NETWORK FAMILY CERTIFICATE (W = 1, ≤ 42 layers, polynomial widths/gates). -/
theorem rest_net : NetFam restAdm restLen restN 1 42 :=
  binNet_cert (S := restS) restLen_pos (fun i _ => rest_bound i) (fun _ _ => by omega)
    (fun i _ => Nat.le_refl _)
    (polyE restLen_pos leafBN rest_leaves ((1 + vr + vB) * restSzE + 2 * (vB * vN)) _ (fun _ => rfl))
    (polyE restLen_pos leafBN rest_leaves ((2 * 20 + 1) * ((1 + vr + vB) * restSzE) + (1 + vr + vB)) _
      (fun _ => rfl))

/-- Semantics of the SAME objects on the promised domain (previous nim-sum zero, legal
    transition): formulas and network output the restoring binary move. -/
theorem rest_semantics {B N : Nat} {Q Q' : List Nat} (hQ : Q.length = N) (hQ' : Q'.length = N)
    (hw : Width B Q) (hw' : Width B Q') (h0 : nimSum Q = 0) (hm : Move Q Q') :
    ∃ i v, binSem (restS (B, N)) N (LocalRestore.tf B N Q Q') = some (i, v) ∧
      netBinSem (restN (B, N)) N (rIdx N) B (LocalRestore.tf B N Q Q') = some (i, v) ∧
      restore Q Q' = some (Q'.set i v) ∧ Move Q' (Q'.set i v) ∧ nimSum (Q'.set i v) = 0 := by
  obtain ⟨i, v, h1, h2, h3, h4⟩ := restBin_correct (rIdx_width N) hQ hQ' hw hw' h0 hm
  have hb := restBin_bound (B := B) (N := N) (rIdx_width N)
  refine ⟨i, v, h1, ?_, h2, h3, h4⟩
  show netBinSem (binNet (restBin B N (rIdx N))) N (rIdx N) B (LocalRestore.tf B N Q Q') = some (i, v)
  rw [binNet_correct _ hb.idx_len hb.val_len]
  exact h1

/-! ## (ii) Multi-head: one policy step and the outcome-conditioned readout -/

/-- Policy members are indexed by (B, (N, j)). -/
def polAdm : Nat × (Nat × Nat) → Prop := fun i => 1 ≤ i.1 ∧ 1 ≤ i.2.1 ∧ i.2.2 < i.1
def polLen : Nat × (Nat × Nat) → Nat := fun i => i.1 * i.2.1
def polS (i : Nat × (Nat × Nat)) : BCirc := polBin i.1 i.2.1 i.2.2 (rIdx i.2.1)

def polSz (B N : Nat) : Nat := 4 * ((N + 2) * (12 * ((N + 2) * (B + 2) * (4 * B + 9 + 2)) ^ 8 + 2)) ^ 3
def polSzE {ι : Type} : PE ι := 4 * ((vN + 2) * (12 * ((vN + 2) * (vB + 2) * (4 * vB + 9 + 2)) ^ 8 + 2)) ^ 3

theorem polLen_pos (i : Nat × (Nat × Nat)) (hi : polAdm i) : 1 ≤ polLen i := by
  have := Nat.mul_le_mul hi.1 hi.2.1; unfold polLen; omega
theorem pol_B (i : Nat × (Nat × Nat)) (hi : polAdm i) : i.1 ≤ polLen i := by
  have := Nat.mul_le_mul_left i.1 hi.2.1; unfold polLen; simpa using this
theorem pol_N (i : Nat × (Nat × Nat)) (hi : polAdm i) : i.2.1 ≤ polLen i := by
  have := Nat.mul_le_mul_right i.2.1 hi.1; unfold polLen; simpa using this
theorem pol_leaves (k : Nat) (i : Nat × (Nat × Nat)) (hi : polAdm i) : leafBNj k i ≤ polLen i := by
  match k with
  | 0 => exact pol_B i hi
  | 1 => exact pol_N i hi
  | _ + 2 => exact Nat.le_trans (rIdx_le hi.2.1) (pol_N i hi)

theorem pol_bound (i : Nat × (Nat × Nat)) :
    BinBound (polS i) i.2.1 i.1 (rIdx i.2.1) 17 (polSz i.1 i.2.1) (i.1 * i.2.1) :=
  polBin_bound (rIdx_width i.2.1)

theorem pol_sizePoly : PolyIn polAdm polLen (fun i => (1 + rIdx i.2.1 + i.1) * polSz i.1 i.2.1) :=
  polyE polLen_pos leafBNj pol_leaves ((1 + vr + vB) * polSzE) _ (fun _ => rfl)

/-- ONE STRUCTURED POLICY STEP: formula family certificate (depth ≤ 17, input B·N). -/
theorem pol_ac0 : AC0Fam polAdm polLen (fun i => bForms (polS i)) 17 :=
  bin_cert polLen_pos (fun i _ => pol_bound i) (fun _ _ => Nat.le_refl _) (fun _ _ => Nat.le_refl _)
    pol_sizePoly

def polN (i : Nat × (Nat × Nat)) : List Layer := polNet i.1 i.2.1 i.2.2 (rIdx i.2.1)

theorem pol_net : NetFam polAdm polLen polN 1 36 :=
  binNet_cert (S := polS) polLen_pos (fun i _ => pol_bound i) (fun _ _ => by omega) (fun _ _ => Nat.le_refl _)
    (polyE polLen_pos leafBNj pol_leaves ((1 + vr + vB) * polSzE + vB * vN) _ (fun _ => rfl))
    (polyE polLen_pos leafBNj pol_leaves ((2 * 17 + 1) * ((1 + vr + vB) * polSzE) + (1 + vr + vB)) _
      (fun _ => rfl))

theorem pol_semantics {B N j : Nat} {P : List Nat} (hP : P.length = N) (hw : Width B P) :
    binSem (polS (B, N, j)) N (boardBits B P) = policyIdx j P ∧
    applyM P (netBinSem (polN (B, N, j)) N (rIdx N) B (boardBits B P)) = policyStep j P := by
  refine ⟨(polBin_correct (rIdx_width N) hP hw).1, ?_⟩
  exact polNet_correct (rIdx_width N) hP hw

/-- Readout members (board plus B outcome wires). -/
def mhAdm : Nat × Nat → Prop := restAdm
def mhLen : Nat × Nat → Nat := fun i => i.1 * i.2 + i.1
def mhS (i : Nat × Nat) : BCirc := mhBin i.1 i.2 (rIdx i.2)

def mhSz (B N : Nat) : Nat :=
  4 * ((N + 2) * (12 * ((N + 2) * (B + 2) * (B * (2 * B + 3) + 9 + 2)) ^ 8 * (9 + 1) + 2)) ^ 3
def mhSzE {ι : Type} : PE ι :=
  4 * ((vN + 2) * (12 * ((vN + 2) * (vB + 2) * (vB * (2 * vB + 3) + 9 + 2)) ^ 8 * (9 + 1) + 2)) ^ 3

theorem mhLen_pos (i : Nat × Nat) (hi : mhAdm i) : 1 ≤ mhLen i := by
  have := hi.1; unfold mhLen; omega
theorem mh_B (i : Nat × Nat) (_hi : mhAdm i) : i.1 ≤ mhLen i := by unfold mhLen; omega
theorem mh_N (i : Nat × Nat) (hi : mhAdm i) : i.2 ≤ mhLen i := by
  have := Nat.mul_le_mul_right i.2 hi.1; unfold mhLen; simp at this; omega
theorem mh_leaves (k : Nat) (i : Nat × Nat) (hi : mhAdm i) : leafBN k i ≤ mhLen i := by
  match k with
  | 0 => exact mh_B i hi
  | 1 => exact mh_N i hi
  | _ + 2 => exact Nat.le_trans (rIdx_le hi.2) (mh_N i hi)

theorem mh_bound (i : Nat × Nat) :
    BinBound (mhS i) i.2 i.1 (rIdx i.2) 19 (mhSz i.1 i.2) (i.1 * i.2 + i.1) :=
  mhBin_bound (rIdx_width i.2)

theorem mh_sizePoly : PolyIn mhAdm mhLen (fun i => (1 + rIdx i.2 + i.1) * mhSz i.1 i.2) :=
  polyE mhLen_pos leafBN mh_leaves ((1 + vr + vB) * mhSzE) _ (fun _ => rfl)

/-- OUTCOME-CONDITIONED READOUT: formula family certificate (depth ≤ 19, input B·N + B). -/
theorem mh_ac0 : AC0Fam mhAdm mhLen (fun i => bForms (mhS i)) 19 :=
  bin_cert mhLen_pos (fun i _ => mh_bound i) (fun _ _ => Nat.le_refl _) (fun _ _ => Nat.le_refl _) mh_sizePoly

def mhN (i : Nat × Nat) : List Layer := mhNet i.1 i.2 (rIdx i.2)

theorem mh_net : NetFam mhAdm mhLen mhN 1 40 :=
  binNet_cert (S := mhS) mhLen_pos (fun i _ => mh_bound i) (fun _ _ => by omega) (fun _ _ => Nat.le_refl _)
    (polyE mhLen_pos leafBN mh_leaves ((1 + vr + vB) * mhSzE + (vB * vN + vB)) _ (fun _ => rfl))
    (polyE mhLen_pos leafBN mh_leaves ((2 * 19 + 1) * ((1 + vr + vB) * mhSzE) + (1 + vr + vB)) _
      (fun _ => rfl))

/-- Readout semantics for ARBITRARY outcome wires o (reconstruction then selection), and
    for executed outcomes; formulas and network agree. -/
theorem mh_semantics {B N : Nat} {P : List Nat} (hP : P.length = N) (hw : Width B P) (o : Nat → Bool) :
    binSem (mhS (B, N)) N (obsIn B N P o) = attainT (reconstruct B o) P ∧
    netBinSem (mhN (B, N)) N (rIdx N) B (obsIn B N P o) = attainT (reconstruct B o) P ∧
    netBinSem (mhN (B, N)) N (rIdx N) B (obsIn B N P (outcomes P)) = decisionMove P := by
  have hb := mhBin_bound (B := B) (N := N) (rIdx_width N)
  have h1 := mhBin_correct (rIdx_width N) hP hw o
  refine ⟨h1, ?_, mhNet_correct (rIdx_width N) hP hw⟩
  show netBinSem (binNet (mhBin B N (rIdx N))) N (rIdx N) B (obsIn B N P o) = attainT (reconstruct B o) P
  rw [binNet_correct _ hb.idx_len hb.val_len]
  exact h1

/-! ## (iii) Recurrent controller: one update (state plus one token) -/

def ctrlAdm : Nat × Nat → Prop := restAdm
/-- Per-update input: state (4 + 5B + 3r bits) plus one token (2 + B bits), r = log₂N + 1. -/
def ctrlLen : Nat × Nat → Nat := fun i => inWidth i.1 (rIdx i.2)
def ctrlF (i : Nat × Nat) : List Circ := ctrlForms i.1 (rIdx i.2)

theorem ctrl_widths (B N : Nat) :
    inWidth B (rIdx N) = stateWidth B (rIdx N) + (2 + B) ∧
    (ctrlForms B (rIdx N)).length = stateWidth B (rIdx N) + outCount B (rIdx N) ∧
    stateWidth B (rIdx N) = 7 + 5 * B + 3 * N.log2 ∧ outCount B (rIdx N) = 5 + 3 * B + N.log2 ∧
    N < 2 ^ rIdx N := by
  refine ⟨by simp [inWidth, stateWidth]; omega, ctrlForms_length _ _, (counter_width (B := B) N).2,
    by simp [outCount, rIdx]; omega, rIdx_counter N⟩

/-- Leaves for the controller: 0 ↦ B, otherwise ↦ r = log₂N + 1 (N itself is not a leaf:
    the per-update width is logarithmic in N). -/
def leafBr : Nat → Nat × Nat → Nat
  | 0, i => i.1
  | _, i => rIdx i.2

def vR {ι : Type} : PE ι := PE.v 1

theorem ctrlLen_pos (i : Nat × Nat) (_hi : ctrlAdm i) : 1 ≤ ctrlLen i := by unfold ctrlLen inWidth; omega
theorem ctrl_leaves (k : Nat) (i : Nat × Nat) (_hi : ctrlAdm i) : leafBr k i ≤ ctrlLen i := by
  match k with
  | 0 => show i.1 ≤ inWidth i.1 (rIdx i.2); unfold inWidth; omega
  | _ + 1 => show rIdx i.2 ≤ inWidth i.1 (rIdx i.2); unfold inWidth; omega

def ctrlSzE {ι : Type} : PE ι :=
  ((4 + 5 * vB + 3 * vR) + (4 + 3 * vB + vR)) * (((vB * (2 * vB + 3) + 1) + 5 * vB + 2 * vR + 40) + 16)

/-- RECURRENT UPDATE: formula family certificate (depth ≤ 8, input = state + token,
    total size polynomial in that width, hence in B + log N). -/
theorem ctrl_ac0 : AC0Fam ctrlAdm ctrlLen ctrlF 8 := by
  refine ⟨ctrlLen_pos, fun i _ c hc => (ctrlForms_res _ _ c hc).1, fun i _ c hc => (ctrlForms_res _ _ c hc).2.2, ?_⟩
  exact polyIn_mono (fun i _ => ctrlForms_size _ _) (polyE ctrlLen_pos leafBr ctrl_leaves ctrlSzE _ (fun _ => rfl))

def ctrlN (i : Nat × Nat) : List Layer := ctrlNet i.1 (rIdx i.2)

theorem ctrl_net : NetFam ctrlAdm ctrlLen ctrlN 1 18 := by
  refine ⟨ctrlLen_pos, fun i _ => (ctrlNet_res _ _).1, fun i _ => (ctrlNet_res _ _).2.1,
    fun i _ => (ctrlNet_res _ _).2.2.1, ?_, ?_⟩
  · obtain ⟨c, k, h⟩ := polyE ctrlLen_pos leafBr ctrl_leaves (ctrlSzE + (6 + 6 * vB + 3 * vR))
      (fun i => (stateWidth i.1 (rIdx i.2) + outCount i.1 (rIdx i.2)) * (cellSize i.1 (rIdx i.2) + 16) +
        inWidth i.1 (rIdx i.2)) (fun _ => rfl)
    refine ⟨c, k, fun i hi => netBounded_mono (ctrlNet_res _ _).2.2.2.1 ?_⟩
    have h5 := (ctrlNet_res i.1 (rIdx i.2)).2.2.2.2.2
    have h6 := h i hi
    dsimp only at h6
    unfold ctrlLen at h6 ⊢; omega
  · refine polyIn_mono (fun i _ => ?_) (polyE ctrlLen_pos leafBr ctrl_leaves
      (17 * ctrlSzE + ((4 + 5 * vB + 3 * vR) + (4 + 3 * vB + vR)))
      (fun i => 17 * ((stateWidth i.1 (rIdx i.2) + outCount i.1 (rIdx i.2)) * (cellSize i.1 (rIdx i.2) + 16)) +
        (stateWidth i.1 (rIdx i.2) + outCount i.1 (rIdx i.2))) (fun _ => rfl))
    have h1 := (ctrlNet_res i.1 (rIdx i.2)).2.2.2.2.1
    have h3 := (ctrlNet_res i.1 (rIdx i.2)).2.2.2.2.2
    have := Nat.mul_le_mul_left 17 h3
    show gateCount (ctrlNet i.1 (rIdx i.2)) ≤ _
    omega

/-- Semantics of the SAME update formulas/network: for EVERY state vector v and token t,
    the formulas give the bit-level update bstep, and the network equals it. -/
theorem ctrl_semantics (B N : Nat) (v : Nat → Bool) (t : Tok) :
    (∀ k (hk : k < stateWidth B (rIdx N)),
      eval (inp B (rIdx N) v t) ((ctrlF (B, N))[k]'(by
        show k < (ctrlForms B (rIdx N)).length; rw [ctrlForms_length]; omega)) =
        (bstep B (rIdx N) v t).1 k) ∧
    tstep B (rIdx N) v t = bstep B (rIdx N) v t := by
  refine ⟨fun k hk => ?_, tstep_eq _ _ v t⟩
  simp only [ctrlF]
  rw [ctrlForms_get, if_pos hk]
  rfl

/-! ## Axiom audit -/

#print axioms polyIn_const
#print axioms polyIn_leaf
#print axioms polyIn_add
#print axioms polyIn_mul
#print axioms polyIn_pow
#print axioms polyIn_mono
#print axioms PE.poly
#print axioms length_le_tsize
#print axioms AC0Fam.outs_poly
#print axioms netBounded_mono
#print axioms netFam_ac0
#print axioms log2_lt_self
#print axioms rIdx_le
#print axioms rIdx_width
#print axioms rIdx_counter
#print axioms tsize_bForms
#print axioms bForms_mem
#print axioms bin_cert
#print axioms wired_mono
#print axioms binNet_cert
#print axioms polyE
#print axioms restLen_pos
#print axioms rest_B
#print axioms rest_N
#print axioms rest_leaves
#print axioms rest_bound
#print axioms rest_sizePoly
#print axioms rest_ac0
#print axioms rest_net
#print axioms rest_semantics
#print axioms polLen_pos
#print axioms pol_B
#print axioms pol_N
#print axioms pol_leaves
#print axioms pol_bound
#print axioms pol_sizePoly
#print axioms pol_ac0
#print axioms pol_net
#print axioms pol_semantics
#print axioms mhLen_pos
#print axioms mh_B
#print axioms mh_N
#print axioms mh_leaves
#print axioms mh_bound
#print axioms mh_sizePoly
#print axioms mh_ac0
#print axioms mh_net
#print axioms mh_semantics
#print axioms ctrl_widths
#print axioms ctrlLen_pos
#print axioms ctrl_leaves
#print axioms ctrl_ac0
#print axioms ctrl_net
#print axioms ctrl_semantics


