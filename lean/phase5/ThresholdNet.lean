import SharedCircuit
import FiniteNet

/- Phase 5, task 2: compiling bounded-depth Boolean formulas into the paper's
   fixed-scale literal-threshold networks (the existing AC0.Gate / Layer / evalNet
   model), in the direction opposite to Circuit.compileNet.  Written by Claude
   (10 October 2026).  Lean 4.26.0, core/Std only.

   Gates used (W = 1, i.e. the fixed grid with denominator D = 1):
     * OR of literals: coefficients in {0,1}, one negation flag, threshold 1;
     * constants: no inputs, threshold 0 (true) or 1 (false).
   AND is never realised by a threshold equal to its fan-in: an AND node takes two
   layers, OR of negated children (= NOT AND) followed by OR of the negated result
   (De Morgan).  NOT costs one layer (an OR of one negated literal).

   Construction.  The formulas are first laid out as one shared gate program
   (SharedCircuit.emitL, one gate per formula node).  Every layer has one wire per
   program gate (width S); gate g is computed at layer lvl(g) (inputs and constants
   at layer 1, NOT and OR one layer above their children, AND two layers above),
   and identity buffers carry each value to all later layers.  A final layer copies
   the K output gates to wires 0, …, K−1.  Layer 1 reads the n input wires only
   through single-literal buffers of input i (fan-in i + 1 ≤ n).
   Proved for the one compiled network `compileF n cs`: exact outputs on every input,
   NetValid 1, Wired n, exactly 2D + 2 layers for depth bound D, width and fan-in
   ≤ S + n, and gate count (2D+1)·S + K, where S = Σ size(c_k). -/

namespace NimAudit
namespace ThresholdNet

open AC0 AC0.Circ Shared FiniteNet

/-! ## The two gate shapes -/

/-- OR of the literals (z j XOR ng) over the wires j < K with sel j. -/
def orGate (K : Nat) (sel : Nat → Bool) (ng : Bool) : Gate :=
  ⟨(List.range K).map (fun j => if sel j then 1 else 0), (List.range K).map (fun _ => ng), 1⟩

/-- Constant gate (no inputs). -/
def constGate (b : Bool) : Gate := ⟨[], [], if b then 0 else 1⟩

theorem sum_range_pos (f : Nat → Nat) : ∀ K, 1 ≤ ((List.range K).map f).sum ↔ ∃ j < K, 1 ≤ f j
  | 0 => by simp
  | K + 1 => by
    have ih := sum_range_pos f K
    rw [List.range_succ, List.map_append, List.sum_append_nat]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
    constructor
    · intro h
      by_cases h1 : 1 ≤ f K
      · exact ⟨K, by omega, h1⟩
      · obtain ⟨j, hj, hf⟩ := ih.1 (by omega)
        exact ⟨j, by omega, hf⟩
    · rintro ⟨j, hj, hf⟩
      by_cases hjK : j = K
      · subst hjK; omega
      · have := ih.2 ⟨j, by omega, hf⟩; omega

theorem orGate_eval (K : Nat) (sel : Nat → Bool) (ng : Bool) (z : Nat → Bool) :
    (orGate K sel ng).eval z = decide (∃ j < K, sel j = true ∧ xor (z j) ng = true) := by
  unfold Gate.eval Gate.wsum Gate.psum Gate.fanin orGate
  simp only [List.length_map, List.length_range]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_iff]
  have e : ∀ j ∈ List.range K, (Gate.coeff ⟨(List.range K).map (fun j => if sel j then 1 else 0),
      (List.range K).map (fun _ => ng), 1⟩ j) * (if Gate.lit ⟨(List.range K).map (fun j => if sel j then 1 else 0),
      (List.range K).map (fun _ => ng), 1⟩ z j then 1 else 0) =
      (if sel j = true ∧ xor (z j) ng = true then 1 else 0) := by
    intro j hj
    have hj' := List.mem_range.mp hj
    simp only [Gate.coeff, Gate.lit, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj',
      Option.map_some, Option.getD_some]
    cases sel j <;> cases xor (z j) ng <;> simp
  rw [List.map_congr_left e, sum_range_pos]
  constructor
  · rintro ⟨j, hj, h⟩; refine ⟨j, hj, ?_⟩; split at h <;> simp_all
  · rintro ⟨j, hj, h⟩; exact ⟨j, hj, by simp [h]⟩

theorem constGate_eval (b : Bool) (z : Nat → Bool) : (constGate b).eval z = b := by
  cases b <;> simp [constGate, Gate.eval, Gate.wsum, Gate.psum, Gate.fanin]

theorem orGate_valid (K : Nat) (sel : Nat → Bool) (ng : Bool) : Gate.Valid 1 (orGate K sel ng) := by
  refine ⟨by simp [orGate], ?_⟩
  intro a ha
  simp only [orGate, List.mem_map, List.mem_range] at ha
  obtain ⟨j, _, rfl⟩ := ha
  split <;> omega

theorem constGate_valid (b : Bool) : Gate.Valid 1 (constGate b) := by
  refine ⟨by cases b <;> simp [constGate], by simp [constGate]⟩

theorem orGate_fanin (K : Nat) (sel : Nat → Bool) (ng : Bool) : (orGate K sel ng).fanin = K := by
  simp [orGate, Gate.fanin]

theorem constGate_fanin (b : Bool) : (constGate b).fanin = 0 := rfl

/-! ## Levels of program gates -/

/-- Layer at which a program gate is available: 1 for inputs/constants, +1 for NOT
    and OR, +2 for AND (De Morgan). -/
def lvlAlg : Alg Nat := ⟨0, fun _ => 1, fun _ => 1, (· + 1), fun l => listMax l + 2, fun l => listMax l + 1⟩

mutual
def lvl : Circ → Nat
  | .input _ => 1
  | .const _ => 1
  | .not c => lvl c + 1
  | .and cs => lvlL cs + 2
  | .or cs => lvlL cs + 1
def lvlL : List Circ → Nat
  | [] => 0
  | c :: cs => max (lvl c) (lvlL cs)
end

theorem lvlL_eq : ∀ cs : List Circ, lvlL cs = listMax (cs.map lvl)
  | [] => rfl
  | c :: cs => by simp only [lvlL, List.map_cons, listMax, List.foldr_cons]; rw [lvlL_eq cs]; rfl

theorem lvl_fhom : FHom lvlAlg lvl :=
  ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, fun cs => by simp [lvl, lvlAlg, lvlL_eq],
   fun cs => by simp [lvl, lvlAlg, lvlL_eq]⟩

mutual
theorem lvl_le : ∀ c : Circ, lvl c ≤ 2 * depth c + 1
  | .input _ => by simp [lvl]
  | .const _ => by simp [lvl]
  | .not c => by have := lvl_le c; simp [lvl]; omega
  | .and cs => by have := lvlL_le cs; simp only [lvl, depth_and]; omega
  | .or cs => by have := lvlL_le cs; simp only [lvl, depth_or]; omega
theorem lvlL_le : ∀ cs : List Circ, lvlL cs ≤ 2 * listMax (cs.map depth) + 1
  | [] => by simp [lvlL]
  | c :: cs => by
    have h1 := lvl_le c
    have h2 := lvlL_le cs
    simp only [lvlL, List.map_cons, listMax, List.foldr_cons] at h2 ⊢
    omega
end

/-! ## Generic facts on sequential evaluation -/

section RunFacts
variable {α : Type}

theorem run_take (A : Alg α) (C : List DGate) (g : Nat) (hg : g ≤ C.length) :
    (run A [] C).take g = run A [] (C.take g) := by
  have e : C = C.take g ++ C.drop g := (List.take_append_drop g C).symm
  conv => lhs; rw [e]
  rw [run_append]
  obtain ⟨W, hW, _⟩ := run_prefix A (run A [] (C.take g)) (C.drop g)
  rw [hW]
  have hl : (run A [] (C.take g)).length = g := by rw [run_length]; simp; omega
  rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]

theorem run_getD (A : Alg α) (C : List DGate) (g : Nat) (hg : g < C.length) :
    (run A [] C).getD g A.dflt = gstep A ((run A [] C).take g) C[g] := by
  have e : C = C.take (g + 1) ++ C.drop (g + 1) := (List.take_append_drop (g + 1) C).symm
  have et : C.take (g + 1) = C.take g ++ [C[g]] := by
    rw [List.take_add_one, List.getElem?_eq_getElem hg]; rfl
  have hlen : (run A [] (C.take g)).length = g := by rw [run_length]; simp; omega
  have h1 : (run A [] C).getD g A.dflt = (run A [] (C.take (g + 1))).getD g A.dflt := by
    conv => lhs; rw [e]
    rw [run_append]
    obtain ⟨W, hW, _⟩ := run_prefix A (run A [] (C.take (g + 1))) (C.drop (g + 1))
    rw [hW]
    have hl2 : (run A [] (C.take (g + 1))).length = g + 1 := by rw [run_length]; simp; omega
    exact rd_append_left A _ W (by omega)
  rw [h1, et, run_append]
  simp only [run]
  rw [run_take A C g (by omega)]
  have := rd_snoc A (run A [] (C.take g)) (gstep A (run A [] (C.take g)) C[g])
  rw [hlen] at this
  exact this

theorem rd_take (A : Alg α) (l : List α) (g a : Nat) (hg : g ≤ l.length) :
    rd A (l.take g) a = if a < g then rd A l a else A.dflt := by
  unfold rd
  simp only [List.getD_eq_getElem?_getD, List.getElem?_take]
  by_cases h : a < g <;> simp [h]

end RunFacts

/-! ## The layered network for a gate program -/

section Prog
variable (prog : List DGate)

/-- Value of program gate g on input x (false out of range). -/
def vl (x : Nat → Bool) (g : Nat) : Bool := (run (valAlg x) [] prog).getD g false

/-- Level of program gate g. -/
def lv (g : Nat) : Nat := (run lvlAlg [] prog).getD g 0

/-- Layer-1 gate for program gate g (reads only input wires). -/
def gate1 (g : Nat) : DGate → Gate
  | .inp i => orGate (i + 1) (fun j => j == i) false
  | .cst b => constGate b
  | .neg a => if a < g then constGate false else constGate true
  | .disj _ => constGate false
  | .conj as => if as.any (fun a => decide (a < g)) then constGate false
      else if as.isEmpty then constGate false else constGate true

/-- Gate for program gate g at layer t ≥ 2 (reads the S wires of layer t − 1). -/
def gateT (t g : Nat) (d : DGate) : Gate :=
  if lv prog g < t then orGate prog.length (fun j => j == g) false
  else if lv prog g = t then
    match d with
    | .inp _ => constGate false
    | .cst b => constGate b
    | .neg a => if a < g then orGate prog.length (fun j => j == a) true else constGate true
    | .disj as => orGate prog.length (fun j => decide (j ∈ as ∧ j < g)) false
    | .conj _ => orGate prog.length (fun j => j == g) true
  else if lv prog g = t + 1 then
    match d with
    | .conj as => if as.any (fun a => !decide (a < g)) then constGate true
        else orGate prog.length (fun j => decide (j ∈ as)) true
    | _ => constGate false
  else constGate false

def layerAt (t : Nat) : Layer :=
  if t ≤ 1 then (List.range prog.length).map (fun g => gate1 g (prog.getD g (.cst false)))
  else (List.range prog.length).map (fun g => gateT prog t g (prog.getD g (.cst false)))

/-- Wire values after t layers. -/
def ys (x : Nat → Bool) : Nat → (Nat → Bool)
  | 0 => x
  | t + 1 => evalLayer (layerAt prog (t + 1)) (ys x t)

end Prog

section ProgFacts
variable {prog : List DGate}

theorem lvlAlg_pos : ∀ v ∈ run lvlAlg [] prog, 1 ≤ v :=
  run_inv lvlAlg (fun v => 1 ≤ v) (fun _ => True)
    (fun acc g _ _ => by cases g <;> simp [gstep, lvlAlg]) prog [] (fun _ _ => trivial) (by simp)

theorem lv_pos {g : Nat} (hg : g < prog.length) : 1 ≤ lv prog g := by
  unfold lv
  have hl : g < (run lvlAlg [] prog).length := by rw [run_length]; simp; omega
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl]
  exact lvlAlg_pos _ (List.getElem_mem hl)

theorem getD_eq_getElem' (hg : g < prog.length) : prog.getD g (.cst false) = prog[g] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hg]; rfl

/-- Local value equation. -/
theorem vl_eq (x : Nat → Bool) {g : Nat} (hg : g < prog.length) :
    vl prog x g = gstep (valAlg x) ((run (valAlg x) [] prog).take g) prog[g] :=
  run_getD (valAlg x) prog g hg

theorem lv_eq {g : Nat} (hg : g < prog.length) :
    lv prog g = gstep lvlAlg ((run lvlAlg [] prog).take g) prog[g] :=
  run_getD lvlAlg prog g hg

theorem rdv_take (x : Nat → Bool) {g a : Nat} (hg : g < prog.length) :
    rd (valAlg x) ((run (valAlg x) [] prog).take g) a = if a < g then vl prog x a else false := by
  rw [rd_take _ _ _ _ (by rw [run_length]; simp; omega)]; rfl

theorem rdl_take {g a : Nat} (hg : g < prog.length) :
    rd lvlAlg ((run lvlAlg [] prog).take g) a = if a < g then lv prog a else 0 := by
  rw [rd_take _ _ _ _ (by rw [run_length]; simp; omega)]; rfl

theorem evalLayer_at {l : Layer} {z : Nat → Bool} {g : Nat} (f : Nat → Gate) (K : Nat) (hl : l = (List.range K).map f)
    (hg : g < K) : evalLayer l z g = (f g).eval z := by
  subst hl; simp [evalLayer, List.getElem?_range hg]

theorem listMax_ge {l : List Nat} {a : Nat} (h : a ∈ l) : a ≤ listMax l := le_listMax h

theorem vl_inp (x : Nat → Bool) {g i : Nat} (hg : g < prog.length) (hd : prog[g] = .inp i) :
    vl prog x g = x i := by rw [vl_eq x hg, hd]; rfl

theorem vl_cst (x : Nat → Bool) {g : Nat} {b : Bool} (hg : g < prog.length) (hd : prog[g] = .cst b) :
    vl prog x g = b := by rw [vl_eq x hg, hd]; rfl

theorem vl_neg (x : Nat → Bool) {g a : Nat} (hg : g < prog.length) (hd : prog[g] = .neg a) :
    vl prog x g = !(if a < g then vl prog x a else false) := by
  rw [vl_eq x hg, hd]; simp only [gstep]; rw [rdv_take x hg]; rfl

theorem vl_disj (x : Nat → Bool) {g : Nat} {as : List Nat} (hg : g < prog.length) (hd : prog[g] = .disj as) :
    vl prog x g = as.any (fun a => if a < g then vl prog x a else false) := by
  rw [vl_eq x hg, hd]; simp only [gstep]
  rw [List.map_congr_left (fun a _ => rdv_take (a := a) x hg)]
  simp [valAlg, List.any_map, Function.comp_def]

theorem vl_conj (x : Nat → Bool) {g : Nat} {as : List Nat} (hg : g < prog.length) (hd : prog[g] = .conj as) :
    vl prog x g = as.all (fun a => if a < g then vl prog x a else false) := by
  rw [vl_eq x hg, hd]; simp only [gstep]
  rw [List.map_congr_left (fun a _ => rdv_take (a := a) x hg)]
  simp [valAlg, List.all_map, Function.comp_def]

theorem lv_inp {g i : Nat} (hg : g < prog.length) (hd : prog[g] = .inp i) : lv prog g = 1 := by
  rw [lv_eq hg, hd]; rfl

theorem lv_cst {g : Nat} {b : Bool} (hg : g < prog.length) (hd : prog[g] = .cst b) : lv prog g = 1 := by
  rw [lv_eq hg, hd]; rfl

theorem lv_neg {g a : Nat} (hg : g < prog.length) (hd : prog[g] = .neg a) :
    lv prog g = (if a < g then lv prog a else 0) + 1 := by
  rw [lv_eq hg, hd]; simp only [gstep]; rw [rdl_take hg]; rfl

theorem lv_disj {g : Nat} {as : List Nat} (hg : g < prog.length) (hd : prog[g] = .disj as) :
    lv prog g = listMax (as.map (fun a => if a < g then lv prog a else 0)) + 1 := by
  rw [lv_eq hg, hd]; simp only [gstep]
  rw [List.map_congr_left (fun a _ => rdl_take (a := a) hg)]; rfl

theorem lv_conj {g : Nat} {as : List Nat} (hg : g < prog.length) (hd : prog[g] = .conj as) :
    lv prog g = listMax (as.map (fun a => if a < g then lv prog a else 0)) + 2 := by
  rw [lv_eq hg, hd]; simp only [gstep]
  rw [List.map_congr_left (fun a _ => rdl_take (a := a) hg)]; rfl

theorem child_lv {g a : Nat} {as : List Nat} (ha : a ∈ as) (hag : a < g) :
    lv prog a ≤ listMax (as.map (fun a => if a < g then lv prog a else 0)) := by
  apply le_listMax; rw [List.mem_map]; exact ⟨a, ha, by rw [if_pos hag]⟩

theorem decide_or1 {K i : Nat} (hi : i < K) (z : Nat → Bool) (ng : Bool) :
    decide (∃ j < K, (j == i) = true ∧ xor (z j) ng = true) = xor (z i) ng := by
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_iff]
  constructor
  · rintro ⟨j, _, hj, h⟩; simp at hj; subst hj; exact h
  · intro h; exact ⟨i, hi, by simp, h⟩

/-- THE LAYER INVARIANT: after t ≥ 1 layers, wire g carries the value of program gate g
    as soon as t ≥ lvl(g); an AND gate carries its complement one layer earlier. -/
theorem ys_spec (x : Nat → Bool) : ∀ t, 1 ≤ t → ∀ g (hg : g < prog.length),
    (lv prog g ≤ t → ys prog x t g = vl prog x g) ∧
    (∀ as, prog[g] = .conj as → lv prog g = t + 1 → ys prog x t g = !vl prog x g)
  | 0, h, _, _ => absurd h (by omega)
  | 1, _, g, hg => by
    have hy : ys prog x 1 g = (gate1 g prog[g]).eval x := by
      simp only [ys]
      rw [evalLayer_at (fun g => gate1 g (prog.getD g (.cst false))) prog.length
        (by simp [layerAt]) hg, getD_eq_getElem' hg]
    rw [hy]
    cases hd : prog[g] with
    | inp i =>
      refine ⟨fun _ => ?_, fun as h => by cases h⟩
      rw [vl_inp x hg hd]; simp only [gate1, orGate_eval]
      rw [decide_or1 (by omega : i < i + 1)]; simp
    | cst b =>
      refine ⟨fun _ => ?_, fun as h => by cases h⟩
      rw [vl_cst x hg hd]; simp [gate1, constGate_eval]
    | neg a =>
      refine ⟨fun hle => ?_, fun as h => by cases h⟩
      have hl := lv_neg hg hd
      by_cases ha : a < g
      · exfalso; rw [if_pos ha] at hl
        have := lv_pos (prog := prog) (show a < prog.length by omega); omega
      · rw [vl_neg x hg hd]; simp [gate1, ha, constGate_eval]
    | disj as =>
      refine ⟨fun hle => ?_, fun as' h => by cases h⟩
      have hl := lv_disj hg hd
      rw [vl_disj x hg hd]
      simp only [gate1, constGate_eval]
      symm
      apply List.any_eq_false.mpr
      intro a ha
      by_cases hag : a < g
      · exfalso
        have h1 := child_lv (prog := prog) ha hag
        have := lv_pos (prog := prog) (show a < prog.length by omega); omega
      · simp [hag]
    | conj as =>
      have hl := lv_conj hg hd
      refine ⟨fun hle => by omega, fun as' h hlv => ?_⟩
      cases h
      have hnone : ∀ a ∈ as, ¬ a < g := by
        intro a ha hag
        have h1 := child_lv (prog := prog) ha hag
        have := lv_pos (prog := prog) (show a < prog.length by omega); omega
      have hany : as.any (fun a => decide (a < g)) = false := by
        apply List.any_eq_false.mpr; intro a ha; simpa using hnone a ha
      rw [vl_conj x hg hd]
      simp only [gate1, hany, Bool.false_eq_true, if_false]
      cases as with
      | nil => simp [constGate_eval]
      | cons a as =>
        simp only [List.isEmpty_cons, Bool.false_eq_true, if_false, constGate_eval]
        have : (a :: as).all (fun a => if a < g then vl prog x a else false) = false := by
          apply List.all_eq_false.mpr
          exact ⟨a, by simp, by simp [hnone a (by simp)]⟩
        rw [this]; rfl
  | t + 2, _, g, hg => by
    have IH := fun g hg => ys_spec x (t + 1) (by omega) g hg
    have hy : ys prog x (t + 2) g = (gateT prog (t + 2) g prog[g]).eval (ys prog x (t + 1)) := by
      simp only [ys]
      rw [evalLayer_at (fun g => gateT prog (t + 2) g (prog.getD g (.cst false))) prog.length
        (by simp [layerAt]) hg, getD_eq_getElem' hg]
    rw [hy]
    constructor
    · intro hle
      by_cases hlt : lv prog g < t + 2
      · -- buffer
        unfold gateT; rw [if_pos hlt, orGate_eval, decide_or1 hg, (IH g hg).1 (by omega)]; simp
      · have heq : lv prog g = t + 2 := by omega
        unfold gateT; rw [if_neg hlt, if_pos heq]
        cases hd : prog[g] with
        | inp i => exfalso; have := lv_inp hg hd; omega
        | cst b => exfalso; have := lv_cst hg hd; omega
        | neg a =>
          have hl := lv_neg hg hd
          by_cases ha : a < g
          · rw [if_pos ha] at hl
            simp only [ha, if_true, orGate_eval]
            rw [vl_neg x hg hd, if_pos ha, decide_or1 (show a < prog.length by omega),
              (IH a (by omega)).1 (by omega)]
            cases vl prog x a <;> rfl
          · exfalso; rw [if_neg ha] at hl; omega
        | disj as =>
          have hl := lv_disj hg hd
          simp only [orGate_eval]
          rw [vl_disj x hg hd]
          have hch : ∀ a ∈ as, a < g → lv prog a ≤ t + 1 := by
            intro a ha hag; have := child_lv (prog := prog) ha hag; omega
          apply Bool.eq_iff_iff.mpr
          simp only [decide_eq_true_iff, List.any_eq_true]
          constructor
          · rintro ⟨j, hj, hsel, h⟩
            try simp only [decide_eq_true_iff] at hsel
            refine ⟨j, hsel.1, ?_⟩
            rw [if_pos hsel.2, ← (IH j hj).1 (hch j hsel.1 hsel.2)]; simpa using h
          · rintro ⟨a, ha, h⟩
            by_cases hag : a < g
            · rw [if_pos hag] at h
              refine ⟨a, by omega, by simp [ha, hag], ?_⟩
              rw [(IH a (by omega)).1 (hch a ha hag)]; simpa using h
            · rw [if_neg hag] at h; cases h
        | conj as =>
          simp only [orGate_eval]
          rw [decide_or1 hg, (IH g hg).2 as hd (by omega)]
          cases vl prog x g <;> rfl
    · intro as hd hlv
      have hl := lv_conj hg hd
      unfold gateT
      rw [if_neg (show ¬ lv prog g < t + 2 by omega), if_neg (show ¬ lv prog g = t + 2 by omega),
        if_pos hlv, hd]
      simp only
      rw [vl_conj x hg hd]
      by_cases hout : as.any (fun a => !decide (a < g)) = true
      · simp only [hout, if_true, constGate_eval]
        obtain ⟨a, ha, hna⟩ := List.any_eq_true.mp hout
        simp only [Bool.not_eq_true', decide_eq_false_iff_not] at hna
        have : as.all (fun a => if a < g then vl prog x a else false) = false := by
          apply List.all_eq_false.mpr
          exact ⟨a, ha, by simp [hna]⟩
        rw [this]; rfl
      · simp only [Bool.not_eq_true] at hout
        simp only [hout, Bool.false_eq_true, if_false, orGate_eval]
        have hin : ∀ a ∈ as, a < g := by
          intro a ha
          have := List.any_eq_false.mp hout a ha
          simpa using this
        have hch : ∀ a ∈ as, lv prog a ≤ t + 1 := by
          intro a ha; have := child_lv (prog := prog) ha (hin a ha); omega
        apply Bool.eq_iff_iff.mpr
        simp only [decide_eq_true_iff, Bool.not_eq_true', List.all_eq_false]
        constructor
        · rintro ⟨j, hj, hsel, h⟩
          try simp only [decide_eq_true_iff] at hsel
          refine ⟨j, hsel, ?_⟩
          rw [if_pos (hin j hsel), ← (IH j hj).1 (hch j hsel)]; simpa using h
        · rintro ⟨a, ha, h⟩
          rw [if_pos (hin a ha)] at h
          refine ⟨a, by have := hin a ha; omega, by simp [ha], ?_⟩
          rw [(IH a (by have := hin a ha; omega)).1 (hch a ha)]; simpa using h

end ProgFacts

/-! ## Compiling a list of formulas -/

/-- The shared program and output gates of a formula list. -/
def progOf (cs : List Circ) : List DGate := (emitL 0 cs).1
def outsOf (cs : List Circ) : List Nat := (emitL 0 cs).2

/-- Depth bound used for the layer count. -/
def dmax (cs : List Circ) : Nat := listMax (cs.map depth)

/-- Number of computing layers: 2·D + 1. -/
def nLayers (cs : List Circ) : Nat := 2 * dmax cs + 1

/-- THE COMPILED NETWORK for formulas cs on n input wires: 2·D + 1 computing layers of
    width S, then one output layer of width K = cs.length. -/
def compileF (cs : List Circ) : List Layer :=
  (List.range (nLayers cs)).map (fun t => layerAt (progOf cs) (t + 1)) ++
    [(outsOf cs).map (fun o => orGate (progOf cs).length (fun j => j == o) false)]

theorem evalNet_append (ls : List Layer) (l : Layer) (z : Nat → Bool) :
    evalNet (ls ++ [l]) z = evalLayer l (evalNet ls z) := by
  induction ls generalizing z with
  | nil => rfl
  | cons l' ls ih => simp only [List.cons_append, evalNet]; exact ih _

theorem evalNet_layers (prog : List DGate) (x : Nat → Bool) : ∀ L,
    evalNet ((List.range L).map (fun t => layerAt prog (t + 1))) x = ys prog x L
  | 0 => rfl
  | L + 1 => by rw [List.range_succ, List.map_append, List.map_cons, List.map_nil, evalNet_append,
      evalNet_layers prog x L]; rfl

theorem outs_range : ∀ (cs : List Circ) (base : Nat),
    ∀ a ∈ (emitL base cs).2, base ≤ a ∧ a < base + (emitL base cs).1.length
  | [], _ => by simp [emitL]
  | c :: cs, base => by
    intro a ha
    have hpos := size_pos' c
    have hlc := emit_len base c
    simp only [emitL, List.mem_cons] at ha
    have hlen : (emitL base (c :: cs)).1.length =
        (emit base c).length + (emitL (base + (emit base c).length) cs).1.length := by simp [emitL]
    rw [hlen]
    rcases ha with rfl | ha
    · omega
    · have := outs_range cs (base + (emit base c).length) a ha; omega

theorem outs_length (cs : List Circ) : (outsOf cs).length = cs.length := (emitL_len 0 cs).2

theorem prog_length (cs : List Circ) : (progOf cs).length = (cs.map size).sum := (emitL_len 0 cs).1

theorem valAlg_fhom (x : Nat → Bool) : FHom (valAlg x) (eval x) :=
  ⟨fun _ => by simp [valAlg], fun _ => by simp [valAlg], fun _ => by simp [valAlg],
   fun _ => by simp [valAlg, List.all_map], fun _ => by simp [valAlg, List.any_map]⟩

theorem outs_val (cs : List Circ) (x : Nat → Bool) {k : Nat} (hk : k < cs.length) :
    vl (progOf cs) x ((outsOf cs)[k]'(by rw [outs_length]; exact hk)) = eval x cs[k] := by
  have h := emitL_val (valAlg x) (eval x) (valAlg_fhom x) 0 cs [] rfl
  have h2 := congrArg (fun l => l[k]?) h
  simp only [List.getElem?_map] at h2
  rw [List.getElem?_eq_getElem (by rw [(emitL_len 0 cs).2]; exact hk), List.getElem?_eq_getElem hk] at h2
  simp only [Option.map_some, Option.some.injEq] at h2
  exact h2

theorem outs_lv (cs : List Circ) {k : Nat} (hk : k < cs.length) :
    lv (progOf cs) ((outsOf cs)[k]'(by rw [outs_length]; exact hk)) ≤ nLayers cs := by
  have h := emitL_val lvlAlg lvl lvl_fhom 0 cs [] rfl
  have h2 := congrArg (fun l => l[k]?) h
  simp only [List.getElem?_map] at h2
  rw [List.getElem?_eq_getElem (by rw [(emitL_len 0 cs).2]; exact hk), List.getElem?_eq_getElem hk] at h2
  simp only [Option.map_some, Option.some.injEq] at h2
  unfold lv
  have e : (run lvlAlg [] (progOf cs)).getD ((outsOf cs)[k]'(by rw [outs_length]; exact hk)) 0 =
      lvl cs[k] := h2
  rw [e]
  have h3 := lvl_le cs[k]
  have h4 : depth cs[k] ≤ dmax cs := le_listMax (List.mem_map_of_mem (List.getElem_mem hk))
  unfold nLayers; omega

/-- OUTPUT CORRECTNESS: output k of the compiled network is formula k, on every input. -/
theorem compileF_eval (cs : List Circ) (x : Nat → Bool) {k : Nat} (hk : k < cs.length) :
    evalNet (compileF cs) x k = eval x cs[k] := by
  unfold compileF
  rw [evalNet_append, evalNet_layers]
  have hk' : k < (outsOf cs).length := by rw [outs_length]; exact hk
  rw [evalLayer_at (fun k => orGate (progOf cs).length (fun j => j == (outsOf cs).getD k 0) false)
    (outsOf cs).length (by
      apply List.ext_getElem (by simp)
      intro n h1 h2; simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using h1)]) hk']
  simp only [orGate_eval]
  have ho : (outsOf cs).getD k 0 = (outsOf cs)[k] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk']; rfl
  have hor := outs_range cs 0 (outsOf cs)[k] (List.getElem_mem hk')
  have hS : (outsOf cs)[k] < (progOf cs).length := by simpa [progOf] using hor.2
  have hspec := (ys_spec (prog := progOf cs) x (nLayers cs) (by unfold nLayers; omega) _ hS).1 (outs_lv cs hk)
  rw [ho]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_iff]
  constructor
  · rintro ⟨j, _, hj, h⟩; simp at hj; subst hj; rw [hspec, outs_val cs x hk] at h; simpa using h
  · intro h; exact ⟨_, hS, by simp, by rw [hspec, outs_val cs x hk]; simpa using h⟩

/-- Outputs beyond K are false. -/
theorem compileF_eval_out (cs : List Circ) (x : Nat → Bool) {k : Nat} (hk : cs.length ≤ k) :
    evalNet (compileF cs) x k = false := by
  unfold compileF
  rw [evalNet_append]
  simp [evalLayer, List.getElem?_eq_none (show (outsOf cs).length ≤ k by rw [outs_length]; exact hk)]

/-! ## Resources of the compiled network -/

theorem compileF_valid (cs : List Circ) : NetValid 1 (compileF cs) := by
  intro l hl g hg
  simp only [compileF, List.mem_append, List.mem_map, List.mem_range, List.mem_singleton] at hl
  rcases hl with ⟨t, _, rfl⟩ | rfl
  · simp only [layerAt] at hg
    split at hg
    · simp only [List.mem_map, List.mem_range] at hg
      obtain ⟨g', _, rfl⟩ := hg
      generalize (progOf cs).getD g' (.cst false) = d
      cases d <;> simp only [gate1] <;> (try split) <;> (try split) <;>
        first | exact orGate_valid _ _ _ | exact constGate_valid _
    · simp only [List.mem_map, List.mem_range] at hg
      obtain ⟨g', _, rfl⟩ := hg
      generalize (progOf cs).getD g' (.cst false) = d
      unfold gateT
      split
      · exact orGate_valid _ _ _
      · split
        · cases d <;> simp only <;> (try split) <;> first | exact orGate_valid _ _ _ | exact constGate_valid _
        · split
          · cases d <;> simp only <;> (try split) <;> first | exact orGate_valid _ _ _ | exact constGate_valid _
          · exact constGate_valid _
  · simp only [List.mem_map] at hg
    obtain ⟨o, _, rfl⟩ := hg
    exact orGate_valid _ _ _

/-- WIRED: if every formula reads only inputs below n, every first-layer gate has
    fan-in ≤ n. -/
theorem compileF_wired (cs : List Circ) (n : Nat) (hn : ∀ c ∈ cs, maxInput c ≤ n) :
    Wired n (compileF cs) := by
  have hlay : nLayers cs = (nLayers cs - 1) + 1 := by unfold nLayers; omega
  unfold compileF
  rw [hlay, List.range_succ_eq_map, List.map_cons, List.cons_append]
  intro g hg
  simp only [show (0 : Nat) + 1 ≤ 1 by omega, layerAt, if_true, List.mem_map, List.mem_range] at hg
  obtain ⟨g', hg', rfl⟩ := hg
  have hmem : (progOf cs).getD g' (.cst false) ∈ progOf cs := by
    rw [getD_eq_getElem' hg']; exact List.getElem_mem hg'
  have hr := emitL_reads 0 cs _ hmem
  have hmx : listMax (cs.map maxInput) ≤ n := listMax_le (fun a ha => by
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ha; exact hn c hc)
  generalize (progOf cs).getD g' (.cst false) = d at hr
  cases d with
  | inp i => simp only [gate1, orGate_fanin]; simp [gmax] at hr; omega
  | cst b => simp [gate1, constGate_fanin]
  | neg a => simp only [gate1]; split <;> simp [constGate_fanin]
  | disj as => simp [gate1, constGate_fanin]
  | conj as => simp only [gate1]; split <;> (try split) <;> simp [constGate_fanin]

theorem compileF_length (cs : List Circ) : (compileF cs).length = 2 * dmax cs + 2 := by
  simp [compileF, nLayers]

theorem cs_le_prog (cs : List Circ) : cs.length ≤ (progOf cs).length := by
  rw [prog_length]
  have h : ∀ c ∈ cs, 1 ≤ size c := fun c _ => size_pos' c
  induction cs with
  | nil => simp
  | cons c cs ih =>
    simp only [List.length_cons, List.map_cons, List.sum_cons]
    have := ih (fun c' hc' => h c' (by simp [hc']))
    have := h c (by simp); omega

/-- BOUNDED WIDTH AND FAN-IN: every layer has ≤ S + n gates, every gate fan-in ≤ S + n,
    where S = Σ size(c_k) is the program size. -/
theorem compileF_bounded (cs : List Circ) (n : Nat) (hn : ∀ c ∈ cs, maxInput c ≤ n) :
    NetBounded ((cs.map size).sum + n) (compileF cs) := by
  have hmx : listMax (cs.map maxInput) ≤ n := listMax_le (fun a ha => by
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ha; exact hn c hc)
  have hS := prog_length cs
  intro l hl
  simp only [compileF, List.mem_append, List.mem_map, List.mem_range, List.mem_singleton] at hl
  rcases hl with ⟨t, _, rfl⟩ | rfl
  · refine ⟨by simp only [layerAt]; split <;> simp [hS], ?_⟩
    intro g hg
    simp only [layerAt] at hg
    split at hg
    · simp only [List.mem_map, List.mem_range] at hg
      obtain ⟨g', hg', rfl⟩ := hg
      have hmem : (progOf cs).getD g' (.cst false) ∈ progOf cs := by
        rw [getD_eq_getElem' hg']; exact List.getElem_mem hg'
      have hr := emitL_reads 0 cs _ hmem
      generalize (progOf cs).getD g' (.cst false) = d at hr
      cases d with
      | inp i => simp only [gate1, orGate_fanin]; simp [gmax] at hr; omega
      | cst b => simp [gate1, constGate_fanin]
      | neg a => simp only [gate1]; split <;> simp [constGate_fanin]
      | disj as => simp [gate1, constGate_fanin]
      | conj as => simp only [gate1]; split <;> (try split) <;> simp [constGate_fanin]
    · simp only [List.mem_map, List.mem_range] at hg
      obtain ⟨g', _, rfl⟩ := hg
      generalize (progOf cs).getD g' (.cst false) = d
      unfold gateT
      split
      · rw [orGate_fanin]; omega
      · split
        · cases d <;> simp only <;> (try split) <;>
            first | (rw [orGate_fanin]; omega) | (rw [constGate_fanin]; omega)
        · split
          · cases d <;> simp only <;> (try split) <;>
              first | (rw [orGate_fanin]; omega) | (rw [constGate_fanin]; omega)
          · rw [constGate_fanin]; omega
  · refine ⟨by simp [outs_length]; have := cs_le_prog cs; omega, ?_⟩
    intro g hg
    simp only [List.mem_map] at hg
    obtain ⟨o, _, rfl⟩ := hg
    rw [orGate_fanin]; omega

/-- Total number of gates: (2D + 1)·S computing gates and K output buffers. -/
def gateCount (ls : List Layer) : Nat := (ls.map List.length).sum

theorem compileF_gates (cs : List Circ) :
    gateCount (compileF cs) = (2 * dmax cs + 1) * (cs.map size).sum + cs.length := by
  unfold gateCount compileF
  simp only [List.map_append, List.map_map, List.sum_append_nat, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, List.length_map, outs_length, Nat.add_zero]
  have e : ∀ t ∈ List.range (nLayers cs), (List.length ∘ fun t => layerAt (progOf cs) (t + 1)) t =
      (cs.map size).sum := by
    intro t _; simp only [Function.comp_apply, layerAt]; split <;> simp [prog_length]
  rw [List.map_congr_left e, List.map_const', List.sum_replicate_nat, List.length_range]
  unfold nLayers; rfl

/-- THE COMPILER THEOREM (all properties of the one network `compileF cs`). -/
theorem compileF_spec (cs : List Circ) (n D : Nat) (hn : ∀ c ∈ cs, maxInput c ≤ n)
    (hD : ∀ c ∈ cs, depth c ≤ D) :
    (∀ x : Nat → Bool, ∀ k (hk : k < cs.length), evalNet (compileF cs) x k = eval x cs[k]) ∧
    (∀ x : Nat → Bool, ∀ k, cs.length ≤ k → evalNet (compileF cs) x k = false) ∧
    NetValid 1 (compileF cs) ∧ Wired n (compileF cs) ∧
    (compileF cs).length ≤ 2 * D + 2 ∧
    NetBounded ((cs.map size).sum + n) (compileF cs) ∧
    gateCount (compileF cs) ≤ (2 * D + 1) * (cs.map size).sum + cs.length := by
  have hd : dmax cs ≤ D := listMax_le (fun a ha => by obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ha; exact hD c hc)
  refine ⟨fun x k hk => compileF_eval cs x hk, fun x k hk => compileF_eval_out cs x hk, compileF_valid cs,
    compileF_wired cs n hn, by rw [compileF_length]; omega, compileF_bounded cs n hn, ?_⟩
  rw [compileF_gates]
  have : (2 * dmax cs + 1) * (cs.map size).sum ≤ (2 * D + 1) * (cs.map size).sum :=
    Nat.mul_le_mul_right _ (by omega)
  omega

/-- FIXED GRID: every gate of a compiled network fires in the paper's rational form with
    denominator D = 1 exactly when it fires in integer form (weights in {0,1}, threshold
    in {0,1}). -/
theorem compileF_fixed_grid (cs : List Circ) :
    ∀ l ∈ compileF cs, ∀ g ∈ l, Gate.Valid 1 g ∧ ∀ z, (ratFires g 1 z ↔ g.eval z = true) :=
  fun l hl g hg => ⟨compileF_valid cs l hl g hg, fun z => gate_rat_iff g (by decide) z⟩


/-! ## Axiom audit -/

#print axioms sum_range_pos
#print axioms orGate_eval
#print axioms constGate_eval
#print axioms orGate_valid
#print axioms constGate_valid
#print axioms orGate_fanin
#print axioms constGate_fanin
#print axioms lvlL_eq
#print axioms lvl_fhom
#print axioms lvl_le
#print axioms lvlL_le
#print axioms run_take
#print axioms run_getD
#print axioms rd_take
#print axioms lvlAlg_pos
#print axioms lv_pos
#print axioms getD_eq_getElem'
#print axioms vl_eq
#print axioms lv_eq
#print axioms rdv_take
#print axioms rdl_take
#print axioms evalLayer_at
#print axioms listMax_ge
#print axioms vl_inp
#print axioms vl_cst
#print axioms vl_neg
#print axioms vl_disj
#print axioms vl_conj
#print axioms lv_inp
#print axioms lv_cst
#print axioms lv_neg
#print axioms lv_disj
#print axioms lv_conj
#print axioms child_lv
#print axioms decide_or1
#print axioms ys_spec
#print axioms evalNet_append
#print axioms evalNet_layers
#print axioms outs_range
#print axioms outs_length
#print axioms prog_length
#print axioms valAlg_fhom
#print axioms outs_val
#print axioms outs_lv
#print axioms compileF_eval
#print axioms compileF_eval_out
#print axioms compileF_valid
#print axioms compileF_wired
#print axioms compileF_length
#print axioms cs_le_prog
#print axioms compileF_bounded
#print axioms compileF_gates
#print axioms compileF_spec
#print axioms compileF_fixed_grid
end ThresholdNet
end NimAudit
