import BinaryReadout

/- Phase 4, Priority 2b: formula versus shared-circuit (DAG) conventions.
   Written by Claude (10 October 2026).  Lean 4.26.0, core/Std only.

   All earlier circuit statements use FORMULAS (`AC0.Circ`, trees without sharing).
   The classical parity theorem is normally stated for CIRCUITS with sharing.  This
   file defines bounded-depth straight-line circuits (DAGs) and proves both
   translations, so that the two conventions are related precisely:

     * EMBEDDING   formula C  ↦  DAG `toDag C` with the same function, the same depth
                   (NOT counted), exactly `size C` gates, reading the same inputs;
     * UNFOLDING   DAG D with fan-in ≤ F (F ≥ 1)  ↦  formula `D.formula` with the same
                   function, the same depth, size ≤ (F+1)^depth, reading the same inputs.

   Consequences: the DAG form of the parity-correlation premise implies the formula
   form at the SAME depth and size (`formula_premise_of_dag`), so every conditional
   readout theorem may assume the classical theorem in the shared-circuit convention
   (`network_readout_bound_dag`); conversely the formula premise at size (F+1)^d
   implies the DAG premise for fan-in-F circuits of depth d (`dag_premise_of_formula`),
   which is polynomial for constant d.

   DAG semantics: a program is a list of gates in topological order; gate k reads the
   values of gates with smaller index; a reference to any other index reads a fixed
   default (false), so every list of gates is a well-defined circuit. -/

namespace NimAudit
namespace Shared

open AC0 AC0.Circ Prob Bridge CorrBridge

inductive DGate where
  | inp (i : Nat)
  | cst (b : Bool)
  | neg (a : Nat)
  | conj (as : List Nat)
  | disj (as : List Nat)

/-- An interpretation of the gate types over a carrier (values, depths, formulas, …). -/
structure Alg (α : Type) where
  dflt : α
  inp : Nat → α
  cst : Bool → α
  neg : α → α
  conj : List α → α
  disj : List α → α

def rd {α : Type} (A : Alg α) (acc : List α) (a : Nat) : α := acc.getD a A.dflt

def gstep {α : Type} (A : Alg α) (acc : List α) : DGate → α
  | .inp i => A.inp i
  | .cst b => A.cst b
  | .neg a => A.neg (rd A acc a)
  | .conj as => A.conj (as.map (rd A acc))
  | .disj as => A.disj (as.map (rd A acc))

/-- Sequential evaluation: append the value of each gate in turn. -/
def run {α : Type} (A : Alg α) (acc : List α) : List DGate → List α
  | [] => acc
  | g :: C => run A (acc ++ [gstep A acc g]) C

section Generic
variable {α β : Type}

theorem run_append (A : Alg α) : ∀ (acc : List α) (C D : List DGate),
    run A acc (C ++ D) = run A (run A acc C) D
  | _, [], _ => rfl
  | acc, g :: C, D => run_append A (acc ++ [gstep A acc g]) C D

theorem run_prefix (A : Alg α) : ∀ (acc : List α) (C : List DGate),
    ∃ W, run A acc C = acc ++ W ∧ W.length = C.length
  | acc, [] => ⟨[], by simp [run]⟩
  | acc, g :: C => by
    obtain ⟨W, h1, h2⟩ := run_prefix A (acc ++ [gstep A acc g]) C
    exact ⟨gstep A acc g :: W, by simp [run, h1], by simp [h2]⟩

theorem run_length (A : Alg α) (acc : List α) (C : List DGate) :
    (run A acc C).length = acc.length + C.length := by
  obtain ⟨W, h1, h2⟩ := run_prefix A acc C
  rw [h1, List.length_append, h2]

theorem rd_append_left (A : Alg α) (l W : List α) {a : Nat} (h : a < l.length) :
    rd A (l ++ W) a = rd A l a := by
  simp [rd, List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem rd_snoc (A : Alg α) (l : List α) (v : α) : rd A (l ++ [v]) l.length = v := by
  simp [rd, List.getD_eq_getElem?_getD]

theorem rd_map (A : Alg α) (B : Alg β) (h : α → β) (hd : h A.dflt = B.dflt) (l : List α) (a : Nat) :
    h (rd A l a) = rd B (l.map h) a := by
  simp only [rd, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[a]? <;> simp [hd]

theorem rd_inv (A : Alg α) (P : α → Prop) (l : List α) (a : Nat) (hl : ∀ v ∈ l, P v) (hd : P A.dflt) :
    P (rd A l a) := by
  simp only [rd, List.getD_eq_getElem?_getD]
  cases h : l[a]? with
  | none => simpa using hd
  | some v => simpa using hl v (List.mem_of_getElem? h)

/-- An invariant preserved by every gate step is preserved by evaluation. -/
theorem run_inv (A : Alg α) (P : α → Prop) (Q : DGate → Prop)
    (hstep : ∀ acc g, Q g → (∀ v ∈ acc, P v) → P (gstep A acc g)) :
    ∀ (C : List DGate) (acc : List α), (∀ g ∈ C, Q g) → (∀ v ∈ acc, P v) → ∀ v ∈ run A acc C, P v
  | [], _, _, hacc => hacc
  | g :: C, acc, hC, hacc => by
    apply run_inv A P Q hstep C _ (fun g' hg' => hC g' (by simp [hg']))
    intro v hv
    simp only [List.mem_append, List.mem_singleton] at hv
    rcases hv with hv | rfl
    · exact hacc v hv
    · exact hstep acc g (hC g (by simp)) hacc

/-- Homomorphism of interpretations. -/
structure Hom (A : Alg α) (B : Alg β) (h : α → β) : Prop where
  dflt : h A.dflt = B.dflt
  inp : ∀ i, h (A.inp i) = B.inp i
  cst : ∀ b, h (A.cst b) = B.cst b
  neg : ∀ a, h (A.neg a) = B.neg (h a)
  conj : ∀ l, h (A.conj l) = B.conj (l.map h)
  disj : ∀ l, h (A.disj l) = B.disj (l.map h)

theorem gstep_hom {A : Alg α} {B : Alg β} {h : α → β} (hh : Hom A B h) (acc : List α) (g : DGate) :
    h (gstep A acc g) = gstep B (acc.map h) g := by
  cases g with
  | inp i => exact hh.inp i
  | cst b => exact hh.cst b
  | neg a => simp only [gstep]; rw [hh.neg, rd_map A B h hh.dflt]
  | conj as =>
    simp only [gstep]; rw [hh.conj, List.map_map]
    congr 1; apply List.map_congr_left; intro a _; exact rd_map A B h hh.dflt acc a
  | disj as =>
    simp only [gstep]; rw [hh.disj, List.map_map]
    congr 1; apply List.map_congr_left; intro a _; exact rd_map A B h hh.dflt acc a

theorem run_hom {A : Alg α} {B : Alg β} {h : α → β} (hh : Hom A B h) :
    ∀ (acc : List α) (C : List DGate), (run A acc C).map h = run B (acc.map h) C
  | _, [] => rfl
  | acc, g :: C => by
    simp only [run]
    rw [run_hom hh _ C, List.map_append, List.map_cons, List.map_nil, gstep_hom hh]

end Generic

/-! ## Interpretations -/

def valAlg (x : Nat → Bool) : Alg Bool := ⟨false, x, id, (!·), fun l => l.all id, fun l => l.any id⟩
def depAlg : Alg Nat := ⟨0, fun _ => 0, fun _ => 0, (· + 1), fun l => listMax l + 1, fun l => listMax l + 1⟩
def maxAlg : Alg Nat := ⟨0, (· + 1), fun _ => 0, id, listMax, listMax⟩
def frmAlg : Alg Circ := ⟨const false, input, const, not, and, or⟩

theorem eval_hom (x : Nat → Bool) : Hom frmAlg (valAlg x) (eval x) :=
  ⟨by simp [frmAlg, valAlg], fun _ => by simp [frmAlg, valAlg], fun _ => by simp [frmAlg, valAlg],
   fun _ => by simp [frmAlg, valAlg], fun _ => by simp [frmAlg, valAlg, List.all_map],
   fun _ => by simp [frmAlg, valAlg, List.any_map]⟩

theorem depth_hom : Hom frmAlg depAlg depth :=
  ⟨by simp [frmAlg, depAlg], fun _ => by simp [frmAlg, depAlg], fun _ => by simp [frmAlg, depAlg],
   fun _ => by simp [frmAlg, depAlg], fun _ => by simp [frmAlg, depAlg],
   fun _ => by simp [frmAlg, depAlg]⟩

theorem maxIn_hom : Hom frmAlg maxAlg maxInput :=
  ⟨by simp [frmAlg, maxAlg], fun _ => by simp [frmAlg, maxAlg], fun _ => by simp [frmAlg, maxAlg],
   fun _ => by simp [frmAlg, maxAlg], fun _ => by simp [frmAlg, maxAlg],
   fun _ => by simp [frmAlg, maxAlg]⟩

/-! ## Shared circuits -/

/-- A bounded-depth shared circuit: a gate program and an output gate. -/
structure Dag where
  prog : List DGate
  out : Nat

def gmax : DGate → Nat
  | .inp i => i + 1
  | _ => 0

def gfan : DGate → Nat
  | .neg _ => 1
  | .conj as => as.length
  | .disj as => as.length
  | _ => 0

namespace Dag

def val {α : Type} (A : Alg α) (D : Dag) : α := rd A (run A [] D.prog) D.out
def eval (x : Nat → Bool) (D : Dag) : Bool := D.val (valAlg x)
/-- Depth of the output gate (NOT counted, as for formulas). -/
def depth (D : Dag) : Nat := D.val depAlg
/-- Number of gates (input and constant nodes included, as for formula size). -/
def size (D : Dag) : Nat := D.prog.length
/-- The unfolded formula. -/
def formula (D : Dag) : Circ := D.val frmAlg
def Reads (m : Nat) (D : Dag) : Prop := ∀ g ∈ D.prog, gmax g ≤ m
def Fanin (F : Nat) (D : Dag) : Prop := ∀ g ∈ D.prog, gfan g ≤ F

end Dag

theorem val_hom {α β : Type} {A : Alg α} {B : Alg β} {h : α → β} (hh : Hom A B h) (D : Dag) :
    h (D.val A) = D.val B := by
  simp only [Dag.val]
  rw [rd_map A B h hh.dflt, run_hom hh]
  rfl

/-! ## Unfolding a DAG into a formula -/

theorem formula_eval (x : Nat → Bool) (D : Dag) : eval x D.formula = D.eval x := val_hom (eval_hom x) D

theorem formula_depth (D : Dag) : depth D.formula = D.depth := val_hom depth_hom D

theorem formula_maxInput {m : Nat} (D : Dag) (h : D.Reads m) : maxInput D.formula ≤ m := by
  rw [show maxInput D.formula = D.val maxAlg from val_hom maxIn_hom D]
  apply rd_inv maxAlg (· ≤ m) _ _ _ (Nat.zero_le m)
  apply run_inv maxAlg (· ≤ m) (fun g => gmax g ≤ m) _ D.prog [] h (by simp)
  intro acc g hg hacc
  cases g with
  | inp i => exact hg
  | cst b => exact Nat.zero_le m
  | neg a => exact rd_inv maxAlg (· ≤ m) acc a hacc (Nat.zero_le m)
  | conj as =>
    apply listMax_le; intro v hv
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp hv
    exact rd_inv maxAlg (· ≤ m) acc a hacc (Nat.zero_le m)
  | disj as =>
    apply listMax_le; intro v hv
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp hv
    exact rd_inv maxAlg (· ≤ m) acc a hacc (Nat.zero_le m)

theorem size_list_pow {F M : Nat} (cs : List Circ) (hlen : cs.length ≤ F)
    (h : ∀ c ∈ cs, size c ≤ (F + 1) ^ depth c) (hM : ∀ c ∈ cs, depth c ≤ M) :
    (cs.map size).sum + 1 ≤ (F + 1) ^ (M + 1) := by
  have h1 : ∀ c ∈ cs, size c ≤ (F + 1) ^ M := fun c hc =>
    Nat.le_trans (h c hc) (Nat.pow_le_pow_right (by omega) (hM c hc))
  have h2 := sum_le_len_mul h1
  have h3 : cs.length * (F + 1) ^ M ≤ F * (F + 1) ^ M := Nat.mul_le_mul_right _ hlen
  have h4 : 0 < (F + 1) ^ M := Nat.pow_pos (by omega)
  have h5 : (F + 1) ^ (M + 1) = F * (F + 1) ^ M + (F + 1) ^ M := by
    rw [Nat.pow_succ, Nat.mul_comm, Nat.succ_mul]
  omega

/-- UNFOLDING: a shared circuit of depth D and fan-in ≤ F (F ≥ 1) unfolds into a
    formula computing the same function, of the same depth and size ≤ (F+1)^D. -/
theorem formula_size {F : Nat} (hF1 : 1 ≤ F) (D : Dag) (hF : D.Fanin F) :
    size D.formula ≤ (F + 1) ^ D.depth := by
  rw [← formula_depth]
  let P : Circ → Prop := fun c => size c ≤ (F + 1) ^ depth c
  have hd : P (const false) := by simp [P]
  show P (D.val frmAlg)
  apply rd_inv frmAlg P _ _ _ hd
  apply run_inv frmAlg P (fun g => gfan g ≤ F) _ D.prog [] hF (by simp)
  intro acc g hg hacc
  have hrd : ∀ a, P (rd frmAlg acc a) := fun a => rd_inv frmAlg P acc a hacc hd
  cases g with
  | inp i => show size (input i) ≤ (F + 1) ^ depth (input i); simp
  | cst b => show size (const b) ≤ (F + 1) ^ depth (const b); simp
  | neg a =>
    have h := hrd a
    show size (not (rd frmAlg acc a)) ≤ (F + 1) ^ depth (not (rd frmAlg acc a))
    generalize rd frmAlg acc a = c at h ⊢
    simp only [P] at h
    rw [size_not, depth_not, Nat.pow_succ]
    have h1 : 0 < (F + 1) ^ depth c := Nat.pow_pos (by omega)
    have h2 : (F + 1) ^ depth c * 2 ≤ (F + 1) ^ depth c * (F + 1) := Nat.mul_le_mul_left _ (by omega)
    omega
  | conj as =>
    show size (and (as.map (rd frmAlg acc))) ≤ (F + 1) ^ depth (and (as.map (rd frmAlg acc)))
    rw [size_and, depth_and]
    apply size_list_pow
    · simp only [List.length_map]; exact hg
    · intro c hc; obtain ⟨a, _, rfl⟩ := List.mem_map.mp hc; exact hrd a
    · intro c hc; exact le_listMax (List.mem_map_of_mem hc)
  | disj as =>
    show size (or (as.map (rd frmAlg acc))) ≤ (F + 1) ^ depth (or (as.map (rd frmAlg acc)))
    rw [size_or, depth_or]
    apply size_list_pow
    · simp only [List.length_map]; exact hg
    · intro c hc; obtain ⟨a, _, rfl⟩ := List.mem_map.mp hc; exact hrd a
    · intro c hc; exact le_listMax (List.mem_map_of_mem hc)

/-! ## Embedding a formula into a DAG -/

mutual
/-- Gates for formula c, appended to a program that already has `base` gates. -/
def emit (base : Nat) : Circ → List DGate
  | .input i => [.inp i]
  | .const b => [.cst b]
  | .not c => emit base c ++ [.neg (base + (emit base c).length - 1)]
  | .and cs => (emitL base cs).1 ++ [.conj (emitL base cs).2]
  | .or cs => (emitL base cs).1 ++ [.disj (emitL base cs).2]
/-- Gates for a list of formulas, with the indices of their output gates. -/
def emitL (base : Nat) : List Circ → List DGate × List Nat
  | [] => ([], [])
  | c :: cs => (emit base c ++ (emitL (base + (emit base c).length) cs).1,
      (base + (emit base c).length - 1) :: (emitL (base + (emit base c).length) cs).2)
end

mutual
theorem emit_len (base : Nat) : ∀ c : Circ, (emit base c).length = size c
  | .input i => by simp [emit]
  | .const b => by simp [emit]
  | .not c => by simp [emit, emit_len base c]
  | .and cs => by simp [emit, (emitL_len base cs).1]
  | .or cs => by simp [emit, (emitL_len base cs).1]
theorem emitL_len (base : Nat) : ∀ cs : List Circ,
    (emitL base cs).1.length = (cs.map size).sum ∧ (emitL base cs).2.length = cs.length
  | [] => by simp [emitL]
  | c :: cs => by
    have h := emitL_len (base + (emit base c).length) cs
    rw [emit_len base c] at h
    simp [emitL, emit_len base c, h.1, h.2]
end

theorem size_pos' (c : Circ) : 1 ≤ size c := by
  cases c <;> simp [size_input, size_const, size_not, size_and, size_or]

/-- Formula-side equations of an interpretation-valued function. -/
structure FHom {α : Type} (A : Alg α) (f : Circ → α) : Prop where
  inp : ∀ i, f (input i) = A.inp i
  cst : ∀ b, f (const b) = A.cst b
  neg : ∀ c, f (not c) = A.neg (f c)
  conj : ∀ cs, f (and cs) = A.conj (cs.map f)
  disj : ∀ cs, f (or cs) = A.disj (cs.map f)

section Emit
variable {α : Type} (A : Alg α) (f : Circ → α)

mutual
theorem emit_val (hf : FHom A f) (base : Nat) : ∀ (c : Circ) (acc : List α), acc.length = base →
    rd A (run A acc (emit base c)) (base + size c - 1) = f c
  | .input i, acc, hl => by
    simp only [emit, run, size_input]
    rw [show base + 1 - 1 = acc.length by omega, rd_snoc]; exact (hf.inp i).symm
  | .const b, acc, hl => by
    simp only [emit, run, size_const]
    rw [show base + 1 - 1 = acc.length by omega, rd_snoc]; exact (hf.cst b).symm
  | .not c, acc, hl => by
    have ih := emit_val hf base c acc hl
    have hlen := run_length A acc (emit base c)
    rw [emit_len] at hlen
    simp only [emit, run_append, run, size_not, emit_len]
    rw [show base + (size c + 1) - 1 = (run A acc (emit base c)).length by omega, rd_snoc]
    simp only [gstep]; rw [ih, hf.neg]
  | .and cs, acc, hl => by
    have ih := emitL_val hf base cs acc hl
    have hlen := run_length A acc (emitL base cs).1
    rw [(emitL_len base cs).1] at hlen
    simp only [emit, run_append, run, size_and]
    rw [show base + ((cs.map size).sum + 1) - 1 = (run A acc (emitL base cs).1).length by omega, rd_snoc]
    simp only [gstep]; rw [ih, hf.conj]
  | .or cs, acc, hl => by
    have ih := emitL_val hf base cs acc hl
    have hlen := run_length A acc (emitL base cs).1
    rw [(emitL_len base cs).1] at hlen
    simp only [emit, run_append, run, size_or]
    rw [show base + ((cs.map size).sum + 1) - 1 = (run A acc (emitL base cs).1).length by omega, rd_snoc]
    simp only [gstep]; rw [ih, hf.disj]
theorem emitL_val (hf : FHom A f) (base : Nat) : ∀ (cs : List Circ) (acc : List α), acc.length = base →
    (emitL base cs).2.map (rd A (run A acc (emitL base cs).1)) = cs.map f
  | [], _, _ => by simp [emitL]
  | c :: cs, acc, hl => by
    have h1 := emit_val hf base c acc hl
    have hlen := run_length A acc (emit base c)
    have hpos := size_pos' c
    rw [emit_len] at hlen
    have h2 := emitL_val hf (base + (emit base c).length) cs (run A acc (emit base c))
      (by rw [hlen, emit_len]; omega)
    simp only [emitL, List.map_cons, run_append]
    obtain ⟨W, hW, _⟩ := run_prefix A (run A acc (emit base c)) (emitL (base + (emit base c).length) cs).1
    rw [h2, hW, rd_append_left A _ W (by rw [hlen, emit_len]; omega), emit_len, h1]
end

end Emit

mutual
theorem emit_reads (base : Nat) : ∀ c : Circ, ∀ g ∈ emit base c, gmax g ≤ maxInput c
  | .input i => by intro g hg; simp [emit] at hg; subst hg; simp [gmax]
  | .const b => by intro g hg; simp [emit] at hg; subst hg; simp [gmax]
  | .not c => by
    intro g hg
    simp only [emit, List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | rfl
    · simpa using emit_reads base c g hg
    · simp [gmax]
  | .and cs => by
    intro g hg
    simp only [emit, List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | rfl
    · simpa using emitL_reads base cs g hg
    · simp [gmax]
  | .or cs => by
    intro g hg
    simp only [emit, List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | rfl
    · simpa using emitL_reads base cs g hg
    · simp [gmax]
theorem emitL_reads (base : Nat) : ∀ cs : List Circ, ∀ g ∈ (emitL base cs).1, gmax g ≤ listMax (cs.map maxInput)
  | [] => by intro g hg; simp [emitL] at hg
  | c :: cs => by
    intro g hg
    simp only [emitL, List.mem_append] at hg
    simp only [List.map_cons, listMax, List.foldr_cons]
    rcases hg with hg | hg
    · have := emit_reads base c g hg; omega
    · have := emitL_reads (base + (emit base c).length) cs g hg
      simp only [listMax] at this; omega
end

/-- The DAG of a formula: one gate per formula node, output = last gate. -/
def toDag (c : Circ) : Dag := ⟨emit 0 c, size c - 1⟩

/-- EMBEDDING: same function, same depth, exactly `size c` gates, same inputs read. -/
theorem toDag_spec (c : Circ) :
    (∀ x, (toDag c).eval x = eval x c) ∧ (toDag c).depth = depth c ∧ (toDag c).size = size c ∧
      (toDag c).Reads (maxInput c) := by
  refine ⟨fun x => ?_, ?_, ?_, emit_reads 0 c⟩
  · have hf : FHom (valAlg x) (eval x) :=
      ⟨fun _ => by simp [valAlg], fun _ => by simp [valAlg], fun _ => by simp [valAlg],
       fun _ => by simp [valAlg, List.all_map], fun _ => by simp [valAlg, List.any_map]⟩
    have := emit_val (valAlg x) (eval x) hf 0 c [] rfl
    simpa [Dag.eval, Dag.val, toDag] using this
  · have hf : FHom depAlg depth :=
      ⟨fun _ => by simp [depAlg], fun _ => by simp [depAlg], fun _ => by simp [depAlg],
       fun _ => by simp [depAlg], fun _ => by simp [depAlg]⟩
    have := emit_val depAlg depth hf 0 c [] rfl
    simpa [Dag.depth, Dag.val, toDag] using this
  · simp [Dag.size, toDag, emit_len]

/-! ## The two premise conventions -/

/-- The parity-correlation premise in the SHARED-CIRCUIT convention. -/
def DagParityPremise (d S m : Nat) (ε : Rat) : Prop :=
  ∀ D : Dag, D.depth ≤ d → D.size ≤ S → D.Reads m →
    -ε ≤ rsum (bitvecs m) (fun y => ind (D.eval (vfun y)) * sgn (par y)) / (2 : Rat) ^ m ∧
    rsum (bitvecs m) (fun y => ind (D.eval (vfun y)) * sgn (par y)) / (2 : Rat) ^ m ≤ ε

/-- The same, restricted to fan-in ≤ F (any number of gates). -/
def DagParityPremiseF (d F m : Nat) (ε : Rat) : Prop :=
  ∀ D : Dag, D.depth ≤ d → D.Fanin F → D.Reads m →
    -ε ≤ rsum (bitvecs m) (fun y => ind (D.eval (vfun y)) * sgn (par y)) / (2 : Rat) ^ m ∧
    rsum (bitvecs m) (fun y => ind (D.eval (vfun y)) * sgn (par y)) / (2 : Rat) ^ m ≤ ε

/-- The shared-circuit premise implies the formula premise at the same depth and size. -/
theorem formula_premise_of_dag {d S m : Nat} {ε : Rat} (h : DagParityPremise d S m ε) :
    ParityCorrPremise d S m ε := by
  intro C hd hs hm
  obtain ⟨he, hdep, hsz, hrd⟩ := toDag_spec C
  have := h (toDag C) (by rw [hdep]; exact hd) (by rw [hsz]; exact hs)
    (fun g hg => Nat.le_trans (hrd g hg) hm)
  simpa only [he] using this

/-- The formula premise at size (F+1)^d implies the shared-circuit premise for fan-in-F
    circuits of depth d (polynomial size for constant d and polynomial F). -/
theorem dag_premise_of_formula {d F m : Nat} {ε : Rat} (hF1 : 1 ≤ F)
    (h : ParityCorrPremise d ((F + 1) ^ d) m ε) : DagParityPremiseF d F m ε := by
  intro D hd hF hm
  have := h D.formula (by rw [formula_depth]; exact hd)
    (Nat.le_trans (formula_size hF1 D hF) (Nat.pow_le_pow_right (by omega) hd))
    (formula_maxInput D hm)
  simpa only [formula_eval] using this

/-- The network readout bound with the classical theorem assumed in the shared-circuit
    convention (same depth and size parameters as `BinReadout.network_readout_bound`). -/
theorem network_readout_bound_dag {W M B N j r L : Nat} (hj : j < B) (nets : Bool → List Layer)
    (hlen : ∀ b, (nets b).length = L) (hv : ∀ b, NetValid W (nets b))
    (hb : ∀ b, NetBounded M (nets b)) (hr : N + 1 ≤ 2 ^ r) {ε : Rat}
    (hprem : ∀ m, N + 1 ≤ m → m ≤ B * (N + 1) →
      DagParityPremise (3 * L + 2 + 11)
        (12 * Upar (N + 1) B ((r + 1) * (2 * ((2 * W + 3) ^ L * (M + 1) ^ (W * L)) + 1)) ^ 10) m ε) :
    succCountRO B (N + 1) (BinReadout.binReadoutOf B (N + 1)
        (fun b => BinReadout.netBCirc W B (N + 1) r (nets b))) j /
        nonzeroCount B (N + 1) ≤
      2 / (((2 ^ B : Nat) : Rat) - 1) + (((2 ^ B : Nat) : Rat) - 1) * ε :=
  BinReadout.network_readout_bound hj nets hlen hv hb hr
    (fun m h1 h2 => formula_premise_of_dag (hprem m h1 h2))


/-! ## Axiom audit -/

#print axioms run_append
#print axioms run_prefix
#print axioms run_length
#print axioms rd_append_left
#print axioms rd_snoc
#print axioms rd_map
#print axioms rd_inv
#print axioms run_inv
#print axioms gstep_hom
#print axioms run_hom
#print axioms eval_hom
#print axioms depth_hom
#print axioms maxIn_hom
#print axioms val_hom
#print axioms formula_eval
#print axioms formula_depth
#print axioms formula_maxInput
#print axioms size_list_pow
#print axioms formula_size
#print axioms emit_len
#print axioms emitL_len
#print axioms size_pos'
#print axioms emit_val
#print axioms emitL_val
#print axioms emit_reads
#print axioms emitL_reads
#print axioms toDag_spec
#print axioms formula_premise_of_dag
#print axioms dag_premise_of_formula
#print axioms network_readout_bound_dag
end Shared
end NimAudit
