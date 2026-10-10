import Foundation
import SharedCircuit
import LocalRestore
import ParityCircuit

/- Phase 4: composition of the phase-4 interfaces (coverage glue).  Written by Claude
   (10 October 2026).  Lean 4.26.0, core/Std only.

   The negative (single-frame) results now accept the classical input in any of three
   forms, each PROVED here to imply the formula premise of phase 3: the formula premise
   itself, the shared-circuit premise (`Shared.DagParityPremise`), or the restriction /
   switching bound (`Foundation.SwitchingBound`, the exact remaining classical content).
   All three remain explicit, unproved hypotheses. -/

namespace NimAudit
namespace Coverage

open Prob AC0 AC0.Circ Bridge CorrBridge Game

/-- Single-frame barrier from the switching bound (no formula premise assumed). -/
theorem no_strong_master_of_switching {S : BinReadout.BCirc} {m r d s : Nat} {p ε : Rat}
    (hb : BinReadout.BBound S (m + 1) 2 r d s) (hm : 1 ≤ m) (hε : ε < 1 / 2)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (h : Foundation.SwitchingBound d s m p ε) :
    ¬ ParityCircuit.StrongMastery S (m + 1) :=
  ParityCircuit.no_strong_master_of_premise hb hm hε (Foundation.premise_of_switching hp0 hp1 h)

/-- Single-frame barrier from the shared-circuit form of the classical theorem. -/
theorem no_strong_master_of_dag {S : BinReadout.BCirc} {m r d s : Nat} {ε : Rat}
    (hb : BinReadout.BBound S (m + 1) 2 r d s) (hm : 1 ≤ m) (hε : ε < 1 / 2)
    (h : Shared.DagParityPremise d s m ε) : ¬ ParityCircuit.StrongMastery S (m + 1) :=
  ParityCircuit.no_strong_master_of_premise hb hm hε (Shared.formula_premise_of_dag h)

/-- Network readout bound from the switching bound. -/
theorem network_readout_bound_switching {W M B N j r L : Nat} (hj : j < B) (nets : Bool → List Layer)
    (hlen : ∀ b, (nets b).length = L) (hv : ∀ b, NetValid W (nets b))
    (hb : ∀ b, NetBounded M (nets b)) (hr : N + 1 ≤ 2 ^ r) {p ε : Rat} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hsw : ∀ m, N + 1 ≤ m → m ≤ B * (N + 1) →
      Foundation.SwitchingBound (3 * L + 2 + 11)
        (12 * Upar (N + 1) B ((r + 1) * (2 * ((2 * W + 3) ^ L * (M + 1) ^ (W * L)) + 1)) ^ 10) m p ε) :
    succCountRO B (N + 1) (BinReadout.binReadoutOf B (N + 1)
        (fun b => BinReadout.netBCirc W B (N + 1) r (nets b))) j /
        nonzeroCount B (N + 1) ≤
      2 / (((2 ^ B : Nat) : Rat) - 1) + (((2 ^ B : Nat) : Rat) - 1) * ε :=
  BinReadout.network_readout_bound hj nets hlen hv hb hr
    (fun m h1 h2 => Foundation.premise_of_switching hp0 hp1 (hsw m h1 h2))

/-- Positive two-frame result, end to end: from a zero position Q and any legal
    opponent move Q → Q', the purely local circuit (no global nim-sum) selects a legal
    reply restoring nim-sum 0, identical to `NimGame.restore`. -/
theorem two_frame_restoration {B N : Nat} {Q Q' : List Nat} (hQ : Q.length = N) (hQ' : Q'.length = N)
    (hw : Width B Q) (hw' : Width B Q') (h0 : nimSum Q = 0) (hm : Game.Move Q Q') :
    ∃ i v, SelectCircuit.selReadout (LocalRestore.restC B N) (LocalRestore.tf B N Q Q') = some (i, v) ∧
      Game.Move Q' (Q'.set i v) ∧ nimSum (Q'.set i v) = 0 ∧
      SelectCircuit.SelBound (LocalRestore.restC B N) N B (4 + 9 + 4)
        (12 * ((N + 2) * (B + 2) * (B * (2 * B + 3) + 9 + 2)) ^ 8 * (10 * N + 1 + 1)) (2 * (B * N)) := by
  obtain ⟨i, v, h1, _, h3, h4⟩ := LocalRestore.restore_equiv hQ hQ' hw hw' h0 hm
  exact ⟨i, v, h1, h3, h4, LocalRestore.restC_bound⟩

/-- Positive multi-head result, end to end: the circuit reading the board and the B
    rollout outcomes outputs the verified decision move, with explicit resources. -/
theorem multi_head_selection {B N : Nat} {P : List Nat} (hP : P.length = N) (hw : Width B P) :
    SelectCircuit.selReadout (SelectCircuit.mhSel B N) (SelectCircuit.obsIn B N P (Game.outcomes P)) =
      Controller.decisionMove P ∧
    SelectCircuit.SelBound (SelectCircuit.mhSel B N) N B (4 + 9 + 3)
      (12 * ((N + 2) * (B + 2) * (B * (2 * B + 3) + 9 + 2)) ^ 8 * (9 + 1)) (B * N + B) :=
  ⟨SelectCircuit.mhSel_outcomes hP hw, SelectCircuit.mhSel_bound⟩


/-! ## Axiom audit -/

#print axioms no_strong_master_of_switching
#print axioms no_strong_master_of_dag
#print axioms network_readout_bound_switching
#print axioms two_frame_restoration
#print axioms multi_head_selection
end Coverage
end NimAudit
