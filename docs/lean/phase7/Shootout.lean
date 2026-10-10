import Misc
import BoardStore

/- Phase 7, Part A: the outer shootout controller in bounded binary registers, composed
   with the actual rollout executor.  Written by Claude (10 October 2026).
   Lean 4.26.0, core/Std only.

   ONE MACHINE, TWO SCHEDULES.  The register vector holds
     * the rollout registers of RolloutExec (board B·N bits, outcome parity, halt),
     * run (1 = running, 0 = done/hold), dec (OR of the outcomes consumed so far),
     * the head index j (r bits, LSB first; B ≤ 2^r), and
     * B stored outcome bits o₀ … o_{B−1}.
   Per tick the update reads the registers, a reset bit and the ORIGINAL BOARD P (B·N input
   wires, present at every tick; nothing else).  The schedule flag `early` is a
   construction parameter:
     early = true   the figure's controller: stop at the first outcome 1, or after head B−1;
     early = false  all heads in turn, retaining every outcome (needed for move selection).
   A tick does exactly one of: reset (load P, j := 0); one policy step of head j
   (multiplexed over the B certified step circuits); CONSUME a finished rollout (store its
   outcome, update dec, then stop, or advance j and reload P); hold when done.
   Nothing else enters: no outcome oracle, no nim-sum, no P.sum, no arithmetic primitive.
   Semantics (ostep) → bit formulas (cForms) → compiled network (cNet), with refinement,
   reset from arbitrary bits, termination, exact tick counts, refinement to Misc.shootout,
   and the all-head composition with the existing readout equal to mhExec. -/

namespace NimAudit
namespace Shootout

open Game Rollout Prob Attain Recurrent AC0 AC0.Circ CorrBridge AttainCircuit Bridge SelectCircuit
  BinReadout Controller ControllerBits PriorityEncoder ThresholdNet ThresholdInst FiniteNet WholeGame
  Family Barrier RolloutExec

/-! ## A1. Semantic registers and one tick -/

structure OS where
  rs : RS
  run : Bool
  dec : Bool
  j : Nat
  outs : Nat → Bool

/-- Total reset (from any register contents): load the board, head 0, nothing stored.
    Convention B = 0: there are no heads, run = 0 at once and dec = 0. -/
def initOS (B : Nat) (P : List Nat) : OS := ⟨⟨P, false, false⟩, decide (1 ≤ B), false, 0, fun _ => false⟩

/-- Stop condition when a rollout has finished: outcome 1 (early schedule) or last head. -/
def coreB (early : Bool) (B : Nat) (s : OS) : Bool := (early && s.rs.par) || decide (s.j = B - 1)

/-- One tick of the outer controller with its embedded rollout registers. -/
def ostep (early : Bool) (B : Nat) (P : List Nat) (rst : Bool) (s : OS) : OS :=
  if rst then initOS B P
  else if s.run = false then s
  else if s.rs.halted = false then { s with rs := rsStep (policyIdx s.j) s.rs }
  else if coreB early B s then
    { s with run := false, dec := s.dec || s.rs.par, outs := fun h => if h = s.j then s.rs.par else s.outs h }
  else
    ⟨⟨P, false, false⟩, true, s.dec || s.rs.par, s.j + 1, fun h => if h = s.j then s.rs.par else s.outs h⟩

/-- Valid states: the board has N heaps of width B, the index fits in r bits, and a
    running controller points at an existing head.  (Encodings with j ≥ B are unused; the
    reset maps every bit pattern to a valid state and valid states stay valid.) -/
structure Valid (B N r : Nat) (s : OS) : Prop where
  len : s.rs.board.length = N
  width : Width B s.rs.board
  jfit : s.j < 2 ^ r
  jrun : s.run = true → s.j < B

/-! ## Binary layout -/

def SW (B N r : Nat) : Nat := B * N + 4 + r + B
def jW (B N q : Nat) : Nat := B * N + 4 + q
def oW (B N r h : Nat) : Nat := B * N + 4 + r + h

/-- Register encoding: rollout registers (wires < BN+2), run (BN+2), dec (BN+3), head index
    bits (BN+4 …), stored outcomes (BN+4+r …); zero beyond SW. -/
def enc (B N r : Nat) (s : OS) : Nat → Bool := fun w =>
  if w < B * N + 2 then rsBits B N s.rs w
  else if w = B * N + 2 then s.run
  else if w = B * N + 3 then s.dec
  else if w < B * N + 4 + r then s.j.testBit (w - (B * N + 4))
  else if w < SW B N r then s.outs (w - (B * N + 4 + r))
  else false

/-- Per-tick input: registers (< SW), reset bit (SW), original board P (SW+1 …). -/
def zIn (B N r : Nat) (x : Nat → Bool) (rst : Bool) (P : List Nat) : Nat → Bool := fun w =>
  if w < SW B N r then x w else if w = SW B N r then rst else boardBits B P (w - (SW B N r + 1))

/-- Total input width of one update. -/
def IW (B N r : Nat) : Nat := SW B N r + 1 + B * N

/-! ## A2. The update formulas -/

def jlit (B N h q : Nat) : Circ := if h.testBit q then input (jW B N q) else not (input (jW B N q))
/-- Equality decoder j = h. -/
def isH (B N r h : Nat) : Circ := and ((List.range r).map (jlit B N h))
/-- Bit q of j + 1: bit q XOR (AND of all lower bits), constant depth. -/
def incB (B N q : Nat) : Circ := xor2 (input (jW B N q)) (and ((List.range q).map (fun t => input (jW B N t))))
/-- Renaming of a rollout step formula into the register layout (reset wire and external
    board of the step circuit are tied to 0: reloading is done by the outer multiplexer). -/
def σR (B N : Nat) : Nat → Circ := fun i => if i < B * N + 2 then input i else const false
/-- Head h's certified rollout step (RolloutExec.stepForms with the binary policy polBin). -/
def hstep (B N h w : Nat) : Circ := subst (σR B N) ((stepForms B N (polBin B N h (rIdx N))).getD w (const false))
/-- HEAD SELECTION: the step of the head named by the index register. -/
def mstep (B N r w : Nat) : Circ := or ((List.range B).map (fun h => and [isH B N r h, hstep B N h w]))

def rstI (B N r : Nat) : Circ := input (SW B N r)
def parI (B N : Nat) : Circ := input (B * N)
def haltI (B N : Nat) : Circ := input (B * N + 1)
def runI (B N : Nat) : Circ := input (B * N + 2)
def decI (B N : Nat) : Circ := input (B * N + 3)
def lastC (B N r : Nat) : Circ := isH B N r (B - 1)
def coreC (early : Bool) (B N r : Nat) : Circ := if early then or [parI B N, lastC B N r] else lastC B N r
def consC (B N : Nat) : Circ := and [runI B N, haltI B N]
def stepC (B N : Nat) : Circ := and [runI B N, not (haltI B N)]
def stopC (early : Bool) (B N r : Nat) : Circ := and [consC B N, coreC early B N r]
def contC (early : Bool) (B N r : Nat) : Circ := and [consC B N, not (coreC early B N r)]
def loadC (early : Bool) (B N r : Nat) : Circ := or [rstI B N r, contC early B N r]

def boardF (early : Bool) (B N r w : Nat) : Circ :=
  RolloutExec.mux (loadC early B N r) (input (SW B N r + 1 + w)) (RolloutExec.mux (stepC B N) (mstep B N r w) (input w))
def parF (early : Bool) (B N r : Nat) : Circ :=
  RolloutExec.mux (loadC early B N r) (const false) (RolloutExec.mux (stepC B N) (mstep B N r (B * N)) (input (B * N)))
def haltF (early : Bool) (B N r : Nat) : Circ :=
  RolloutExec.mux (loadC early B N r) (const false) (RolloutExec.mux (stepC B N) (mstep B N r (B * N + 1)) (input (B * N + 1)))
def runF (early : Bool) (B N r : Nat) : Circ :=
  RolloutExec.mux (rstI B N r) (const (decide (1 ≤ B))) (and [runI B N, not (stopC early B N r)])
def decF (B N r : Nat) : Circ := RolloutExec.mux (rstI B N r) (const false) (or [decI B N, and [consC B N, parI B N]])
def jF (early : Bool) (B N r q : Nat) : Circ :=
  RolloutExec.mux (rstI B N r) (const false) (RolloutExec.mux (contC early B N r) (incB B N q) (input (jW B N q)))
def oF (B N r h : Nat) : Circ :=
  RolloutExec.mux (rstI B N r) (const false) (RolloutExec.mux (and [consC B N, isH B N r h]) (parI B N) (input (oW B N r h)))

/-- THE UPDATE: SW = BN + 4 + r + B formulas, one per register bit. -/
def cForms (early : Bool) (B N r : Nat) : List Circ :=
  (List.range (B * N)).map (boardF early B N r) ++
    ([parF early B N r, haltF early B N r, runF early B N r, decF B N r] ++
      ((List.range r).map (jF early B N r) ++ (List.range B).map (oF B N r)))

/-- One clocked bit-level update. -/
def cstep (early : Bool) (B N r : Nat) (P : List Nat) (rst : Bool) (x : Nat → Bool) : Nat → Bool := fun w =>
  if w < SW B N r then eval (zIn B N r x rst P) ((cForms early B N r).getD w (const false)) else false

theorem cForms_length (early : Bool) (B N r : Nat) : (cForms early B N r).length = SW B N r := by
  simp [cForms, SW]; omega

theorem cF_board {early : Bool} {B N r w : Nat} (hw : w < B * N) :
    (cForms early B N r).getD w (const false) = boardF early B N r w := by
  unfold cForms
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simpa using hw), List.getElem?_map,
    List.getElem?_range hw]; rfl

theorem cF_mid (early : Bool) (B N r k : Nat) (hk : k < 4) :
    (cForms early B N r).getD (B * N + k) (const false) =
      [parF early B N r, haltF early B N r, runF early B N r, decF B N r].getD k (const false) := by
  unfold cForms
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp), List.getElem?_append_left (by simp; omega)]
  simp [List.getD_eq_getElem?_getD]

theorem cF_par (early : Bool) (B N r : Nat) : (cForms early B N r).getD (B * N) (const false) = parF early B N r := by
  have := cF_mid early B N r 0 (by omega); simpa using this
theorem cF_halt (early : Bool) (B N r : Nat) : (cForms early B N r).getD (B * N + 1) (const false) = haltF early B N r := by
  have := cF_mid early B N r 1 (by omega); simpa using this
theorem cF_run (early : Bool) (B N r : Nat) : (cForms early B N r).getD (B * N + 2) (const false) = runF early B N r := by
  have := cF_mid early B N r 2 (by omega); simpa using this
theorem cF_dec (early : Bool) (B N r : Nat) : (cForms early B N r).getD (B * N + 3) (const false) = decF B N r := by
  have := cF_mid early B N r 3 (by omega); simpa using this

theorem cF_j {early : Bool} {B N r q : Nat} (hq : q < r) :
    (cForms early B N r).getD (jW B N q) (const false) = jF early B N r q := by
  unfold cForms jW
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp; omega),
    List.getElem?_append_right (by simp; omega), List.getElem?_append_left (by simp; omega)]
  simp only [List.length_map, List.length_range, List.length_cons, List.length_nil]
  rw [show B * N + 4 + q - B * N - 4 = q by omega, List.getElem?_map, List.getElem?_range hq]; rfl

theorem cF_o {early : Bool} {B N r h : Nat} (hh : h < B) :
    (cForms early B N r).getD (oW B N r h) (const false) = oF B N r h := by
  unfold cForms oW
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp; omega),
    List.getElem?_append_right (by simp; omega), List.getElem?_append_right (by simp; omega)]
  simp only [List.length_map, List.length_range, List.length_cons, List.length_nil]
  rw [show B * N + 4 + r + h - B * N - 4 - r = h by omega, List.getElem?_map, List.getElem?_range hh]; rfl

/-! ## Signal evaluation -/

section Signals

variable {B N r : Nat} (s : OS) (rst : Bool) (P : List Nat)

theorem z_low {w : Nat} (hw : w < B * N + 2) : zIn B N r (enc B N r s) rst P w = rsBits B N s.rs w := by
  unfold zIn enc SW; rw [if_pos (by omega), if_pos hw]

theorem z_par : zIn B N r (enc B N r s) rst P (B * N) = s.rs.par := by
  rw [z_low s rst P (by omega)]; unfold rsBits; rw [if_neg (by omega), if_pos rfl]

theorem z_halt : zIn B N r (enc B N r s) rst P (B * N + 1) = s.rs.halted := by
  rw [z_low s rst P (by omega)]; unfold rsBits; rw [if_neg (by omega), if_neg (by omega), if_pos rfl]

theorem z_run : zIn B N r (enc B N r s) rst P (B * N + 2) = s.run := by
  unfold zIn enc SW; rw [if_pos (by omega), if_neg (by omega), if_pos rfl]

theorem z_dec : zIn B N r (enc B N r s) rst P (B * N + 3) = s.dec := by
  unfold zIn enc SW; rw [if_pos (by omega), if_neg (by omega), if_neg (by omega), if_pos rfl]

theorem z_j {q : Nat} (hq : q < r) : zIn B N r (enc B N r s) rst P (jW B N q) = s.j.testBit q := by
  unfold zIn enc SW jW; rw [if_pos (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_pos (by omega)]; congr 1; omega

theorem z_o {h : Nat} (hh : h < B) : zIn B N r (enc B N r s) rst P (oW B N r h) = s.outs h := by
  unfold zIn enc SW oW; rw [if_pos (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_pos (by omega)]; congr 1; omega

theorem z_rst (x : Nat → Bool) : zIn B N r x rst P (SW B N r) = rst := by
  unfold zIn; rw [if_neg (by omega), if_pos rfl]

theorem z_P (x : Nat → Bool) (w : Nat) : zIn B N r x rst P (SW B N r + 1 + w) = boardBits B P w := by
  unfold zIn; rw [if_neg (by omega), if_neg (by omega)]; congr 1; omega

theorem eval_isH_bits (h : Nat) :
    eval (zIn B N r (enc B N r s) rst P) (isH B N r h) = decide (∀ q < r, s.j.testBit q = h.testBit q) := by
  unfold isH
  rw [eval_and]
  apply Bool.eq_iff_iff.mpr
  rw [List.all_eq_true, decide_eq_true_iff]
  constructor
  · intro hall q hq
    have := hall (jlit B N h q) (List.mem_map.mpr ⟨q, List.mem_range.mpr hq, rfl⟩)
    unfold jlit at this
    split at this <;> simp_all [z_j s rst P hq]
  · intro hall c hc
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hc
    have hq' := List.mem_range.mp hq
    unfold jlit; have := hall q hq'
    split <;> simp_all [z_j s rst P hq']

theorem eval_isH {h : Nat} (hj : s.j < 2 ^ r) (hh : h < 2 ^ r) :
    eval (zIn B N r (enc B N r s) rst P) (isH B N r h) = decide (s.j = h) := by
  rw [eval_isH_bits]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_iff]
  exact ⟨fun hb => BoardStore.eq_of_low_bits hj hh hb, fun e q _ => by rw [e]⟩

theorem eval_incB {q : Nat} (hq : q < r) :
    eval (zIn B N r (enc B N r s) rst P) (incB B N q) = (s.j + 1).testBit q := by
  unfold incB
  rw [CorrBridge.eval_xor2, eval_input, z_j s rst P hq, ControllerBits.testBit_succ, eval_and]
  congr 1
  apply Bool.eq_iff_iff.mpr
  rw [List.all_eq_true, decide_eq_true_iff]
  constructor
  · intro hall t ht
    have := hall (input (jW B N t)) (List.mem_map.mpr ⟨t, List.mem_range.mpr ht, rfl⟩)
    rwa [eval_input, z_j s rst P (by omega)] at this
  · intro hall c hc
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hc
    have ht' := List.mem_range.mp ht
    rw [eval_input, z_j s rst P (by omega)]; exact hall t ht'

theorem eval_hstep (hl : s.rs.board.length = N) (hwd : Width B s.rs.board) (h : Nat) {w : Nat}
    (hw : w < B * N + 2) :
    eval (zIn B N r (enc B N r s) rst P) (hstep B N h w) = rsBits B N (rsStep (policyIdx h) s.rs) w := by
  unfold hstep
  rw [eval_subst]
  have e : (fun i => eval (zIn B N r (enc B N r s) rst P) (σR B N i)) = stepIn B N (rsBits B N s.rs) false [] := by
    funext i; unfold σR stepIn
    by_cases hi : i < B * N + 2
    · rw [if_pos hi, if_pos hi, eval_input, z_low s rst P hi]
    · rw [if_neg hi, if_neg hi, eval_const]
      split
      · rfl
      · simp [boardBits]
  rw [e]
  have := congrFun (bitStep_run (polSpec_polBin B N h) s.rs hl hwd []) w
  unfold bitStep at this; rw [if_pos hw] at this; exact this

theorem eval_mstep (hBr : B ≤ 2 ^ r) (hl : s.rs.board.length = N) (hwd : Width B s.rs.board) (hj : s.j < B)
    {w : Nat} (hw : w < B * N + 2) :
    eval (zIn B N r (enc B N r s) rst P) (mstep B N r w) = rsBits B N (rsStep (policyIdx s.j) s.rs) w := by
  unfold mstep
  rw [eval_or]
  apply Bool.eq_iff_iff.mpr
  rw [List.any_eq_true]
  constructor
  · rintro ⟨c, hc, he⟩
    obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hc
    have hh' := List.mem_range.mp hh
    simp only [eval_and, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at he
    rw [eval_isH s rst P (by omega) (by omega), decide_eq_true_iff] at he
    obtain ⟨rfl, he2⟩ := he
    rwa [eval_hstep s rst P hl hwd _ hw] at he2
  · intro he
    refine ⟨and [isH B N r s.j, hstep B N s.j w], List.mem_map.mpr ⟨s.j, List.mem_range.mpr hj, rfl⟩, ?_⟩
    simp only [eval_and, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
    rw [eval_isH s rst P (by omega) (by omega), eval_hstep s rst P hl hwd _ hw]
    exact ⟨by simp, he⟩

end Signals

/-- ostep without reset, as one flat record of Boolean cases. -/
theorem ostep_flat (early : Bool) (B : Nat) (P : List Nat) (s : OS) :
    ostep early B P false s =
      ⟨if (s.run && s.rs.halted && !coreB early B s) then ⟨P, false, false⟩
        else if (s.run && !s.rs.halted) then rsStep (policyIdx s.j) s.rs else s.rs,
       s.run && !(s.run && s.rs.halted && coreB early B s),
       s.dec || (s.run && s.rs.halted && s.rs.par),
       if (s.run && s.rs.halted && !coreB early B s) then s.j + 1 else s.j,
       fun h => if (s.run && s.rs.halted && decide (h = s.j)) then s.rs.par else s.outs h⟩ := by
  obtain ⟨rs, run, dec, j, outs⟩ := s
  unfold ostep
  cases run <;> cases hh : rs.halted <;> simp only [Bool.false_eq_true, if_false, if_true, Bool.false_and,
    Bool.and_false, Bool.true_and, Bool.not_false, Bool.not_true, Bool.or_false, Bool.and_true, hh] <;>
    (try rfl) <;> (cases hc : coreB early B ⟨rs, true, dec, j, outs⟩ <;> simp [hc])

/-! ## A1/A2. Reset from arbitrary bits and one-tick refinement -/

theorem enc_low (B N r : Nat) (s : OS) {w : Nat} (hw : w < B * N + 2) : enc B N r s w = rsBits B N s.rs w := by
  unfold enc; rw [if_pos hw]

theorem rsBits_board (B N : Nat) (t : RS) {w : Nat} (hw : w < B * N) : rsBits B N t w = boardBits B t.board w := by
  unfold rsBits; rw [if_pos hw]

theorem rsBits_par (B N : Nat) (t : RS) : rsBits B N t (B * N) = t.par := by
  unfold rsBits; rw [if_neg (by omega), if_pos rfl]

theorem rsBits_halt (B N : Nat) (t : RS) : rsBits B N t (B * N + 1) = t.halted := by
  unfold rsBits; rw [if_neg (by omega), if_neg (by omega), if_pos rfl]

theorem enc_run (B N r : Nat) (s : OS) : enc B N r s (B * N + 2) = s.run := by
  unfold enc; rw [if_neg (by omega), if_pos rfl]

theorem enc_dec (B N r : Nat) (s : OS) : enc B N r s (B * N + 3) = s.dec := by
  unfold enc; rw [if_neg (by omega), if_neg (by omega), if_pos rfl]

theorem enc_j (B N r : Nat) (s : OS) {q : Nat} (hq : q < r) : enc B N r s (jW B N q) = s.j.testBit q := by
  unfold enc jW; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]; congr 1; omega

theorem enc_o (B N r : Nat) (s : OS) {h : Nat} (hh : h < B) : enc B N r s (oW B N r h) = s.outs h := by
  unfold enc oW SW; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_pos (by omega)]; congr 1; omega

theorem enc_high (B N r : Nat) (s : OS) {w : Nat} (hw : SW B N r ≤ w) : enc B N r s w = false := by
  unfold enc SW at *; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega)]

/-- Every wire below SW is a board, par, halt, run, dec, index or outcome wire. -/
theorem wire_cases (B N r w : Nat) (hw : w < SW B N r) :
    w < B * N ∨ w = B * N ∨ w = B * N + 1 ∨ w = B * N + 2 ∨ w = B * N + 3 ∨
    (∃ q, q < r ∧ w = jW B N q) ∨ (∃ h, h < B ∧ w = oW B N r h) := by
  unfold SW at hw
  by_cases h1 : w < B * N + 4
  · omega
  · by_cases h2 : w < B * N + 4 + r
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨w - (B * N + 4), by omega, by unfold jW; omega⟩)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨w - (B * N + 4 + r), by omega, by unfold oW; omega⟩)))))

/-- TOTAL RESET: from ARBITRARY register bits, a reset tick yields the encoding of the
    initial state (board P loaded, head 0, run = [B ≥ 1], nothing stored). -/
theorem cstep_reset (early : Bool) (B N r : Nat) (P : List Nat) (x : Nat → Bool) :
    cstep early B N r P true x = enc B N r (initOS B P) := by
  funext w
  unfold cstep
  by_cases hw : w < SW B N r
  · rw [if_pos hw]
    have hload : eval (zIn B N r x true P) (loadC early B N r) = true := by
      simp [loadC, rstI, z_rst]
    have hrst : eval (zIn B N r x true P) (rstI B N r) = true := by simp [rstI, z_rst]
    rcases wire_cases B N r w hw with h | h | h | h | h | ⟨q, hq, rfl⟩ | ⟨k, hk, rfl⟩
    · rw [cF_board h, enc_low _ _ _ _ (by omega), rsBits_board _ _ _ h]
      simp only [boardF, eval_mux, hload, if_true, eval_input, z_P]; rfl
    · subst h; rw [cF_par, enc_low _ _ _ _ (by omega), rsBits_par]
      simp [parF, eval_mux, hload, initOS]
    · subst h; rw [cF_halt, enc_low _ _ _ _ (by omega), rsBits_halt]
      simp [haltF, eval_mux, hload, initOS]
    · subst h; rw [cF_run, enc_run]
      simp [runF, eval_mux, hrst, initOS]
    · subst h; rw [cF_dec, enc_dec]
      simp [decF, eval_mux, hrst, initOS]
    · rw [cF_j hq, enc_j _ _ _ _ hq]
      simp [jF, eval_mux, hrst, initOS]
    · rw [cF_o hk, enc_o _ _ _ _ hk]
      simp [oF, eval_mux, hrst, initOS]
  · rw [if_neg hw, enc_high _ _ _ _ (by omega)]

/-- ONE-TICK REFINEMENT (no reset): on every valid state the update formulas compute the
    encoding of the semantic tick. -/
theorem cstep_enc (early : Bool) {B N r : Nat} (hBr : B ≤ 2 ^ r) {P : List Nat} (hP : P.length = N)
    {s : OS} (hv : Valid B N r s) :
    cstep early B N r P false (enc B N r s) = enc B N r (ostep early B P false s) := by
  rw [ostep_flat]
  funext w
  unfold cstep
  have hB1 : B - 1 < 2 ^ r := by have := Nat.one_le_two_pow (n := r); omega
  have hr0 : eval (zIn B N r (enc B N r s) false P) (rstI B N r) = false := by simp [rstI, z_rst]
  have hst : eval (zIn B N r (enc B N r s) false P) (stepC B N) = (s.run && !s.rs.halted) := by
    simp [stepC, runI, haltI, z_run, z_halt]
  have hcs : eval (zIn B N r (enc B N r s) false P) (consC B N) = (s.run && s.rs.halted) := by simp [consC, runI, haltI, z_run, z_halt]
  have hcore : eval (zIn B N r (enc B N r s) false P) (coreC early B N r) = coreB early B s := by
    unfold coreC coreB lastC
    cases early
    · simp only [if_false, Bool.false_and, Bool.false_or]; exact eval_isH s false P hv.jfit hB1
    · simp only [if_true, Bool.true_and, eval_or, List.any_cons, List.any_nil, Bool.or_false]
      rw [eval_isH s false P hv.jfit hB1]; simp [parI, z_par]
  have hcont : eval (zIn B N r (enc B N r s) false P) (contC early B N r) = (s.run && s.rs.halted && !coreB early B s) := by
    simp only [contC, eval_and, eval_not, List.all_cons, List.all_nil, Bool.and_true, hcs, hcore]
  have hload : eval (zIn B N r (enc B N r s) false P) (loadC early B N r) = (s.run && s.rs.halted && !coreB early B s) := by
    simp only [loadC, eval_or, List.any_cons, List.any_nil, Bool.or_false, hr0, hcont, Bool.false_or]
  have hstop : eval (zIn B N r (enc B N r s) false P) (stopC early B N r) = (s.run && s.rs.halted && coreB early B s) := by
    simp only [stopC, eval_and, List.all_cons, List.all_nil, Bool.and_true, hcs, hcore]
  have hms : ∀ w, w < B * N + 2 → s.run = true →
      eval (zIn B N r (enc B N r s) false P) (mstep B N r w) = rsBits B N (rsStep (policyIdx s.j) s.rs) w :=
    fun w hw hrun => eval_mstep s false P hBr hv.len hv.width (hv.jrun hrun) hw
  by_cases hw : w < SW B N r
  · rw [if_pos hw]
    rcases wire_cases B N r w hw with h | h | h | h | h | ⟨q, hq, rfl⟩ | ⟨k, hk, rfl⟩
    · rw [cF_board h, enc_low _ _ _ _ (by omega), rsBits_board _ _ _ h]
      show eval (zIn B N r (enc B N r s) false P) (boardF early B N r w) = _
      simp only [boardF, eval_mux, hload, hst, eval_input]
      rw [z_P, z_low s false P (by omega), rsBits_board _ _ _ h]
      by_cases c1 : (s.run && s.rs.halted && !coreB early B s) = true
      · rw [if_pos c1, if_pos c1]
      · rw [if_neg c1, if_neg c1]
        by_cases c2 : (s.run && !s.rs.halted) = true
        · rw [if_pos c2, if_pos c2, hms w (by omega) (by simp at c2; exact c2.1), rsBits_board _ _ _ h]
        · rw [if_neg c2, if_neg c2]
    · subst h; rw [cF_par, enc_low _ _ _ _ (by omega), rsBits_par]
      show eval (zIn B N r (enc B N r s) false P) (parF early B N r) = _
      simp only [parF, eval_mux, hload, hst, eval_input, eval_const]
      rw [z_par]
      by_cases c1 : (s.run && s.rs.halted && !coreB early B s) = true
      · rw [if_pos c1, if_pos c1]
      · rw [if_neg c1, if_neg c1]
        by_cases c2 : (s.run && !s.rs.halted) = true
        · rw [if_pos c2, if_pos c2, hms _ (by omega) (by simp at c2; exact c2.1), rsBits_par]
        · rw [if_neg c2, if_neg c2]
    · subst h; rw [cF_halt, enc_low _ _ _ _ (by omega), rsBits_halt]
      show eval (zIn B N r (enc B N r s) false P) (haltF early B N r) = _
      simp only [haltF, eval_mux, hload, hst, eval_input, eval_const]
      rw [z_halt]
      by_cases c1 : (s.run && s.rs.halted && !coreB early B s) = true
      · rw [if_pos c1, if_pos c1]
      · rw [if_neg c1, if_neg c1]
        by_cases c2 : (s.run && !s.rs.halted) = true
        · rw [if_pos c2, if_pos c2, hms _ (by omega) (by simp at c2; exact c2.1), rsBits_halt]
        · rw [if_neg c2, if_neg c2]
    · subst h; rw [cF_run, enc_run]
      show eval (zIn B N r (enc B N r s) false P) (runF early B N r) = _
      simp only [runF, eval_mux, hr0, eval_and, eval_not, List.all_cons, List.all_nil, Bool.and_true, hstop,
        eval_input, Bool.false_eq_true, if_false]
      rw [show runI B N = input (B * N + 2) from rfl, eval_input, z_run]
    · subst h; rw [cF_dec, enc_dec]
      show eval (zIn B N r (enc B N r s) false P) (decF B N r) = _
      simp only [decF, eval_mux, hr0, eval_or, eval_and, List.any_cons, List.any_nil, List.all_cons,
        List.all_nil, Bool.and_true, Bool.or_false, hcs, eval_input, Bool.false_eq_true, if_false]
      rw [show decI B N = input (B * N + 3) from rfl, show parI B N = input (B * N) from rfl, eval_input,
        eval_input, z_dec, z_par]
    · rw [cF_j hq, enc_j _ _ _ _ hq]
      show eval (zIn B N r (enc B N r s) false P) (jF early B N r q) = _
      simp only [jF, eval_mux, hr0, hcont, eval_input, Bool.false_eq_true, if_false]
      rw [z_j s false P hq]
      by_cases c1 : (s.run && s.rs.halted && !coreB early B s) = true
      · rw [if_pos c1, if_pos c1, eval_incB s false P hq]
      · rw [if_neg c1, if_neg c1]
    · rw [cF_o hk, enc_o _ _ _ _ hk]
      show eval (zIn B N r (enc B N r s) false P) (oF B N r k) = _
      simp only [oF, eval_mux, hr0, eval_and, List.all_cons, List.all_nil, Bool.and_true, hcs, eval_input,
        Bool.false_eq_true, if_false]
      rw [eval_isH s false P hv.jfit (by omega), z_o s false P hk]
      show (if (s.run && s.rs.halted && decide (s.j = k)) = true then eval (zIn B N r (enc B N r s) false P) (parI B N) else s.outs k) = _
      rw [show parI B N = input (B * N) from rfl, eval_input, z_par]
      by_cases c : (s.run && s.rs.halted) = true
      · by_cases e : s.j = k
        · subst e; simp [c]
        · have e' : ¬ k = s.j := fun h => e h.symm
          simp [c, e, e']
      · have : (s.run && s.rs.halted) = false := by simpa using c
        simp [this]
  · rw [if_neg hw, enc_high _ _ _ _ (by omega)]

/-! ## Invariant, runs and the bit-level/semantic correspondence -/

theorem initOS_valid {B N r : Nat} {P : List Nat} (hP : P.length = N) (hwP : Width B P) :
    Valid B N r (initOS B P) :=
  ⟨hP, hwP, Nat.two_pow_pos r, fun h => by simp [initOS] at h; simp [initOS]; omega⟩

theorem ostep_valid (early : Bool) {B N r : Nat} (hBr : B ≤ 2 ^ r) {P : List Nat} (hP : P.length = N)
    (hwP : Width B P) {s : OS} (hv : Valid B N r s) : Valid B N r (ostep early B P false s) := by
  obtain ⟨hl, hw, hjf, hjr⟩ := hv
  unfold ostep
  cases hr : s.run
  · simp only [Bool.false_eq_true, if_false, if_true]; exact ⟨hl, hw, hjf, hjr⟩
  · have hj := hjr hr
    cases hh : s.rs.halted
    · simp only [Bool.false_eq_true, if_false, if_true]
      obtain ⟨h1, h2⟩ := rsStep_inv (polSpec_polBin B N s.j) s.rs hl hw
      exact ⟨h1, h2, hjf, fun _ => hj⟩
    · cases hc : coreB early B s
      · simp only [Bool.false_eq_true, Bool.true_eq_false, if_false, if_true]
        have hne : s.j ≠ B - 1 := by intro e; unfold coreB at hc; simp [e] at hc
        refine ⟨hP, hwP, ?_, fun _ => ?_⟩ <;> dsimp only <;> omega
      · simp only [Bool.false_eq_true, Bool.true_eq_false, if_false, if_true]
        exact ⟨hl, hw, hjf, fun h => by simp at h⟩

/-- Semantic run of k ticks (no reset). -/
def arun (early : Bool) (B : Nat) (P : List Nat) : Nat → OS → OS
  | 0, s => s
  | k + 1, s => arun early B P k (ostep early B P false s)

/-- Bit-level run of k ticks (no reset). -/
def brun (early : Bool) (B N r : Nat) (P : List Nat) : Nat → (Nat → Bool) → (Nat → Bool)
  | 0, x => x
  | k + 1, x => brun early B N r P k (cstep early B N r P false x)

theorem arun_add (early : Bool) (B : Nat) (P : List Nat) : ∀ a b s, arun early B P (a + b) s = arun early B P b (arun early B P a s)
  | 0, b, s => by simp [arun]
  | a + 1, b, s => by rw [show a + 1 + b = (a + b) + 1 by omega]; simp only [arun]; exact arun_add early B P a b _

/-- RUN REFINEMENT: from a valid state, k bit-level ticks compute the encoding of k
    semantic ticks, and the state stays valid. -/
theorem brun_enc (early : Bool) {B N r : Nat} (hBr : B ≤ 2 ^ r) {P : List Nat} (hP : P.length = N)
    (hwP : Width B P) : ∀ (k : Nat) (s : OS), Valid B N r s →
    brun early B N r P k (enc B N r s) = enc B N r (arun early B P k s) ∧ Valid B N r (arun early B P k s)
  | 0, s, hv => ⟨rfl, hv⟩
  | k + 1, s, hv => by
    simp only [brun, arun]
    rw [cstep_enc early hBr hP hv]
    exact brun_enc early hBr hP hwP k _ (ostep_valid early hBr hP hwP hv)

theorem arun_one (early : Bool) (B : Nat) (P : List Nat) (s : OS) : arun early B P 1 s = ostep early B P false s := rfl

/-- HOLD: a stopped controller (run = 0) is a fixed point of the tick. -/
theorem ostep_hold (early : Bool) (B : Nat) (P : List Nat) (s : OS) (h : s.run = false) :
    ostep early B P false s = s := by
  unfold ostep; simp [h]

theorem arun_hold (early : Bool) (B : Nat) (P : List Nat) (s : OS) (h : s.run = false) : ∀ k, arun early B P k s = s
  | 0 => rfl
  | k + 1 => by simp only [arun]; rw [ostep_hold early B P s h]; exact arun_hold early B P s h k

/-! ## A3. One rollout of head j inside the controller -/

/-- While the embedded rollout runs, each tick is one step of head j's policy and nothing
    else changes; untilHalt counts these ticks. -/
theorem arun_untilHalt (early : Bool) (B : Nat) (P : List Nat) (s : OS) (hrun : s.run = true) :
    ∀ (f : Nat) (t : RS),
      arun early B P (untilHalt (policyIdx s.j) f t).2 { s with rs := t } = { s with rs := (untilHalt (policyIdx s.j) f t).1 } ∧
      ∀ u, u ≤ (untilHalt (policyIdx s.j) f t).2 → (arun early B P u { s with rs := t }).run = true
  | 0, t => by
    refine ⟨rfl, fun u hu => ?_⟩
    obtain rfl : u = 0 := by simpa [untilHalt] using hu
    simpa [arun] using hrun
  | f + 1, t => by
    by_cases ht : t.halted = true
    · simp only [untilHalt, ht, if_true]
      refine ⟨rfl, fun u hu => ?_⟩
      obtain rfl : u = 0 := by omega
      simpa [arun] using hrun
    · have ht' : t.halted = false := by simpa using ht
      simp only [untilHalt, ht', Bool.false_eq_true, if_false]
      have hs : ostep early B P false { s with rs := t } = { s with rs := rsStep (policyIdx s.j) t } := by
        unfold ostep; simp [hrun, ht']
      obtain ⟨ih1, ih2⟩ := arun_untilHalt early B P s hrun f (rsStep (policyIdx s.j) t)
      refine ⟨by simp only [arun]; rw [hs]; exact ih1, fun u hu => ?_⟩
      rcases u with _ | u
      · simpa [arun] using hrun
      · simp only [arun]; rw [hs]; exact ih2 u (by omega)

/-- ROLLOUT PHASE: from the board Q freshly loaded for head j, after exactly L + 1 ticks
    (L = rolloutMoves j Q simulated moves, then the terminal test) the embedded registers
    hold the outcome RO_{π_j}(Q) with halt = 1; run stays 1 throughout. -/
theorem roll_phase (early : Bool) (B : Nat) (P : List Nat) (s : OS) (hrun : s.run = true) (Q : List Nat) :
    ∃ Qe, arun early B P (rolloutMoves s.j Q + 1) { s with rs := ⟨Q, false, false⟩ } =
        { s with rs := ⟨Qe, rolloutWinner s.j Q, true⟩ } ∧
      ∀ u, u ≤ rolloutMoves s.j Q + 1 → (arun early B P u { s with rs := ⟨Q, false, false⟩ }).run = true := by
  obtain ⟨h1, h2, h3⟩ := untilHalt_spec s.j (rolloutMoves s.j Q + 1) Q false (Nat.le_refl _)
  obtain ⟨e1, e2⟩ := arun_untilHalt early B P s hrun (rolloutMoves s.j Q + 1) ⟨Q, false, false⟩
  rw [h3] at e1 e2
  refine ⟨(untilHalt (policyIdx s.j) (rolloutMoves s.j Q + 1) ⟨Q, false, false⟩).1.board, ?_, e2⟩
  rw [e1]
  congr 1
  generalize (untilHalt (policyIdx s.j) (rolloutMoves s.j Q + 1) ⟨Q, false, false⟩).1 = t at h1 h2 ⊢
  obtain ⟨bd, pr, hl⟩ := t
  simp only at h1 h2
  rw [h1, h2]; simp

/-! ## A4. Macro step: one complete query of head j -/

/-- The controller with the original board freshly loaded for head j. -/
def ld (P : List Nat) (j : Nat) (dec : Bool) (outs : Nat → Bool) : OS := ⟨⟨P, false, false⟩, true, dec, j, outs⟩

def upd (outs : Nat → Bool) (j : Nat) (o : Bool) : Nat → Bool := fun h => if h = j then o else outs h

/-- ONE QUERY = L_j + 2 ticks: L_j moves, the terminal test, and one consume tick that
    stores the outcome and then stops or advances to head j+1 with the board reloaded. -/
theorem query_step (early : Bool) (B : Nat) (P : List Nat) (j : Nat) (dec : Bool) (outs : Nat → Bool) :
    ∃ Qe, arun early B P (rolloutMoves j P + 2) (ld P j dec outs) =
        (if ((early && rolloutWinner j P) || decide (j = B - 1)) then
          ⟨⟨Qe, rolloutWinner j P, true⟩, false, dec || rolloutWinner j P, j, upd outs j (rolloutWinner j P)⟩
        else ld P (j + 1) (dec || rolloutWinner j P) (upd outs j (rolloutWinner j P))) ∧
      ∀ u, u ≤ rolloutMoves j P + 1 → (arun early B P u (ld P j dec outs)).run = true := by
  obtain ⟨Qe, h1, h2⟩ := roll_phase early B P (ld P j dec outs) rfl P
  simp only [ld] at h1 h2
  refine ⟨Qe, ?_, fun u hu => by simp only [ld]; exact h2 u hu⟩
  rw [show rolloutMoves j P + 2 = (rolloutMoves j P + 1) + 1 from rfl, arun_add]
  simp only [ld]
  rw [h1, arun_one]
  unfold ostep coreB
  simp only [Bool.true_eq_false, Bool.false_eq_true, if_false, if_true]
  rfl

/-! ## A4. The early-exit schedule refines Misc.shootout -/

/-- Ticks used by the early-exit schedule from head j with k + 1 heads left. -/
def eeT (B : Nat) (P : List Nat) : Nat → Nat → Nat
  | 0, j => rolloutMoves j P + 2
  | k + 1, j => if rolloutWinner j P then rolloutMoves j P + 2 else rolloutMoves j P + 2 + eeT B P k (j + 1)

/-- Rollouts (head queries) executed by the early-exit schedule. -/
def eeR (P : List Nat) : Nat → Nat → Nat
  | 0, _ => 1
  | k + 1, j => if rolloutWinner j P then 1 else eeR P k (j + 1) + 1

theorem ee_run (B : Nat) (P : List Nat) : ∀ (k j : Nat), j + (k + 1) = B → ∀ outs : Nat → Bool,
    (arun true B P (eeT B P k j) (ld P j false outs)).run = false ∧
    (arun true B P (eeT B P k j) (ld P j false outs)).dec = (List.range' j (k + 1)).any (fun h => rolloutWinner h P) ∧
    (∀ u, u < eeT B P k j → (arun true B P u (ld P j false outs)).run = true) ∧
    (arun true B P (eeT B P k j) (ld P j false outs)).j + 1 = j + eeR P k j
  | 0, j, hj, outs => by
    obtain ⟨Qe, h1, h2⟩ := query_step true B P j false outs
    have hl : decide (j = B - 1) = true := by simp; omega
    rw [hl, Bool.or_true, if_pos rfl] at h1
    simp only [eeT]
    rw [h1]
    refine ⟨rfl, by simp, fun u hu => h2 u (by omega), by simp [eeR]⟩
  | k + 1, j, hj, outs => by
    obtain ⟨Qe, h1, h2⟩ := query_step true B P j false outs
    have hl : decide (j = B - 1) = false := by simp; omega
    rw [hl, Bool.or_false] at h1
    simp only [eeT]
    cases ho : rolloutWinner j P
    · have h1' : arun true B P (rolloutMoves j P + 2) (ld P j false outs) = ld P (j + 1) false (upd outs j false) := by
        rw [h1, ho]; rfl
      rw [if_neg (by simp), arun_add, h1']
      obtain ⟨i1, i2, i3, i4⟩ := ee_run B P k (j + 1) (by omega) (upd outs j false)
      have hd : (List.range' (j + 1) (k + 1)).any (fun h => rolloutWinner h P) =
          (List.range' j (k + 1 + 1)).any (fun h => rolloutWinner h P) := by
        rw [show List.range' j (k + 1 + 1) = j :: List.range' (j + 1) (k + 1) from List.range'_succ,
          List.any_cons, ho, Bool.false_or]
      refine ⟨i1, by rw [i2, hd], fun u hu => ?_, by simp only [eeR, ho, Bool.false_eq_true, if_false]; omega⟩
      by_cases hu' : u ≤ rolloutMoves j P + 1
      · exact h2 u hu'
      · obtain ⟨v, rfl⟩ : ∃ v, u = (rolloutMoves j P + 2) + v := ⟨u - (rolloutMoves j P + 2), by omega⟩
        rw [arun_add, h1']; exact i3 v (by omega)
    · have h1' : arun true B P (rolloutMoves j P + 2) (ld P j false outs) =
          ⟨⟨Qe, true, true⟩, false, true, j, upd outs j true⟩ := by
        rw [h1, ho]; rfl
      rw [if_pos rfl, h1']
      refine ⟨rfl, ?_, fun u hu => h2 u (by omega), by simp [eeR, ho]⟩
      show true = _
      rw [List.range'_succ, List.any_cons, ho, Bool.true_or]

/-- REFINEMENT TO Misc.shootout: the number of head queries of the binary controller is
    the query count of the abstract FSM, and the decision is the FSM's decision. -/
theorem eeR_shootout (B : Nat) (P : List Nat) : ∀ (k j : Nat), j + (k + 1) = B →
    eeR P k j = ((Misc.shootout B).run (fun h => rolloutWinner h P) (k + 2) j).2
  | 0, j, hj => by
    rw [Misc.run_query _ (by omega)]
    cases ho : rolloutWinner j P
    · simp only [Bool.false_eq_true, if_false]
      rw [if_neg (show ¬ j + 1 < B by omega), Misc.run_no]; rfl
    · simp only [if_true]; rw [Misc.run_yes]; rfl
  | k + 1, j, hj => by
    rw [Misc.run_query _ (by omega)]
    simp only [eeR]
    cases ho : rolloutWinner j P
    · simp only [Bool.false_eq_true, if_false]
      rw [if_pos (show j + 1 < B by omega), ← eeR_shootout B P k (j + 1) (by omega)]
    · simp only [if_true]; rw [Misc.run_yes]

theorem eeR_le (P : List Nat) : ∀ k j, eeR P k j ≤ k + 1
  | 0, _ => by simp [eeR]
  | k + 1, j => by
    simp only [eeR]; have := eeR_le P k (j + 1); split <;> omega

/-- EXACT TICK COUNT: the early-exit schedule uses Σ (L_h + 2) over the queried heads. -/
theorem eeT_sum (B : Nat) (P : List Nat) : ∀ k j,
    eeT B P k j = ((List.range' j (eeR P k j)).map (fun h => rolloutMoves h P + 2)).sum
  | 0, j => by simp [eeT, eeR]
  | k + 1, j => by
    simp only [eeT, eeR]
    cases rolloutWinner j P
    · simp only [Bool.false_eq_true, if_false]
      rw [List.range'_succ, List.map_cons, List.sum_cons, eeT_sum B P k (j + 1)]
    · simp

theorem eeT_le (B : Nat) {P : List Nat} (hw : Width B P) : ∀ k j, eeT B P k j ≤ (k + 1) * (clockBound B P.length + 1)
  | 0, j => by have := clock_ok (j := j) hw; simp only [eeT]; omega
  | k + 1, j => by
    have := clock_ok (j := j) hw
    have ih := eeT_le B hw k (j + 1)
    simp only [eeT]; split
    · have : clockBound B P.length + 1 ≤ (k + 1 + 1) * (clockBound B P.length + 1) :=
        Nat.le_mul_of_pos_left _ (by omega)
      omega
    · rw [Nat.succ_mul]; omega

/-- The fixed padded clock (ticks after the reset tick): B·(N(2^B − 1) + 2). -/
def Tmax (B N : Nat) : Nat := B * (clockBound B N + 1)

/-- EARLY-EXIT SEMANTIC THEOREM (B ≥ 1): after the reset, the controller stops after exactly
    T = eeT ticks (running at every earlier tick), with decision dec = [nim(P) ≠ 0]; the
    decision and the number of queries are those of Misc.shootout run on the actual
    rollout outcomes; T ≤ Tmax. -/
theorem ee_spec {B : Nat} (hB : 1 ≤ B) {P : List Nat} (hw : Width B P) :
    (arun true B P (eeT B P (B - 1) 0) (initOS B P)).run = false ∧
    (arun true B P (eeT B P (B - 1) 0) (initOS B P)).dec = decide (nimSum P ≠ 0) ∧
    (∀ u, u < eeT B P (B - 1) 0 → (arun true B P u (initOS B P)).run = true) ∧
    some (arun true B P (eeT B P (B - 1) 0) (initOS B P)).dec =
      ((Misc.shootout B).run (fun h => rolloutWinner h P) (B + 1) 0).1 ∧
    eeR P (B - 1) 0 = ((Misc.shootout B).run (fun h => rolloutWinner h P) (B + 1) 0).2 ∧
    eeR P (B - 1) 0 ≤ B ∧ eeT B P (B - 1) 0 ≤ Tmax B P.length ∧
    (arun true B P (eeT B P (B - 1) 0) (initOS B P)).j + 1 = eeR P (B - 1) 0 := by
  have hinit : initOS B P = ld P 0 false (fun _ => false) := by
    simp [initOS, ld]; omega
  rw [hinit]
  obtain ⟨h1, h2, h3, h4⟩ := ee_run B P (B - 1) 0 (by omega) (fun _ => false)
  have hsh := Misc.shootout_from (B := B) (fun h => rolloutWinner h P) (B - 1) 0 (by omega)
  rw [show B - 1 + 2 = B + 1 by omega] at hsh
  have hR := eeR_shootout B P (B - 1) 0 (by omega)
  rw [show B - 1 + 2 = B + 1 by omega] at hR
  refine ⟨h1, ?_, h3, ?_, hR, by have := eeR_le P (B - 1) 0; omega, ?_, by rw [h4]; omega⟩
  · rw [h2, show B - 1 + 1 = B by omega, ← List.range_eq_range']; exact Misc.channels_or hB hw
  · rw [hsh, h2]
  · have := eeT_le B hw (B - 1) 0; unfold Tmax; rw [show B - 1 + 1 = B by omega] at this; exact this

/-! ## A3/A4. The bit-level early-exit implementation -/

/-- THE IMPLEMENTATION: one reset tick from arbitrary register bits x₀, then T clocked
    ticks of the update formulas (input: registers, reset bit 0, the board P). -/
def impl (early : Bool) (B N r : Nat) (P : List Nat) (T : Nat) (x0 : Nat → Bool) : Nat → Bool :=
  brun early B N r P T (cstep early B N r P true x0)

theorem impl_enc (early : Bool) {B N r : Nat} (hBr : B ≤ 2 ^ r) {P : List Nat} (hP : P.length = N)
    (hwP : Width B P) (T : Nat) (x0 : Nat → Bool) :
    impl early B N r P T x0 = enc B N r (arun early B P T (initOS B P)) := by
  unfold impl; rw [cstep_reset]; exact (brun_enc early hBr hP hwP T _ (initOS_valid hP hwP)).1

theorem nimSum_width0 {P : List Nat} (hw : Width 0 P) : nimSum P = 0 := by
  have := nimSum_lt hw; simp at this; exact this

/-- EARLY-EXIT CLASSIFIER, BIT LEVEL: for every B (B = 0 by the stated convention), every
    board of N heaps of width B, every initial register content and every clock
    T ≥ eeT (in particular the fixed padded clock Tmax B N), the dec wire holds
    [nim(P) ≠ 0] and the run wire is 0. -/
theorem ee_impl (B N r : Nat) (hBr : B ≤ 2 ^ r) {P : List Nat} (hP : P.length = N) (hw : Width B P)
    (x0 : Nat → Bool) (T : Nat) (hT : 1 ≤ B → eeT B P (B - 1) 0 ≤ T) :
    impl true B N r P T x0 (B * N + 3) = decide (nimSum P ≠ 0) ∧ impl true B N r P T x0 (B * N + 2) = false := by
  rw [impl_enc true hBr hP hw, enc_dec, enc_run]
  rcases Nat.eq_zero_or_pos B with hB | hB
  · subst hB
    have hrun : (initOS 0 P).run = false := by simp [initOS]
    rw [arun_hold true 0 P _ hrun]
    simp [initOS, nimSum_width0 hw]
  · obtain ⟨h1, h2, _⟩ := ee_spec hB hw
    obtain ⟨d, rfl⟩ : ∃ d, T = eeT B P (B - 1) 0 + d := ⟨T - eeT B P (B - 1) 0, by have := hT hB; omega⟩
    rw [arun_add, arun_hold true B P _ h1]
    exact ⟨h2, h1⟩

/-- The padded clock suffices. -/
theorem ee_impl_padded (B N r : Nat) (hBr : B ≤ 2 ^ r) {P : List Nat} (hP : P.length = N) (hw : Width B P)
    (x0 : Nat → Bool) :
    impl true B N r P (Tmax B N) x0 (B * N + 3) = decide (nimSum P ≠ 0) :=
  (ee_impl B N r hBr hP hw x0 (Tmax B N) (fun hB => by have := (ee_spec hB hw).2.2.2.2.2.2.1; rwa [hP] at this)).1

/-! ## Early stopping: a halting loop on the run wire, with exact tick count -/

/-- Clock the update while the run wire is 1 (fuel f); returns the registers and the number
    of ticks executed. -/
def loopRun (step : (Nat → Bool) → (Nat → Bool)) (hw : Nat) : Nat → (Nat → Bool) → (Nat → Bool) × Nat
  | 0, x => (x, 0)
  | f + 1, x => if x hw = true then ((loopRun step hw f (step x)).1, (loopRun step hw f (step x)).2 + 1) else (x, 0)

theorem loopRun_spec (early : Bool) {B N r : Nat} (hBr : B ≤ 2 ^ r) {P : List Nat} (hP : P.length = N)
    (hwP : Width B P) : ∀ (T f : Nat) (s : OS), Valid B N r s → T ≤ f →
    (∀ u, u < T → (arun early B P u s).run = true) → (arun early B P T s).run = false →
    loopRun (cstep early B N r P false) (B * N + 2) f (enc B N r s) = (enc B N r (arun early B P T s), T)
  | 0, f, s, hv, _, _, hstop => by
    cases f with
    | zero => rfl
    | succ f => simp only [loopRun, enc_run]; simp only [arun] at hstop; simp [hstop, arun]
  | T + 1, f, s, hv, hTf, hrun, hstop => by
    obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
    have h0 : s.run = true := by simpa [arun] using hrun 0 (by omega)
    simp only [loopRun, enc_run, h0, if_true]
    rw [cstep_enc early hBr hP hv]
    have ih := loopRun_spec early hBr hP hwP T f (ostep early B P false s) (ostep_valid early hBr hP hwP hv) (by omega)
      (fun u hu => hrun (u + 1) (by omega)) hstop
    rw [ih]; rfl

/-- EARLY STOPPING, BIT LEVEL: the halting loop on the run wire stops after exactly
    1 (reset) + eeT ticks, Σ over the queried heads of (L_h + 2), with the decision on the
    dec wire.  (The padded clock instead always runs Tmax ticks; both give the same
    registers, ostep_hold.) -/
theorem ee_loop {B N r : Nat} (hB : 1 ≤ B) (hBr : B ≤ 2 ^ r) {P : List Nat} (hP : P.length = N) (hw : Width B P)
    (x0 : Nat → Bool) :
    (loopRun (cstep true B N r P false) (B * N + 2) (Tmax B N) (cstep true B N r P true x0)).2 = eeT B P (B - 1) 0 ∧
    (loopRun (cstep true B N r P false) (B * N + 2) (Tmax B N) (cstep true B N r P true x0)).1 (B * N + 3) =
      decide (nimSum P ≠ 0) := by
  obtain ⟨h1, h2, h3, _, _, _, h7, _⟩ := ee_spec hB hw
  rw [cstep_reset, loopRun_spec true hBr hP hw _ _ _ (initOS_valid hP hw) (by rw [← hP]; exact h7) h3 h1]
  exact ⟨rfl, by show enc B N r _ (B * N + 3) = _; rw [enc_dec, h2]⟩

/-! ## A5. All heads retained, then the existing readout: the move path -/

/-- Ticks of the all-head schedule from head j with k + 1 heads left. -/
def ahT (P : List Nat) : Nat → Nat → Nat
  | 0, j => rolloutMoves j P + 2
  | k + 1, j => rolloutMoves j P + 2 + ahT P k (j + 1)

theorem ah_run (B : Nat) (P : List Nat) : ∀ (k j : Nat), j + (k + 1) = B → ∀ (dec : Bool) (outs : Nat → Bool),
    (∀ h, h < j → outs h = rolloutWinner h P) →
    (arun false B P (ahT P k j) (ld P j dec outs)).run = false ∧
    (∀ h, h < B → (arun false B P (ahT P k j) (ld P j dec outs)).outs h = rolloutWinner h P) ∧
    (∀ u, u < ahT P k j → (arun false B P u (ld P j dec outs)).run = true)
  | 0, j, hj, dec, outs, ho => by
    obtain ⟨Qe, h1, h2⟩ := query_step false B P j dec outs
    have hl : decide (j = B - 1) = true := by simp; omega
    rw [Bool.false_and, Bool.false_or, hl, if_pos rfl] at h1
    simp only [ahT]; rw [h1]
    refine ⟨rfl, fun h hh => ?_, fun u hu => h2 u (by omega)⟩
    simp only [upd]; split
    · subst_vars; rfl
    · exact ho h (by omega)
  | k + 1, j, hj, dec, outs, ho => by
    obtain ⟨Qe, h1, h2⟩ := query_step false B P j dec outs
    have hl : decide (j = B - 1) = false := by simp; omega
    rw [Bool.false_and, Bool.false_or, hl, if_neg (by simp)] at h1
    simp only [ahT]
    rw [arun_add, h1]
    have ho' : ∀ h, h < j + 1 → upd outs j (rolloutWinner j P) h = rolloutWinner h P := by
      intro h hh; simp only [upd]; split
      · subst_vars; rfl
      · exact ho h (by omega)
    obtain ⟨i1, i2, i3⟩ := ah_run B P k (j + 1) (by omega) _ _ ho'
    refine ⟨i1, i2, fun u hu => ?_⟩
    by_cases hu' : u ≤ rolloutMoves j P + 1
    · exact h2 u hu'
    · obtain ⟨v, rfl⟩ : ∃ v, u = (rolloutMoves j P + 2) + v := ⟨u - (rolloutMoves j P + 2), by omega⟩
      rw [arun_add, h1]; exact i3 v (by omega)

theorem ahT_sum (P : List Nat) : ∀ k j, ahT P k j = ((List.range' j (k + 1)).map (fun h => rolloutMoves h P)).sum + 2 * (k + 1)
  | 0, j => by simp [ahT]
  | k + 1, j => by
    rw [ahT, ahT_sum P k (j + 1), show List.range' j (k + 1 + 1) = j :: List.range' (j + 1) (k + 1) from List.range'_succ]
    simp only [List.map_cons, List.sum_cons]; omega

/-- ALL-HEAD TICKS: exactly totalRolloutMoves + 2B ticks after the reset. -/
theorem ahT_total {B : Nat} (hB : 1 ≤ B) (P : List Nat) : ahT P (B - 1) 0 = totalRolloutMoves B P + 2 * B := by
  rw [ahT_sum, totalRolloutMoves, List.range_eq_range', show B - 1 + 1 = B by omega]

theorem ahT_le (B : Nat) {P : List Nat} (hw : Width B P) : ∀ k j, ahT P k j ≤ (k + 1) * (clockBound B P.length + 1)
  | 0, j => by have := clock_ok (j := j) hw; simp only [ahT]; omega
  | k + 1, j => by
    have := clock_ok (j := j) hw; have := ahT_le B hw k (j + 1)
    simp only [ahT]; rw [Nat.succ_mul]; omega

theorem reconstruct_congr {B : Nat} {o1 o2 : Nat → Bool} (h : ∀ j, j < B → o1 j = o2 j) :
    reconstruct B o1 = reconstruct B o2 := by
  unfold reconstruct
  have key : ∀ k, k ≤ B → ofBits k (recoverBit o1) = ofBits k (recoverBit o2) := by
    intro k
    induction k with
    | zero => intro _; rfl
    | succ k ih =>
      intro hk
      simp only [ofBits]
      rw [ih (by omega)]
      congr 2
      unfold recoverBit
      split
      · rw [h 0 (by omega)]
      · rw [h k (by omega), h 0 (by omega)]
  exact key B (Nat.le_refl _)

/-- The all-head move: run the all-head schedule on the padded clock from a reset, then
    evaluate the EXISTING readout network on the board and the stored outcome bits. -/
def ahMove (B : Nat) (P : List Nat) : Option (Nat × Nat) :=
  netBinSem (mhN (B, P.length)) P.length (rIdx P.length) B
    (obsIn B P.length P (fun h => impl false B P.length (rIdx B) P (Tmax B P.length) (fun _ => false) (oW B P.length (rIdx B) h)))

def ahSel (B : Nat) (P : List Nat) : Option (List Nat) := applyM P (ahMove B P)

/-- IMPLEMENTATION EQUALITY: the binary outer controller with retained outcomes followed by
    the readout network computes exactly mhExec (hence decisionMove). -/
theorem ahMove_eq {B : Nat} {P : List Nat} (hw : Width B P) : ahMove B P = mhExec B P := by
  have hBr : B ≤ 2 ^ rIdx B := Nat.le_of_lt (rIdx_counter B)
  unfold ahMove mhExec
  rw [(mh_semantics rfl hw _).2.1]
  show attainT _ P = netBinSem (mhN (B, P.length)) P.length (rIdx P.length) B _
  rw [(mh_semantics rfl hw _).2.1]
  congr 1
  apply reconstruct_congr
  intro h hh
  rw [outBit_eq hw, impl_enc false hBr rfl hw]
  have hB : 1 ≤ B := by omega
  obtain ⟨h1, h2, _⟩ := ah_run B P (B - 1) 0 (by omega) false (fun _ => false) (fun h hh => by omega)
  have hinit : initOS B P = ld P 0 false (fun _ => false) := by simp [initOS, ld]; omega
  have hle : ahT P (B - 1) 0 ≤ Tmax B P.length := by
    have := ahT_le B hw (B - 1) 0; unfold Tmax; rw [show B - 1 + 1 = B by omega] at this; exact this
  obtain ⟨d, hd⟩ : ∃ d, Tmax B P.length = ahT P (B - 1) 0 + d := ⟨Tmax B P.length - ahT P (B - 1) 0, by omega⟩
  rw [hd, hinit, arun_add, arun_hold false B P _ h1, enc_o _ _ _ _ hh, h2 h hh]

/-- WINNING: the implemented all-head controller plus readout wins from every nonzero
    position against every legal opponent (reusing the whole-game theorem mhExec_wins). -/
theorem ahSel_wins {B : Nat} {P : List Nat} (hw : Width B P) (h : nimSum P ≠ 0) : Wins (ahSel B) P :=
  wins_congr (fun Q hQ => by unfold ahSel mhExecSel; rw [ahMove_eq hQ]) hw (mhExec_wins hw h)

/-- EARLY EXIT DOES NOT SUPPLY THE MOVE: for B = 2 and P = (1), the early-exit schedule stops
    after head 0 (outcome 1) with stored bit o₁ = 0, whereas RO_{π₁}(P) = 1; so its stored
    bits are not the readout's input.  Winning-move selection needs the all-head path. -/
theorem early_exit_not_move :
    rolloutWinner 0 [1] = true ∧ rolloutWinner 1 [1] = true ∧
    ∃ s', arun true 2 [1] (rolloutMoves 0 [1] + 2) (initOS 2 [1]) = s' ∧ s'.run = false ∧ s'.outs 1 = false := by
  have h0 : rolloutWinner 0 [1] = true := by rw [rolloutWinner_channel]; decide
  have h1 : rolloutWinner 1 [1] = true := by rw [rolloutWinner_channel]; decide
  refine ⟨h0, h1, ?_⟩
  obtain ⟨Qe, e1, _⟩ := query_step true 2 [1] 0 false (fun _ => false)
  have hinit : initOS 2 [1] = ld [1] 0 false (fun _ => false) := rfl
  rw [h0] at e1
  refine ⟨_, rfl, ?_⟩
  rw [hinit, e1]
  simp [upd]

/-! ## A2. The compiled fixed-scale network: same formulas -/

def cNet (early : Bool) (B N r : Nat) : List Layer := compileF (cForms early B N r)

/-- One tick of the threshold network (registers = its first SW outputs). -/
def nstep (early : Bool) (B N r : Nat) (P : List Nat) (rst : Bool) (x : Nat → Bool) : Nat → Bool := fun w =>
  if w < SW B N r then evalNet (cNet early B N r) (zIn B N r x rst P) w else false

theorem nstep_eq (early : Bool) (B N r : Nat) (P : List Nat) (rst : Bool) (x : Nat → Bool) :
    nstep early B N r P rst x = cstep early B N r P rst x := by
  funext w
  unfold nstep cstep cNet
  by_cases hw : w < SW B N r
  · rw [if_pos hw, if_pos hw, compileF_eval _ _ (by rw [cForms_length]; exact hw),
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [cForms_length]; exact hw)]
    rfl
  · rw [if_neg hw, if_neg hw]

/-- Network implementation: reset tick, then T network ticks. -/
def nrun (early : Bool) (B N r : Nat) (P : List Nat) : Nat → (Nat → Bool) → (Nat → Bool)
  | 0, x => x
  | k + 1, x => nrun early B N r P k (nstep early B N r P false x)

def nimpl (early : Bool) (B N r : Nat) (P : List Nat) (T : Nat) (x0 : Nat → Bool) : Nat → Bool :=
  nrun early B N r P T (nstep early B N r P true x0)

theorem nimpl_eq (early : Bool) (B N r : Nat) (P : List Nat) (T : Nat) (x0 : Nat → Bool) :
    nimpl early B N r P T x0 = impl early B N r P T x0 := by
  unfold nimpl impl
  rw [nstep_eq]
  generalize cstep early B N r P true x0 = x
  induction T generalizing x with
  | zero => rfl
  | succ T ih => simp only [nrun, brun]; rw [nstep_eq]; exact ih _

/-- THE NETWORK-EXECUTED CLASSIFIER and MOVE: the same theorems hold for the threshold
    network implementation. -/
theorem ee_net (B N r : Nat) (hBr : B ≤ 2 ^ r) {P : List Nat} (hP : P.length = N) (hw : Width B P) (x0 : Nat → Bool) :
    nimpl true B N r P (Tmax B N) x0 (B * N + 3) = decide (nimSum P ≠ 0) := by
  rw [nimpl_eq]; exact ee_impl_padded B N r hBr hP hw x0

/-! ## A2. Resources of the update formulas -/

def R3 (d s m : Nat) (c : Circ) : Prop := depth c ≤ d ∧ size c ≤ s ∧ maxInput c ≤ m

theorem and_res {cs : List Circ} {d s m : Nat} (h : ∀ c ∈ cs, R3 d s m c) : R3 (d + 1) (cs.length * s + 1) m (and cs) :=
  ⟨depth_and_le (fun c hc => (h c hc).1), ControllerBits.size_and_le' (fun c hc => (h c hc).2.1),
    ControllerBits.maxInput_and_le (fun c hc => (h c hc).2.2)⟩

theorem or_res {cs : List Circ} {d s m : Nat} (h : ∀ c ∈ cs, R3 d s m c) : R3 (d + 1) (cs.length * s + 1) m (or cs) :=
  ⟨depth_or_le (fun c hc => (h c hc).1), ControllerBits.size_or_le' (fun c hc => (h c hc).2.1),
    ControllerBits.maxInput_or_le (fun c hc => (h c hc).2.2)⟩

theorem R3_mono {d s m d' s' m' : Nat} {c : Circ} (h : R3 d s m c) (hd : d ≤ d') (hs : s ≤ s') (hm : m ≤ m') :
    R3 d' s' m' c := ⟨by have := h.1; omega, by have := h.2.1; omega, by have := h.2.2; omega⟩

theorem not_res {c : Circ} {d s m : Nat} (h : R3 d s m c) : R3 (d + 1) (s + 1) m (not c) := by
  refine ⟨?_, ?_, ?_⟩ <;> simp only [depth_not, size_not, maxInput_not] <;> have := h.1 <;> have := h.2.1 <;>
    have := h.2.2 <;> omega

theorem inp3 {i m : Nat} (h : i + 1 ≤ m) : R3 0 1 m (input i) := BoardStore.inp_res h
theorem cst3 (b : Bool) (m : Nat) : R3 0 1 m (const b) := by refine ⟨?_, ?_, ?_⟩ <;> simp

theorem mux3 {c a b : Circ} {dc sc mc da sa ma db sb mb : Nat} (hc : R3 dc sc mc c) (ha : R3 da sa ma a)
    (hb : R3 db sb mb b) : R3 (max (dc + 1) (max da db) + 2) (2 * sc + sa + sb + 4) (max mc (max ma mb))
      (RolloutExec.mux c a b) := BoardStore.mux_res hc ha hb

/-- Size bound of one rollout-step formula of head h (from the certified policy circuit). -/
def S1 (B N : Nat) : Nat := stepZ (rIdx N) N (polSz B N)

theorem S1_pos (B N : Nat) : 1 ≤ S1 B N := by unfold S1 stepZ; omega

theorem hstep_res (B N h w : Nat) : R3 28 (S1 B N) (B * N + 2) (hstep B N h w) := by
  unfold hstep
  have hleaf : ∀ i, IsLeaf (σR B N i) := fun i => by unfold σR; split <;> trivial
  have hc : R3 28 (S1 B N) (2 * (B * N) + 3) ((stepForms B N (polBin B N h (rIdx N))).getD w (const false)) := by
    rw [List.getD_eq_getElem?_getD]
    cases hg : (stepForms B N (polBin B N h (rIdx N)))[w]? with
    | none => simp only [Option.getD_none]; exact ⟨by simp, by simp; exact S1_pos B N, by simp⟩
    | some c => exact stepForms_res (polBin_bound (j := h) (rIdx_width N)) c (List.mem_of_getElem? hg)
  refine ⟨by rw [depth_subst_leaf _ hleaf]; exact hc.1, by rw [size_subst_leaf _ hleaf]; exact hc.2.1, ?_⟩
  apply maxInput_subst_le
  intro i; unfold σR; split
  · simp; omega
  · simp

theorem isH_res (B N r h : Nat) : R3 2 (2 * r + 1) (B * N + 4 + r) (isH B N r h) := by
  have := and_res (cs := (List.range r).map (jlit B N h)) (d := 1) (s := 2) (m := B * N + 4 + r) (by
    intro c hc; obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hc
    have hq' := List.mem_range.mp hq
    unfold jlit jW; split
    · exact R3_mono (inp3 (by omega)) (by omega) (by omega) (Nat.le_refl _)
    · exact not_res (inp3 (by omega)))
  simp only [List.length_map, List.length_range] at this
  exact R3_mono this (Nat.le_refl _) (by omega) (Nat.le_refl _)

/-- Every update formula has depth ≤ 34, size ≤ Fz and reads only the IW input wires. -/
def Fz (B N r : Nat) : Nat := B * (2 * (2 * r + 1 + S1 B N) + 1) + 1 + 32 * r + 60

theorem mstep_res (B N r w : Nat) : R3 30 (B * (2 * (2 * r + 1 + S1 B N) + 1) + 1) (IW B N r) (mstep B N r w) := by
  have := or_res (cs := (List.range B).map (fun h => and [isH B N r h, hstep B N h w])) (d := 29)
    (s := 2 * (2 * r + 1 + S1 B N) + 1) (m := IW B N r) (by
      intro c hc; obtain ⟨h, _, rfl⟩ := List.mem_map.mp hc
      have := and_res (cs := [isH B N r h, hstep B N h w]) (d := 28) (s := 2 * r + 1 + S1 B N) (m := IW B N r) (by
        intro c hc
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc
        rcases hc with rfl | rfl
        · exact R3_mono (isH_res B N r h) (by omega) (by omega) (by unfold IW SW; omega)
        · exact R3_mono (hstep_res B N h w) (Nat.le_refl _) (by omega) (by unfold IW SW; omega))
      simpa using this)
  simpa using this

theorem cForms_res (early : Bool) (B N r : Nat) :
    ∀ c ∈ cForms early B N r, R3 34 (Fz B N r) (IW B N r) c := by
  have hM : ∀ i, i < SW B N r → R3 0 1 (IW B N r) (input i) := fun i hi => inp3 (by unfold IW; omega)
  have hpar := hM (B * N) (by unfold SW; omega)
  have hhalt := hM (B * N + 1) (by unfold SW; omega)
  have hrun := hM (B * N + 2) (by unfold SW; omega)
  have hdec := hM (B * N + 3) (by unfold SW; omega)
  have hrst : R3 0 1 (IW B N r) (rstI B N r) := inp3 (by unfold IW; omega)
  have hisH : ∀ h, R3 2 (2 * r + 1) (IW B N r) (isH B N r h) :=
    fun h => R3_mono (isH_res B N r h) (Nat.le_refl _) (Nat.le_refl _) (by unfold IW SW; omega)
  have hcons : R3 1 3 (IW B N r) (consC B N) := by
    have := and_res (cs := [runI B N, haltI B N]) (by
      intro c hc; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc
      rcases hc with rfl | rfl <;> assumption)
    simpa using this
  have hstepC : R3 2 5 (IW B N r) (stepC B N) := by
    have := and_res (cs := [runI B N, not (haltI B N)]) (d := 1) (s := 2) (by
      intro c hc; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc
      rcases hc with rfl | rfl
      · exact R3_mono hrun (by omega) (by omega) (Nat.le_refl _)
      · exact not_res hhalt)
    simpa using this
  have hcore : R3 3 (4 * r + 3) (IW B N r) (coreC early B N r) := by
    unfold coreC lastC; cases early
    · exact R3_mono (hisH _) (by omega) (by omega) (Nat.le_refl _)
    · have := or_res (cs := [parI B N, isH B N r (B - 1)]) (d := 2) (s := 2 * r + 1) (by
        intro c hc; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc
        rcases hc with rfl | rfl
        · exact R3_mono hpar (by omega) (by omega) (Nat.le_refl _)
        · exact hisH _)
      simp only [if_true, List.length_cons, List.length_nil] at this ⊢
      exact R3_mono this (Nat.le_refl _) (by omega) (Nat.le_refl _)
  have hcont : R3 5 (8 * r + 9) (IW B N r) (contC early B N r) := by
    have := and_res (cs := [consC B N, not (coreC early B N r)]) (d := 4) (s := 4 * r + 4) (by
      intro c hc; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc
      rcases hc with rfl | rfl
      · exact R3_mono hcons (by omega) (by omega) (Nat.le_refl _)
      · exact not_res hcore)
    simp only [List.length_cons, List.length_nil] at this
    exact R3_mono this (Nat.le_refl _) (by omega) (Nat.le_refl _)
  have hload : R3 6 (16 * r + 19) (IW B N r) (loadC early B N r) := by
    have := or_res (cs := [rstI B N r, contC early B N r]) (d := 5) (s := 8 * r + 9) (by
      intro c hc; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc
      rcases hc with rfl | rfl
      · exact R3_mono hrst (by omega) (by omega) (Nat.le_refl _)
      · exact hcont)
    simp only [List.length_cons, List.length_nil] at this
    exact R3_mono this (Nat.le_refl _) (by omega) (Nat.le_refl _)
  have hstop : R3 4 (8 * r + 7) (IW B N r) (stopC early B N r) := by
    have := and_res (cs := [consC B N, coreC early B N r]) (d := 3) (s := 4 * r + 3) (by
      intro c hc; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc
      rcases hc with rfl | rfl
      · exact R3_mono hcons (by omega) (by omega) (Nat.le_refl _)
      · exact hcore)
    simp only [List.length_cons, List.length_nil] at this
    exact R3_mono this (Nat.le_refl _) (by omega) (Nat.le_refl _)
  have hms := fun w => mstep_res B N r w
  -- the three rollout-register formulas
  have hreg : ∀ (a : Circ) (w : Nat), R3 0 1 (IW B N r) a → w < SW B N r →
      R3 34 (Fz B N r) (IW B N r) (RolloutExec.mux (loadC early B N r) a (RolloutExec.mux (stepC B N) (mstep B N r w) (input w))) := by
    intro a w ha hw
    have inner := mux3 hstepC (hms w) (hM w hw)
    have outer := mux3 hload ha inner
    exact R3_mono outer (by omega) (by unfold Fz; omega) (by omega)
  intro c hc
  unfold cForms at hc
  simp only [List.mem_append, List.mem_map, List.mem_range, List.mem_cons, List.mem_nil_iff, or_false] at hc
  rcases hc with ⟨w, hw, rfl⟩ | (rfl | rfl | rfl | rfl) | ⟨q, hq, rfl⟩ | ⟨h, hh, rfl⟩
  · exact hreg _ w (inp3 (by unfold IW; omega)) (by unfold SW; omega)
  · exact hreg _ (B * N) (cst3 false (IW B N r)) (by unfold SW; omega)
  · exact hreg _ (B * N + 1) (cst3 false (IW B N r)) (by unfold SW; omega)
  · have h1 := and_res (cs := [runI B N, not (stopC early B N r)]) (d := 5) (s := 8 * r + 8) (by
      intro c hc; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc
      rcases hc with rfl | rfl
      · exact R3_mono hrun (by omega) (by omega) (Nat.le_refl _)
      · exact not_res hstop)
    simp only [List.length_cons, List.length_nil] at h1
    have := mux3 hrst (R3_mono (cst3 (decide (1 ≤ B)) (IW B N r)) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)) h1
    exact R3_mono this (by omega) (by unfold Fz; omega) (by omega)
  · have h1 := and_res (cs := [consC B N, parI B N]) (d := 1) (s := 3) (by
      intro c hc; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc
      rcases hc with rfl | rfl
      · exact hcons
      · exact R3_mono hpar (by omega) (by omega) (Nat.le_refl _))
    have h2 := or_res (cs := [decI B N, and [consC B N, parI B N]]) (d := 2) (s := 7) (by
      intro c hc; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc
      rcases hc with rfl | rfl
      · exact R3_mono hdec (by omega) (by omega) (Nat.le_refl _)
      · simpa using h1)
    simp only [List.length_cons, List.length_nil] at h2
    have := mux3 hrst (cst3 false (IW B N r)) h2
    exact R3_mono this (by omega) (by unfold Fz; omega) (by omega)
  · have hinc : R3 4 (2 * r + 9) (IW B N r) (incB B N q) := by
      have ha := and_res (cs := (List.range q).map (fun t => input (jW B N t))) (d := 0) (s := 1) (m := IW B N r) (by
        intro c hc; obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hc
        have := List.mem_range.mp ht
        exact inp3 (by unfold jW IW SW; omega))
      simp only [List.length_map, List.length_range] at ha
      have := BoardStore.xor2_res' (inp3 (m := IW B N r) (i := jW B N q) (by unfold jW IW SW; omega)) ha
      exact R3_mono this (by omega) (by omega) (by omega)
    have inner := mux3 hcont hinc (inp3 (m := IW B N r) (i := jW B N q) (by unfold jW IW SW; omega))
    have := mux3 hrst (cst3 false (IW B N r)) inner
    exact R3_mono this (by omega) (by unfold Fz; omega) (by omega)
  · have hc1 := and_res (cs := [consC B N, isH B N r h]) (d := 2) (s := 2 * r + 3) (by
      intro c hc; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc
      rcases hc with rfl | rfl
      · exact R3_mono hcons (by omega) (by omega) (Nat.le_refl _)
      · exact R3_mono (hisH h) (Nat.le_refl _) (by omega) (Nat.le_refl _))
    simp only [List.length_cons, List.length_nil] at hc1
    have inner := mux3 hc1 hpar (inp3 (m := IW B N r) (i := oW B N r h) (by unfold oW IW SW; omega))
    have := mux3 hrst (cst3 false (IW B N r)) inner
    exact R3_mono this (by omega) (by unfold Fz; omega) (by omega)

/-! ## A2. Family certificates over (B, N), index width r = rIdx B -/

/-- Input width of one update of the (B, N) controller (registers, reset, board). -/
def shLen (i : Nat × Nat) : Nat := IW i.1 i.2 (rIdx i.1)
def shF (early : Bool) (i : Nat × Nat) : List Circ := cForms early i.1 i.2 (rIdx i.1)
def shN (early : Bool) (i : Nat × Nat) : List Layer := cNet early i.1 i.2 (rIdx i.1)

/-- Leaves: 0 ↦ B, 1 ↦ N, 2 ↦ rIdx N, 3 ↦ r = rIdx B. -/
def leafS : Nat → Nat × Nat → Nat
  | 0, i => i.1
  | 1, i => i.2
  | 2, i => rIdx i.2
  | _, i => rIdx i.1

def vRB {ι : Type} : PE ι := PE.v 3

theorem shLen_pos (i : Nat × Nat) (_hi : restAdm i) : 1 ≤ shLen i := by unfold shLen IW SW; omega

theorem sh_leaves (k : Nat) (i : Nat × Nat) (hi : restAdm i) : leafS k i ≤ shLen i := by
  have hB := Nat.mul_le_mul_left i.1 hi.2
  have hN := Nat.mul_le_mul_right i.2 hi.1
  have hr := rIdx_le hi.2
  unfold shLen IW SW
  match k with
  | 0 => show i.1 ≤ _; omega
  | 1 => show i.2 ≤ _; simp at hN; omega
  | 2 => show rIdx i.2 ≤ _; simp at hN; omega
  | _ + 3 => show rIdx i.1 ≤ _; omega

theorem shF_tsize (early : Bool) (i : Nat × Nat) :
    tsize (shF early i) ≤ SW i.1 i.2 (rIdx i.1) * Fz i.1 i.2 (rIdx i.1) := by
  have h := sum_le_len_mul (cs := shF early i) (S := Fz i.1 i.2 (rIdx i.1))
    (fun c hc => (cForms_res early i.1 i.2 (rIdx i.1) c hc).2.1)
  unfold shF at h ⊢; rw [cForms_length] at h; exact h

def shSizeE {ι : Type} : PE ι :=
  (vB * vN + 4 + vRB + vB) * (vB * (2 * (2 * vRB + 1 + stepZE) + 1) + 1 + 32 * vRB + 60)

/-- AC0 FAMILY CERTIFICATE of the outer controller's update (either schedule): depth ≤ 34,
    input width IW = 2BN + B + r + 5, total size polynomial in IW (uniformly in B and N). -/
theorem sh_ac0 (early : Bool) : AC0Fam restAdm shLen (shF early) 34 := by
  refine ⟨shLen_pos, fun i _ c hc => (cForms_res early i.1 i.2 (rIdx i.1) c hc).1,
    fun i _ c hc => (cForms_res early i.1 i.2 (rIdx i.1) c hc).2.2, ?_⟩
  exact polyIn_mono (fun i _ => shF_tsize early i) (polyE shLen_pos leafS sh_leaves shSizeE _ (fun _ => rfl))

/-- NETWORK FAMILY CERTIFICATE: W = 1 (weights and thresholds in {0,1}), ≤ 70 layers,
    polynomial widths, fan-ins and gate count; the network's outputs are the formulas. -/
theorem sh_net (early : Bool) : NetFam restAdm shLen (shN early) 1 70 := by
  have spec := fun i => compileF_spec (shF early i) (shLen i) 34
    (fun c hc => (cForms_res early i.1 i.2 (rIdx i.1) c hc).2.2) (fun c hc => (cForms_res early i.1 i.2 (rIdx i.1) c hc).1)
  have hT := polyE shLen_pos leafS sh_leaves shSizeE
    (fun i => SW i.1 i.2 (rIdx i.1) * Fz i.1 i.2 (rIdx i.1)) (fun _ => rfl)
  refine ⟨shLen_pos, fun i _ => (spec i).2.2.1, fun i _ => (spec i).2.2.2.1, fun i _ => (spec i).2.2.2.2.1, ?_, ?_⟩
  · obtain ⟨c, k, h⟩ := polyIn_add shLen_pos hT (polyIn_leaf (fun i _ => Nat.le_refl (shLen i)))
    refine ⟨c, k, fun i hi => netBounded_mono (spec i).2.2.2.2.2.1 ?_⟩
    have := shF_tsize early i; have := h i hi; dsimp only at *; unfold tsize at *; omega
  · have h2 := polyIn_add shLen_pos (polyIn_mul (polyIn_const _ _ (2 * 34 + 1)) hT)
      (polyE shLen_pos leafS sh_leaves (vB * vN + 4 + vRB + vB) (fun i => SW i.1 i.2 (rIdx i.1)) (fun _ => rfl))
    refine polyIn_mono (fun i _ => ?_) h2
    have g := (spec i).2.2.2.2.2.2
    have := Nat.mul_le_mul_left (2 * 34 + 1) (shF_tsize early i)
    have hl : (shF early i).length = SW i.1 i.2 (rIdx i.1) := by unfold shF; rw [cForms_length]
    unfold tsize at this; rw [hl] at g
    show gateCount (cNet early i.1 i.2 (rIdx i.1)) ≤ _
    exact Nat.le_trans g (by omega)

/-! ## A6. Exact counts and work -/

theorem sum_plus_two (f : Nat → Nat) : ∀ (j n : Nat),
    ((List.range' j n).map (fun h => f h + 2)).sum = ((List.range' j n).map f).sum + 2 * n
  | j, 0 => by simp
  | j, n + 1 => by
    rw [List.range'_succ, List.map_cons, List.map_cons, List.sum_cons, List.sum_cons, sum_plus_two f (j + 1) n]
    omega

/-- COUNTS, EARLY EXIT (B ≥ 1): with R = number of heads queried (R ≤ B, R = 1 when
    RO_{π₀}(P) = 1), the controller executes 1 reset tick + Σ_{h<R} L_h policy steps that
    are legal simulated moves + R terminal-test steps + R consume ticks (R − 1 of which also
    reload the board for the next head; the last stops) — i.e. 1 + Σ_{h<R} L_h + 2R ticks —
    and then holds.  The padded clock runs 1 + Tmax ticks instead. -/
theorem ee_counts {B : Nat} (hB : 1 ≤ B) {P : List Nat} (hw : Width B P) :
    eeT B P (B - 1) 0 = ((List.range (eeR P (B - 1) 0)).map (fun h => rolloutMoves h P)).sum + 2 * eeR P (B - 1) 0 ∧
    eeR P (B - 1) 0 ≤ B ∧ (rolloutWinner 0 P = true → eeR P (B - 1) 0 = 1) ∧
    eeT B P (B - 1) 0 ≤ Tmax B P.length := by
  refine ⟨by rw [eeT_sum, sum_plus_two, List.range_eq_range'], (ee_spec hB hw).2.2.2.2.2.1, fun h0 => ?_,
    (ee_spec hB hw).2.2.2.2.2.2.1⟩
  obtain ⟨k, hk⟩ : ∃ k, B - 1 = k := ⟨_, rfl⟩
  rw [hk]; cases k with
  | zero => rfl
  | succ k => simp [eeR, h0]

/-- COUNTS, ALL HEADS (move path, B ≥ 1): 1 reset tick + totalRolloutMoves legal moves + B
    terminal tests + B consume ticks = totalRolloutMoves + 2B + 1 controller ticks, then ONE
    readout-network evaluation: totalRolloutMoves + 2B + 2 network evaluations in all
    (phase 6's functional composition counted totalRolloutMoves + 2B + 1: B separate
    resets instead of 1 reset + B consume/reload ticks). -/
theorem ah_counts {B : Nat} (hB : 1 ≤ B) {P : List Nat} (hw : Width B P) :
    1 + ahT P (B - 1) 0 = totalRolloutMoves B P + 2 * B + 1 ∧
    ahT P (B - 1) 0 ≤ Tmax B P.length ∧
    totalRolloutMoves B P ≤ B * (P.length * (2 ^ B - 1)) := by
  refine ⟨by rw [ahT_total hB]; omega, ?_, totalRolloutMoves_le hw⟩
  have := ahT_le B hw (B - 1) 0; unfold Tmax; rw [show B - 1 + 1 = B by omega] at this; exact this

/-- WORK PER TICK: formula-node work tsize(cForms) ≤ SW·Fz; compiled network gates
    ≤ 69·tsize + SW.  Work of a run = (number of ticks) × (work per tick). -/
theorem tick_work (early : Bool) (B N r : Nat) :
    tsize (cForms early B N r) ≤ SW B N r * Fz B N r ∧
    gateCount (cNet early B N r) ≤ (2 * 34 + 1) * tsize (cForms early B N r) + SW B N r := by
  have h := sum_le_len_mul (cs := cForms early B N r) (S := Fz B N r) (fun c hc => (cForms_res early B N r c hc).2.1)
  rw [cForms_length] at h
  refine ⟨h, ?_⟩
  have g := (compileF_spec (cForms early B N r) (IW B N r) 34 (fun c hc => (cForms_res early B N r c hc).2.2)
    (fun c hc => (cForms_res early B N r c hc).1)).2.2.2.2.2.2
  rw [cForms_length] at g; exact g

/-- SEQUENTIAL TIME IS NOT CONSTANT: each update is one AC0 evaluation, but for B = 1 and
    the board of T ones the early-exit controller needs more than T ticks. -/
theorem ticks_unbounded (T : Nat) : ∃ P : List Nat, Width 1 P ∧ T < eeT 1 P 0 0 := by
  refine ⟨List.replicate T 1, fun x hx => by rw [List.eq_of_mem_replicate hx]; decide, ?_⟩
  simp only [eeT]
  rw [rolloutMoves_eq]
  have : rolloutCount 0 (List.replicate T 1) = T := by
    unfold rolloutCount heapCount
    induction T with
    | zero => rfl
    | succ T ih => simp [List.replicate_succ] at ih ⊢; omega
  omega

/-! ## The complete maps are not AC0 (the bypass statement is preserved) -/

theorem nimSum_bits : ∀ y : List Bool, nimSum (y.map (fun b => if b then 1 else 0)) = if par y then 1 else 0
  | [] => rfl
  | b :: y => by
    simp only [List.map_cons, nimSum, par, nimSum_bits y]
    cases b <;> by_cases hp : par y = true <;> simp [hp]

/-- Under ParityNotAC0, no AC0 formula family (any fixed depth, polynomial size) computes the
    complete P/N CLASSIFICATION on all boards — not even on boards of one-bit heaps, where it
    is parity. -/
theorem no_ac0_classifier (hard : ParityNotAC0) (F : Nat → Circ) (d c k : Nat)
    (hd : ∀ m, depth (F m) ≤ d) (hs : ∀ m, size (F m) ≤ c * m ^ k) (hm : ∀ m, maxInput (F m) ≤ m)
    (hcorr : ∀ (m : Nat) (y : List Bool), y.length = m →
      eval (vfun y) (F m) = decide (nimSum (y.map (fun b => if b then 1 else 0)) ≠ 0)) : False := by
  obtain ⟨m0, hm0⟩ := hard d c k
  obtain ⟨y, hy, hne⟩ := hm0 m0 (Nat.le_refl _) (F m0) (hd m0) (hs m0) (hm m0)
  apply hne
  rw [hcorr m0 y (mem_bitvecs_length hy), nimSum_bits]
  cases par y <;> rfl

/-- Under ParityNotAC0 the complete board-to-move map of the implemented all-head controller
    with readout (ahMove) is not computed by any AC0 binary selector family on all width-2
    boards (it equals mhExec, Bypass.no_ac0_mhExec_allBoards). -/
theorem no_ac0_ahMove (hard : ParityNotAC0) (S : Nat → BCirc) (r : Nat → Nat) (d : Nat)
    (hfam : AC0Fam encAdm encLen (fun m => bForms (S m)) d)
    (hidx : ∀ m, 1 ≤ m → (S m).idx.length = r m ∧ (S m).val.length = 2 ∧ m + 1 ≤ 2 ^ r m)
    (hcomp : ∀ m, 1 ≤ m → ∀ P : List Nat, P.length = m + 1 → Width 2 P →
      ParityCircuit.binMove (S m) (m + 1) P = ahMove 2 P) : False :=
  Bypass.no_ac0_mhExec_allBoards hard S r d hfam hidx (fun m hm P hP hw => (hcomp m hm P hP hw).trans (ahMove_eq hw))

/-! ## Further interface statements -/

/-- RESET FROM ARBITRARY BITS lands in a valid encoded state (unused encodings, e.g. head
    indices ≥ B, are never reached afterwards: brun_enc preserves validity). -/
theorem reset_valid (early : Bool) {B N r : Nat} {P : List Nat} (hP : P.length = N) (hwP : Width B P)
    (x : Nat → Bool) : ∃ s, Valid B N r s ∧ cstep early B N r P true x = enc B N r s :=
  ⟨initOS B P, initOS_valid hP hwP, cstep_reset early B N r P x⟩

/-- The all-head move path executed by the THRESHOLD NETWORK (both the controller ticks and
    the readout are network evaluations) equals mhExec. -/
def ahMoveN (B : Nat) (P : List Nat) : Option (Nat × Nat) :=
  netBinSem (mhN (B, P.length)) P.length (rIdx P.length) B
    (obsIn B P.length P (fun h => nimpl false B P.length (rIdx B) P (Tmax B P.length) (fun _ => false) (oW B P.length (rIdx B) h)))

theorem ahMoveN_eq {B : Nat} {P : List Nat} (hw : Width B P) : ahMoveN B P = mhExec B P := by
  unfold ahMoveN; simp only [nimpl_eq]; exact ahMove_eq hw

/-! ## A5/A6. The all-head move path with early stopping (halting loop) -/

/-- ALL-HEAD HALTING LOOP: after the reset, the loop on the run wire stops after exactly
    ahT = totalRolloutMoves + 2B ticks with every outcome stored. -/
theorem ah_loop {B N r : Nat} (hB : 1 ≤ B) (hBr : B ≤ 2 ^ r) {P : List Nat} (hP : P.length = N) (hw : Width B P)
    (x0 : Nat → Bool) :
    (loopRun (cstep false B N r P false) (B * N + 2) (Tmax B N) (cstep false B N r P true x0)).2 = ahT P (B - 1) 0 ∧
    ∀ h, h < B → (loopRun (cstep false B N r P false) (B * N + 2) (Tmax B N) (cstep false B N r P true x0)).1
      (oW B N r h) = rolloutWinner h P := by
  have hinit : initOS B P = ld P 0 false (fun _ => false) := by simp [initOS, ld]; omega
  obtain ⟨h1, h2, h3⟩ := ah_run B P (B - 1) 0 (by omega) false (fun _ => false) (fun h hh => by omega)
  have hle : ahT P (B - 1) 0 ≤ Tmax B N := by
    have := ahT_le B hw (B - 1) 0; unfold Tmax; rw [show B - 1 + 1 = B by omega, hP] at this; exact this
  rw [← hinit] at h1 h2 h3
  rw [cstep_reset, loopRun_spec false hBr hP hw _ _ _ (initOS_valid hP hw) hle h3 h1]
  exact ⟨rfl, fun h hh => by show enc B N r _ (oW B N r h) = _; rw [enc_o _ _ _ _ hh, h2 h hh]⟩

/-- The all-head move with early stopping: halting loop, then the existing readout. -/
def ahMoveL (B : Nat) (P : List Nat) : Option (Nat × Nat) :=
  netBinSem (mhN (B, P.length)) P.length (rIdx P.length) B
    (obsIn B P.length P (fun h => (loopRun (cstep false B P.length (rIdx B) P false) (B * P.length + 2)
      (Tmax B P.length) (cstep false B P.length (rIdx B) P true (fun _ => false))).1 (oW B P.length (rIdx B) h)))

theorem ahMoveL_eq {B : Nat} {P : List Nat} (hw : Width B P) : ahMoveL B P = mhExec B P := by
  have hBr : B ≤ 2 ^ rIdx B := Nat.le_of_lt (rIdx_counter B)
  unfold ahMoveL mhExec
  rw [(mh_semantics rfl hw _).2.1]
  show attainT _ P = netBinSem (mhN (B, P.length)) P.length (rIdx P.length) B _
  rw [(mh_semantics rfl hw _).2.1]
  congr 1
  apply reconstruct_congr
  intro h hh
  rw [outBit_eq hw, (ah_loop (by omega) hBr rfl hw _).2 h hh]

/-- COUNTS OF THE EXECUTED MOVE PATH (B ≥ 1): 1 reset tick + exactly totalRolloutMoves + 2B
    loop ticks (Σ L_h legal moves, B terminal tests, B consume ticks), then one readout. -/
theorem ahL_counts {B N r : Nat} (hB : 1 ≤ B) (hBr : B ≤ 2 ^ r) {P : List Nat} (hP : P.length = N) (hw : Width B P)
    (x0 : Nat → Bool) :
    1 + (loopRun (cstep false B N r P false) (B * N + 2) (Tmax B N) (cstep false B N r P true x0)).2 =
      totalRolloutMoves B P + 2 * B + 1 := by
  rw [(ah_loop hB hBr hP hw x0).1, ahT_total hB]; omega

/-- WORK OF A RUN (formula nodes evaluated, reset tick included): early exit and all heads,
    with the exact tick counts, are bounded by the padded-clock work (1 + Tmax)·SW·Fz. -/
theorem run_work {B N r : Nat} (hB : 1 ≤ B) {P : List Nat} (hP : P.length = N) (hw : Width B P) (early : Bool) :
    (1 + eeT B P (B - 1) 0) * tsize (cForms early B N r) ≤ (1 + Tmax B N) * (SW B N r * Fz B N r) ∧
    (1 + ahT P (B - 1) 0) * tsize (cForms early B N r) ≤ (1 + Tmax B N) * (SW B N r * Fz B N r) := by
  have hT := (tick_work early B N r).1
  have h1 : eeT B P (B - 1) 0 ≤ Tmax B N := by have := (ee_spec hB hw).2.2.2.2.2.2.1; rwa [hP] at this
  have h2 : ahT P (B - 1) 0 ≤ Tmax B N := by
    have := ahT_le B hw (B - 1) 0; unfold Tmax; rw [show B - 1 + 1 = B by omega, hP] at this; exact this
  exact ⟨Nat.mul_le_mul (by omega) hT, Nat.mul_le_mul (by omega) hT⟩

/-! ## Axiom audit -/

#print axioms cForms_length
#print axioms cF_board
#print axioms cF_mid
#print axioms cF_par
#print axioms cF_halt
#print axioms cF_run
#print axioms cF_dec
#print axioms cF_j
#print axioms cF_o
#print axioms z_low
#print axioms z_par
#print axioms z_halt
#print axioms z_run
#print axioms z_dec
#print axioms z_j
#print axioms z_o
#print axioms z_rst
#print axioms z_P
#print axioms eval_isH_bits
#print axioms eval_isH
#print axioms eval_incB
#print axioms eval_hstep
#print axioms eval_mstep
#print axioms ostep_flat
#print axioms enc_low
#print axioms rsBits_board
#print axioms rsBits_par
#print axioms rsBits_halt
#print axioms enc_run
#print axioms enc_dec
#print axioms enc_j
#print axioms enc_o
#print axioms enc_high
#print axioms wire_cases
#print axioms cstep_reset
#print axioms cstep_enc
#print axioms initOS_valid
#print axioms ostep_valid
#print axioms arun_add
#print axioms brun_enc
#print axioms arun_one
#print axioms ostep_hold
#print axioms arun_hold
#print axioms arun_untilHalt
#print axioms roll_phase
#print axioms query_step
#print axioms ee_run
#print axioms eeR_shootout
#print axioms eeR_le
#print axioms eeT_sum
#print axioms eeT_le
#print axioms ee_spec
#print axioms impl_enc
#print axioms nimSum_width0
#print axioms ee_impl
#print axioms ee_impl_padded
#print axioms loopRun_spec
#print axioms ee_loop
#print axioms ah_run
#print axioms ahT_sum
#print axioms ahT_total
#print axioms ahT_le
#print axioms reconstruct_congr
#print axioms ahMove_eq
#print axioms ahSel_wins
#print axioms early_exit_not_move
#print axioms nstep_eq
#print axioms nimpl_eq
#print axioms ee_net
#print axioms and_res
#print axioms or_res
#print axioms R3_mono
#print axioms not_res
#print axioms inp3
#print axioms cst3
#print axioms mux3
#print axioms S1_pos
#print axioms hstep_res
#print axioms isH_res
#print axioms mstep_res
#print axioms cForms_res
#print axioms shLen_pos
#print axioms sh_leaves
#print axioms shF_tsize
#print axioms sh_ac0
#print axioms sh_net
#print axioms sum_plus_two
#print axioms ee_counts
#print axioms ah_counts
#print axioms tick_work
#print axioms ticks_unbounded
#print axioms nimSum_bits
#print axioms no_ac0_classifier
#print axioms no_ac0_ahMove
#print axioms reset_valid
#print axioms ahMoveN_eq
#print axioms ah_loop
#print axioms ahMoveL_eq
#print axioms ahL_counts
#print axioms run_work

end Shootout
end NimAudit
