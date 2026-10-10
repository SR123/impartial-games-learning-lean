import ThresholdNet
import PriorityEncoder

/- Phase 5, task 2 (instances): the threshold-network compiler applied to the
   recurrent controller's per-update circuits and to the binary selectors.
   Written by Claude (10 October 2026).  Lean 4.26.0, core/Std only.

   * THRESHOLD UPDATE.  One fixed-scale network (W = 1) computes all
     4 + 5B + 3r next-state bits and all 4 + 3B + r output bits of the controller
     from the 6 + 6B + 3r input wires (state wires, row flag, reset flag, row value).
     `tstep_eq`: the threshold update equals the bit-level update `bstep` for EVERY
     state vector and token, so run refinement, reset from arbitrary bit states,
     the stream/game theorems and the register bounds transfer verbatim.
   * BINARY SELECTORS AS NETWORKS.  Any binary readout (valid, r index bits, B value
     bits) compiles to a network whose output wires 0, 1..r, r+1..r+B decode to the same
     move; instantiated for attainability, local restoration, π_j and multi-head. -/

namespace NimAudit
namespace ThresholdInst

open Game Rollout Prob Attain Recurrent AC0 AC0.Circ CorrBridge AttainCircuit Bridge SelectCircuit
  BinReadout Controller ControllerBits PriorityEncoder ThresholdNet FiniteNet

/-! ## The controller's output wires in a fixed order -/

/-- Output wire j: 0 summary flag; 1..B summary bits; B+1..2B difference bits;
    2B+1 difference-valid; 2B+2 move flag; 2B+3 move-valid; 2B+4.. index bits (r);
    2B+4+r.. move value bits (B). -/
def outAt (B r j : Nat) : Circ :=
  if j = 0 then sumOutC B r
  else if j < 1 + B then sumBitC (j - 1)
  else if j < 1 + 2 * B then diffBitC B (j - (1 + B))
  else if j = 1 + 2 * B then ControllerBits.diffValidC B
  else if j = 2 + 2 * B then moveOutC B r
  else if j = 3 + 2 * B then moveValidC B r
  else if j < 4 + 2 * B + r then moveIC B r (j - (4 + 2 * B))
  else if j < 4 + 3 * B + r then moveVC B r (j - (4 + 2 * B + r))
  else const false

def outCount (B r : Nat) : Nat := 4 + 3 * B + r
def inWidth (B r : Nat) : Nat := 6 + 6 * B + 3 * r

/-- Decoding the output wires into a controller output (bit reading only). -/
def outDecode (B r : Nat) (w : Nat → Bool) : Option COut :=
  if w 0 then
    some (COut.summary (ofBits B (fun k => w (1 + k)))
      (if w (1 + 2 * B) then some (ofBits B (fun k => w (1 + B + k))) else none))
  else if w (2 + 2 * B) then
    some (COut.move (if w (3 + 2 * B) then
      some (ofBits r (fun q => w (4 + 2 * B + q)), ofBits B (fun k => w (4 + 2 * B + r + k))) else none))
  else none

theorem ofBits_congr (B : Nat) (f g : Nat → Bool) (h : ∀ k < B, f k = g k) : ofBits B f = ofBits B g := by
  induction B with
  | zero => rfl
  | succ B ih =>
    simp only [ofBits]
    rw [h B (by omega), ih (fun k hk => h k (by omega))]

theorem outDecode_congr (B r : Nat) (w w' : Nat → Bool) (h : ∀ k < outCount B r, w k = w' k) :
    outDecode B r w = outDecode B r w' := by
  unfold outCount at h
  unfold outDecode
  rw [h 0 (by omega), h (1 + 2 * B) (by omega), h (2 + 2 * B) (by omega), h (3 + 2 * B) (by omega),
    ofBits_congr B (fun k => w (1 + k)) (fun k => w' (1 + k)) (fun k hk => h _ (by omega)),
    ofBits_congr B (fun k => w (1 + B + k)) (fun k => w' (1 + B + k)) (fun k hk => h _ (by omega)),
    ofBits_congr r (fun q => w (4 + 2 * B + q)) (fun q => w' (4 + 2 * B + q)) (fun q hq => h _ (by omega)),
    ofBits_congr B (fun k => w (4 + 2 * B + r + k)) (fun k => w' (4 + 2 * B + r + k)) (fun k hk => h _ (by omega))]

theorem outDecode_eval (B r : Nat) (z : Nat → Bool) :
    outDecode B r (fun j => eval z (outAt B r j)) = decodeOut B r z := by
  unfold outDecode decodeOut
  have e0 : outAt B r 0 = sumOutC B r := by simp [outAt]
  have e1 : outAt B r (1 + 2 * B) = ControllerBits.diffValidC B := by
    simp (disch := omega) only [outAt, if_neg, if_pos, ↓reduceIte]
  have e2 : outAt B r (2 + 2 * B) = moveOutC B r := by
    simp (disch := omega) only [outAt, if_neg, if_pos, ↓reduceIte]
  have e3 : outAt B r (3 + 2 * B) = moveValidC B r := by
    simp (disch := omega) only [outAt, if_neg, if_pos, ↓reduceIte]
  have hs : ofBits B (fun k => eval z (outAt B r (1 + k))) = ofBits B (fun k => eval z (sumBitC k)) :=
    ofBits_congr _ _ _ (fun k hk => by
      simp (disch := omega) only [outAt, if_neg, if_pos]; congr 2; omega)
  have hd : ofBits B (fun k => eval z (outAt B r (1 + B + k))) = ofBits B (fun k => eval z (diffBitC B k)) :=
    ofBits_congr _ _ _ (fun k hk => by
      simp (disch := omega) only [outAt, if_neg, if_pos]; congr 2; omega)
  have hi : ofBits r (fun q => eval z (outAt B r (4 + 2 * B + q))) = ofBits r (fun q => eval z (moveIC B r q)) :=
    ofBits_congr _ _ _ (fun q hq => by
      simp (disch := omega) only [outAt, if_neg, if_pos]; congr 2; omega)
  have hv : ofBits B (fun k => eval z (outAt B r (4 + 2 * B + r + k))) =
      ofBits B (fun k => eval z (moveVC B r k)) :=
    ofBits_congr _ _ _ (fun k hk => by
      simp (disch := omega) only [outAt, if_neg, if_pos]; congr 2; omega)
  simp only [e0, e1, e2, e3, hs, hd, hi, hv]

theorem outAt_res (B r j : Nat) (hj : j < outCount B r) :
    size (outAt B r j) ≤ 16 ∧ depth (outAt B r j) ≤ 3 ∧ maxInput (outAt B r j) ≤ inWidth B r := by
  unfold outCount at hj
  unfold outAt inWidth
  by_cases h0 : j = 0
  · rw [if_pos h0]; simp [sumOutC, Ec, Mc, listMax]; omega
  by_cases h1 : j < 1 + B
  · rw [if_neg h0, if_pos h1]; simp [sumBitC]; omega
  by_cases h2 : j < 1 + 2 * B
  · rw [if_neg h0, if_neg h1, if_pos h2]; simp [diffBitC, xor2, listMax]; omega
  by_cases h3 : j = 1 + 2 * B
  · rw [if_neg h0, if_neg h1, if_neg h2, if_pos h3]; simp [ControllerBits.diffValidC]; omega
  by_cases h4 : j = 2 + 2 * B
  · rw [if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_pos h4]; simp [moveOutC, Ec, Mc, listMax]; omega
  by_cases h5 : j = 3 + 2 * B
  · rw [if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_pos h5]; simp [moveValidC, listMax]; omega
  by_cases h6 : j < 4 + 2 * B + r
  · rw [if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_pos h6]
    simp [moveIC, mux, listMax]; omega
  have h7 : j < 4 + 3 * B + r := by omega
  rw [if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_neg h6, if_pos h7]
  simp [moveVC, mux, listMax]; omega

/-! ## The threshold update -/

/-- All formulas of one controller update: next-state wires, then output wires. -/
def ctrlForms (B r : Nat) : List Circ :=
  (List.range (stateWidth B r + outCount B r)).map
    (fun k => if k < stateWidth B r then nextC B r k else outAt B r (k - stateWidth B r))

/-- THE CONTROLLER'S FIXED-SCALE THRESHOLD NETWORK. -/
def ctrlNet (B r : Nat) : List Layer := compileF (ctrlForms B r)

/-- One update of the threshold-network controller. -/
def tstep (B r : Nat) (v : Nat → Bool) (t : Tok) : (Nat → Bool) × Option COut :=
  ((fun j => if j < stateWidth B r then evalNet (ctrlNet B r) (inp B r v t) j else false),
   outDecode B r (fun k => evalNet (ctrlNet B r) (inp B r v t) (stateWidth B r + k)))

theorem ctrlForms_get (B r k : Nat) (hk : k < (ctrlForms B r).length) :
    (ctrlForms B r)[k] = if k < stateWidth B r then nextC B r k else outAt B r (k - stateWidth B r) := by
  simp [ctrlForms]

theorem ctrlForms_length (B r : Nat) : (ctrlForms B r).length = stateWidth B r + outCount B r := by
  simp [ctrlForms]

/-- THRESHOLD REFINEMENT: the network update equals the bit-level update for every
    state vector and every token. -/
theorem tstep_eq (B r : Nat) (v : Nat → Bool) (t : Tok) : tstep B r v t = bstep B r v t := by
  unfold tstep bstep
  congr 1
  · funext j
    by_cases hj : j < stateWidth B r
    · rw [if_pos hj, ctrlNet, compileF_eval (ctrlForms B r) _ (by rw [ctrlForms_length]; omega),
        ctrlForms_get, if_pos hj]
    · rw [if_neg hj, nextC_beyond B r j (by omega)]; simp
  · rw [outDecode_congr B r _ (fun j => eval (inp B r v t) (outAt B r j)) (fun k hk => by
      rw [ctrlNet, compileF_eval (ctrlForms B r) _ (by rw [ctrlForms_length]; omega), ctrlForms_get,
        if_neg (by omega), Nat.add_sub_cancel_left])]
    exact outDecode_eval B r _

/-- Runs of the threshold controller. -/
def trun (B r : Nat) : (Nat → Bool) → List Tok → (Nat → Bool) × List COut
  | v, [] => (v, [])
  | v, t :: ts => ((trun B r (tstep B r v t).1 ts).1, (tstep B r v t).2.toList ++ (trun B r (tstep B r v t).1 ts).2)

theorem trun_eq (B r : Nat) : ∀ (v : Nat → Bool) (ts : List Tok), trun B r v ts = brun B r v ts
  | _, [] => rfl
  | v, t :: ts => by simp only [trun, brun, tstep_eq, trun_eq B r _ ts]

theorem trun_append (B r : Nat) (v : Nat → Bool) (ts us : List Tok) :
    trun B r v (ts ++ us) =
      ((trun B r (trun B r v ts).1 us).1, (trun B r v ts).2 ++ (trun B r (trun B r v ts).1 us).2) := by
  simp only [trun_eq]; exact brun_append B r v ts us

/-- RUN REFINEMENT (threshold level): from the canonical encoding of a semantic state,
    the threshold controller tracks the semantic controller along every run satisfying
    the width side conditions. -/
theorem trun_refines {B r : Nat} (s : CState) (ts : List Tok) (h : AllDec B r s ts) :
    trun B r (sbits B r s) ts = (sbits B r (crun s ts).1, (crun s ts).2) := by
  rw [trun_eq]; exact brun_refines s ts h

/-- STREAM THEOREM (threshold level). -/
theorem trun_stream {B r N : Nat} (hN : N < 2 ^ r) (Ps : List (List Nat))
    (hP : ∀ P ∈ Ps, P.length = N ∧ Width B P) :
    (trun B r (sbits B r cinit) (stream Ps)).2 = ctrlOuts false 0 Ps := by
  rw [trun_eq]; exact bits_stream hN Ps hP

/-- RESET FROM ARBITRARY BIT STATES and GAMES (threshold level). -/
theorem tstep_reset (B r : Nat) (v : Nat → Bool) : tstep B r v Tok.reset = (sbits B r cinit, none) := by
  rw [tstep_eq]; exact bstep_reset B r v

theorem trun_games (B r : Nat) (v : Nat → Bool) (gs : List (List (List Nat)))
    (h : ∀ g ∈ gs, ∃ N, N < 2 ^ r ∧ ∀ P ∈ g, P.length = N ∧ Width B P) :
    (trun B r v (gameStream gs)).2 = gs.flatMap (ctrlOuts false 0) := by
  rw [trun_eq]; exact bits_games B r v gs h

theorem crunStates_prefix : ∀ (s : CState) (ts us : List Tok), ∀ st ∈ crunStates s ts,
    st ∈ crunStates s (ts ++ us)
  | s, [], us, st, h => by simp [crunStates] at h; subst h; exact self_mem_crunStates st us
  | s, t :: ts, us, st, h => by
    simp only [crunStates, List.mem_cons] at h
    simp only [List.cons_append, crunStates, List.mem_cons]
    rcases h with rfl | h
    · left; rfl
    · right; exact crunStates_prefix _ ts us st h

/-- WIDTH PRESERVATION and LOSSLESS STATE (threshold level): after EVERY prefix of a
    well-formed stream, the threshold controller's state vector is the canonical encoding
    of a reachable semantic state whose registers fit (counter included, no overflow) and
    which is recovered exactly from the vector. -/
theorem trun_states_fit {B r N : Nat} (hN : N < 2 ^ r) (Ps : List (List Nat))
    (hP : ∀ P ∈ Ps, P.length = N ∧ Width B P) : ∀ k, ∃ st ∈ crunStates cinit (stream Ps),
      (trun B r (sbits B r cinit) ((stream Ps).take k)).1 = sbits B r st ∧
      FitsR B r st ∧ decodeS B r (sbits B r st) = st := by
  intro k
  have hfit0 : Fits B N cinit :=
    ⟨Nat.two_pow_pos B, Nat.two_pow_pos B, Nat.two_pow_pos B, Nat.zero_le _, by simp [cinit], by simp [cinit]⟩
  have hfits := stream_fits cinit cinit_idle hfit0 Ps hP
  have e := List.take_append_drop k (stream Ps)
  have hpre : ∀ st ∈ crunStates cinit ((stream Ps).take k), st ∈ crunStates cinit (stream Ps) := by
    intro st h
    have := crunStates_prefix cinit _ ((stream Ps).drop k) st h
    rwa [e] at this
  have hall : AllDec B r cinit ((stream Ps).take k) :=
    allDec_of_fits hN cinit _ (fun st h => hfits st (hpre st h))
      (fun t ht => tok_bound_stream Ps (fun P h => (hP P h).2) t (List.mem_of_mem_take ht))
  have hmem := hpre _ (crun_mem_states cinit ((stream Ps).take k))
  refine ⟨(crun cinit ((stream Ps).take k)).1, hmem, ?_, reachable_lossless hN Ps hP _ hmem⟩
  rw [trun_refines _ _ hall]

theorem trun_one_board {B r : Nat} (P : List Nat) (hN : P.length < 2 ^ r) (hw : Width B P) :
    (trun B r (sbits B r cinit) (dtoks P)).2 = [COut.summary (nimSum P) none, COut.move (decisionMove P)] := by
  rw [trun_eq]; exact bits_one_board P hN hw

/-! ## Resources of the controller network -/

theorem ctrlForms_res (B r : Nat) :
    ∀ c ∈ ctrlForms B r, depth c ≤ 8 ∧ size c ≤ cellSize B r + 16 ∧ maxInput c ≤ inWidth B r := by
  intro c hc
  simp only [ctrlForms, List.mem_map, List.mem_range] at hc
  obtain ⟨k, hk, rfl⟩ := hc
  by_cases hs : k < stateWidth B r
  · rw [if_pos hs]
    obtain ⟨a, b, d⟩ := nextC_resources B r k
    exact ⟨b, by omega, by unfold inWidth; omega⟩
  · rw [if_neg hs]
    obtain ⟨a, b, d⟩ := outAt_res B r (k - stateWidth B r) (by omega)
    exact ⟨by omega, by omega, d⟩

theorem ctrlForms_size (B r : Nat) :
    ((ctrlForms B r).map size).sum ≤ (stateWidth B r + outCount B r) * (cellSize B r + 16) := by
  have := sum_le_len_mul (cs := ctrlForms B r) (S := cellSize B r + 16) (fun c hc => (ctrlForms_res B r c hc).2.1)
  rwa [ctrlForms_length] at this

/-- CONTROLLER NETWORK RESOURCES: W = 1, wired at the input width 6 + 6B + 3r, at most
    18 layers, layer widths and fan-ins ≤ S + 6 + 6B + 3r with
    S ≤ (8 + 8B + 4r)(2B² + 8B + 2r + 57), and at most 17·S + 8 + 8B + 4r gates. -/
theorem ctrlNet_res (B r : Nat) :
    NetValid 1 (ctrlNet B r) ∧ Wired (inWidth B r) (ctrlNet B r) ∧ (ctrlNet B r).length ≤ 18 ∧
    NetBounded (((ctrlForms B r).map size).sum + inWidth B r) (ctrlNet B r) ∧
    gateCount (ctrlNet B r) ≤ 17 * ((ctrlForms B r).map size).sum + (stateWidth B r + outCount B r) ∧
    ((ctrlForms B r).map size).sum ≤ (stateWidth B r + outCount B r) * (cellSize B r + 16) := by
  unfold ctrlNet
  obtain ⟨_, _, h3, h4, h5, h6, h7⟩ := compileF_spec (ctrlForms B r) (inWidth B r) 8
    (fun c hc => (ctrlForms_res B r c hc).2.2) (fun c hc => (ctrlForms_res B r c hc).1)
  rw [ctrlForms_length] at h7
  exact ⟨h3, h4, by omega, h6, h7, ctrlForms_size B r⟩

/-- Memory and update counts are those of the bit-level controller: 4 + 5B + 3r state
    bits (7 + 5B + 3·log₂N with r = log₂N + 1), 2N + 2 network updates per decision,
    one extra update per reset token. -/
theorem ctrl_counts (B N : Nat) (P : List Nat) :
    stateWidth B (N.log2 + 1) = 7 + 5 * B + 3 * N.log2 ∧ N < 2 ^ (N.log2 + 1) ∧
    (dtoks P).length = 2 * P.length + 2 :=
  ⟨(counter_width (B := B) N).2, (counter_width (B := B) N).1, dtoks_length P⟩

/-! ## Summary-only corollary -/

/-- The summary mechanism's formulas: mode, acc (B), prev (B), valid, and the summary
    outputs (flag, B summary bits, B difference bits, difference-valid). -/
def summaryForms (B r : Nat) : List Circ :=
  [modeN B r] ++ (List.range B).map (accN B r) ++ (List.range B).map (prevN B r) ++ [validN B r] ++
    [sumOutC B r] ++ (List.range B).map sumBitC ++ (List.range B).map (diffBitC B) ++ [ControllerBits.diffValidC B]

theorem summaryForms_res (B r : Nat) :
    ∀ c ∈ summaryForms B r, depth c ≤ 8 ∧ size c ≤ 35 ∧ maxInput c ≤ inWidth B r := by
  intro c hc
  simp only [summaryForms, List.mem_append, List.mem_cons, List.mem_map, List.mem_range, List.not_mem_nil,
    or_false] at hc
  unfold inWidth
  rcases hc with ((((((rfl | ⟨k, hk, rfl⟩) | ⟨k, hk, rfl⟩) | rfl) | rfl) | ⟨k, hk, rfl⟩) | ⟨k, hk, rfl⟩) | rfl
  · refine ⟨?_, by have := (summary_resources B r 0).1; omega, ?_⟩ <;> simp [modeN, Rc, Wc, Ec, Mc, listMax] <;> omega
  · refine ⟨?_, by have := (summary_resources B r k).2.1; omega, ?_⟩ <;> simp [accN, Rc, Wc, Ec, Mc, xI, xor2, listMax] <;> omega
  · refine ⟨?_, by have := (summary_resources B r k).2.2.1; omega, ?_⟩ <;> simp [prevN, mux, Rc, Wc, Ec, Mc, listMax] <;> omega
  · refine ⟨?_, by have := (summary_resources B r 0).2.2.2; omega, ?_⟩ <;> simp [validN, Rc, Wc, Ec, Mc, listMax] <;> omega
  · refine ⟨?_, ?_, ?_⟩ <;> simp [sumOutC, Ec, Mc, listMax] <;> omega
  · refine ⟨?_, ?_, ?_⟩ <;> simp [sumBitC] <;> omega
  · refine ⟨?_, ?_, ?_⟩ <;> simp [diffBitC, xor2, listMax] <;> omega
  · refine ⟨?_, ?_, ?_⟩ <;> simp [ControllerBits.diffValidC] <;> omega

theorem summaryForms_length (B r : Nat) : (summaryForms B r).length = 4 + 4 * B := by
  simp [summaryForms]; omega

/-- SUMMARY-ONLY NETWORK: the summary registers' updates and summary outputs are computed
    by a W = 1 network with at most 18 layers and at most 17·35·(4+4B) + 4 + 4B gates,
    i.e. O(B) gates (the replay part is what adds the B² and log N terms). -/
theorem summaryNet_res (B r : Nat) :
    (∀ x : Nat → Bool, ∀ k (hk : k < (summaryForms B r).length),
      evalNet (compileF (summaryForms B r)) x k = eval x (summaryForms B r)[k]) ∧
    NetValid 1 (compileF (summaryForms B r)) ∧ (compileF (summaryForms B r)).length ≤ 18 ∧
    gateCount (compileF (summaryForms B r)) ≤ 17 * (35 * (4 + 4 * B)) + (4 + 4 * B) := by
  obtain ⟨h1, _, h3, _, h5, _, h7⟩ := compileF_spec (summaryForms B r) (inWidth B r) 8
    (fun c hc => (summaryForms_res B r c hc).2.2) (fun c hc => (summaryForms_res B r c hc).1)
  have hs := sum_le_len_mul (cs := summaryForms B r) (S := 35) (fun c hc => (summaryForms_res B r c hc).2.1)
  rw [summaryForms_length] at hs h7
  refine ⟨h1, h3, by omega, ?_⟩
  have : 17 * ((summaryForms B r).map size).sum ≤ 17 * (35 * (4 + 4 * B)) := by
    exact Nat.mul_le_mul_left _ (by rw [Nat.mul_comm]; exact hs)
  omega

/-! ## Binary selectors as threshold networks -/

/-- Output order: wire 0 valid, wires 1..r index bits, wires r+1..r+B value bits. -/
def bForms (S : BCirc) : List Circ := S.valid :: (S.idx ++ S.val)

def binNet (S : BCirc) : List Layer := compileF (bForms S)

/-- Decoding the output wires of a binary-selector network (bit reading only). -/
def netBinSem (net : List Layer) (N r B : Nat) (x : Nat → Bool) : Option (Nat × Nat) :=
  if evalNet net x 0 then
    if toNatBE ((List.range r).map (fun q => evalNet net x (1 + q))) < N then
      some (toNatBE ((List.range r).map (fun q => evalNet net x (1 + q))),
        toNatBE ((List.range B).map (fun k => evalNet net x (1 + r + k))))
    else none
  else none

theorem map_range_eq {r : Nat} (l : List Circ) (hl : l.length = r) (f : Nat → Bool) (x : Nat → Bool)
    (h : ∀ q (hq : q < r), f q = eval x (l[q]'(by omega))) : (List.range r).map f = l.map (eval x) := by
  apply List.ext_getElem (by simp [hl])
  intro n h1 h2
  simp only [List.getElem_map, List.getElem_range]
  exact h n (by simpa using h1)

/-- NETWORK = BINARY SELECTOR, on every input. -/
theorem binNet_correct (S : BCirc) {N r B : Nat} (hr : S.idx.length = r) (hB : S.val.length = B)
    (x : Nat → Bool) : netBinSem (binNet S) N r B x = binSem S N x := by
  have hlen : (bForms S).length = 1 + r + B := by simp [bForms, hr, hB]; omega
  have h0 : evalNet (binNet S) x 0 = eval x S.valid := by
    rw [binNet, compileF_eval _ _ (by omega)]; rfl
  have hi : (List.range r).map (fun q => evalNet (binNet S) x (1 + q)) = S.idx.map (eval x) := by
    apply map_range_eq S.idx hr
    intro q hq
    rw [binNet, compileF_eval _ _ (by omega)]
    have e : (bForms S)[1 + q]? = S.idx[q]? := by
      simp [bForms, show 1 + q = q + 1 by omega, List.getElem?_append_left (show q < S.idx.length by omega)]
    rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega)] at e
    rw [Option.some.inj e]
  have hv : (List.range B).map (fun k => evalNet (binNet S) x (1 + r + k)) = S.val.map (eval x) := by
    apply map_range_eq S.val hB
    intro k hk
    rw [binNet, compileF_eval _ _ (by omega)]
    have e : (bForms S)[1 + r + k]? = S.val[k]? := by
      simp [bForms, show 1 + r + k = (r + k) + 1 by omega,
        List.getElem?_append_right (show S.idx.length ≤ r + k by omega), hr]
    rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega)] at e
    rw [Option.some.inj e]
  unfold netBinSem binSem
  rw [h0, hi, hv]

/-- NETWORK RESOURCES of a compiled binary selector. -/
theorem binNet_res {S : BCirc} {N B r D Sz M : Nat} (h : BinBound S N B r D Sz M) :
    NetValid 1 (binNet S) ∧ Wired M (binNet S) ∧ (binNet S).length ≤ 2 * D + 2 ∧
    NetBounded ((1 + r + B) * Sz + M) (binNet S) ∧
    gateCount (binNet S) ≤ (2 * D + 1) * ((1 + r + B) * Sz) + (1 + r + B) := by
  unfold binNet
  have hall : ∀ c ∈ bForms S, depth c ≤ D ∧ size c ≤ Sz ∧ maxInput c ≤ M := fun c hc => h.all c hc
  have hlen : (bForms S).length = 1 + r + B := by simp [bForms, h.idx_len, h.val_len]; omega
  obtain ⟨_, _, h3, h4, h5, h6, h7⟩ := compileF_spec (bForms S) M D (fun c hc => (hall c hc).2.2)
    (fun c hc => (hall c hc).1)
  have hs := sum_le_len_mul (cs := bForms S) (S := Sz) (fun c hc => (hall c hc).2.1)
  rw [hlen] at hs h7
  refine ⟨h3, h4, h5, ?_, ?_⟩
  · intro l hl
    obtain ⟨a, b⟩ := h6 l hl
    exact ⟨by omega, fun g hg => by have := b g hg; omega⟩
  · have : (2 * D + 1) * ((bForms S).map size).sum ≤ (2 * D + 1) * ((1 + r + B) * Sz) :=
      Nat.mul_le_mul_left _ hs
    omega

/-- Local restoration as a fixed-scale network on the two frames. -/
def restNet (B N r : Nat) : List Layer := binNet (restBin B N r)

theorem restNet_correct {B N r : Nat} (hr : N ≤ 2 ^ r) {Q Q' : List Nat} (hQ : Q.length = N)
    (hQ' : Q'.length = N) (hw : Width B Q) (hw' : Width B Q') (h0 : nimSum Q = 0) (hm : Move Q Q') :
    ∃ i v, netBinSem (restNet B N r) N r B (LocalRestore.tf B N Q Q') = some (i, v) ∧
      restore Q Q' = some (Q'.set i v) ∧ Move Q' (Q'.set i v) ∧ nimSum (Q'.set i v) = 0 := by
  have hb := restBin_bound (B := B) (N := N) hr
  rw [restNet, binNet_correct _ hb.idx_len hb.val_len]
  exact restBin_correct hr hQ hQ' hw hw' h0 hm

theorem restNet_res {B N r : Nat} (hr : N ≤ 2 ^ r) :
    NetValid 1 (restNet B N r) ∧ Wired (2 * (B * N)) (restNet B N r) ∧ (restNet B N r).length ≤ 2 * 20 + 2 :=
  let h := binNet_res (restBin_bound (B := B) (N := N) hr)
  ⟨h.1, h.2.1, h.2.2.1⟩

/-- The multi-head selector as a fixed-scale network on board and outcome wires. -/
def mhNet (B N r : Nat) : List Layer := binNet (mhBin B N r)

theorem mhNet_correct {B N r : Nat} (hr : N ≤ 2 ^ r) {P : List Nat} (hP : P.length = N) (hw : Width B P) :
    netBinSem (mhNet B N r) N r B (obsIn B N P (outcomes P)) = decisionMove P := by
  have hb := mhBin_bound (B := B) (N := N) hr
  rw [mhNet, binNet_correct _ hb.idx_len hb.val_len]
  exact mhBin_outcomes hr hP hw

theorem mhNet_res {B N r : Nat} (hr : N ≤ 2 ^ r) :
    NetValid 1 (mhNet B N r) ∧ Wired (B * N + B) (mhNet B N r) ∧ (mhNet B N r).length ≤ 2 * 19 + 2 :=
  let h := binNet_res (mhBin_bound (B := B) (N := N) hr)
  ⟨h.1, h.2.1, h.2.2.1⟩

/-- The π_j policy step as a fixed-scale network on the board wires. -/
def polNet (B N j r : Nat) : List Layer := binNet (polBin B N j r)

theorem polNet_correct {B N j r : Nat} (hr : N ≤ 2 ^ r) {P : List Nat} (hP : P.length = N) (hw : Width B P) :
    applyM P (netBinSem (polNet B N j r) N r B (boardBits B P)) = policyStep j P := by
  have hb := polBin_bound (B := B) (N := N) (j := j) hr
  rw [polNet, binNet_correct _ hb.idx_len hb.val_len]
  exact (polBin_correct hr hP hw).2

theorem polNet_res {B N j r : Nat} (hr : N ≤ 2 ^ r) :
    NetValid 1 (polNet B N j r) ∧ Wired (B * N) (polNet B N j r) ∧ (polNet B N j r).length ≤ 2 * 17 + 2 :=
  let h := binNet_res (polBin_bound (B := B) (N := N) (j := j) hr)
  ⟨h.1, h.2.1, h.2.2.1⟩

/-- Attainability as fixed-scale networks: exact success 2/(2^B − 1) retained. -/
def attainNet (B N r a0 a1 : Nat) (b : Bool) : List Layer := binNet (attainBin B N r a0 a1 b)

theorem attainNet_correct {B N r a0 a1 : Nat} (h0 : a0 ≠ 0) (h1 : a1 ≠ 0) (hl0 : a0 < 2 ^ B)
    (hl1 : a1 < 2 ^ B) (hr : N ≤ 2 ^ r) {P : List Nat} (hP : P.length = N) (hw : Width B P) (b : Bool) :
    netBinSem (attainNet B N r a0 a1 b) N r B (boardBits B P) = attainF a0 a1 P b := by
  have hb := attainBin_bound h0 h1 hl0 hl1 hr b
  rw [attainNet, binNet_correct _ hb.idx_len hb.val_len, ← binReadoutOf_eq]
  exact attainBin_correct h0 h1 hl0 hl1 hr hP hw b


/-! ## Axiom audit -/

#print axioms ofBits_congr
#print axioms outDecode_congr
#print axioms outDecode_eval
#print axioms outAt_res
#print axioms ctrlForms_get
#print axioms ctrlForms_length
#print axioms tstep_eq
#print axioms trun_eq
#print axioms trun_append
#print axioms trun_refines
#print axioms trun_stream
#print axioms tstep_reset
#print axioms trun_games
#print axioms crunStates_prefix
#print axioms trun_states_fit
#print axioms trun_one_board
#print axioms ctrlForms_res
#print axioms ctrlForms_size
#print axioms ctrlNet_res
#print axioms ctrl_counts
#print axioms summaryForms_res
#print axioms summaryForms_length
#print axioms summaryNet_res
#print axioms map_range_eq
#print axioms binNet_correct
#print axioms binNet_res
#print axioms restNet_correct
#print axioms restNet_res
#print axioms mhNet_correct
#print axioms mhNet_res
#print axioms polNet_correct
#print axioms polNet_res
#print axioms attainNet_correct
end ThresholdInst
end NimAudit
