import Family
import ParityCircuit

/- Phase 6, Priority 1b: the barrier side of the three bypasses.  Written by Claude
   (10 October 2026).  Lean 4.26.0, core/Std only.

   EXTERNAL INPUT.  `ParityNotAC0` is the classical worst-case statement (Furst–Saxe–
   Sipser, Ajtai, Håstad): for each depth d and polynomial size c·m^k, for all large m,
   no formula of depth ≤ d and size ≤ c·m^k reading m inputs computes parity.  It is a
   theorem PARAMETER, never an axiom; Classical.lean derives it from the negligible
   correlation form of Håstad (2014), Corollary 3.2, with the convention adapters.

   PROVED HERE.
   * extraction_enc: the parity extraction of phase 4 needs the selector's behaviour only
     on the encoded boards (2, b₁, …, b_m), B = 2.
   * barrier_core / barrier_fam / barrier_net: under ParityNotAC0 no AC0 formula family
     and no fixed-scale network family (fixed W, constant layers, polynomial widths)
     computes, on every encoded board, a map that plays a winning move there.
   * The COMPLETE multi-head map (rollouts executed by the compiled policy networks, then
     the compiled readout) and the COMPLETE recurrent map (2N+2 threshold-controller
     updates from the initial state) equal decisionMove on every board of width B; hence
     neither is computed by a single-frame AC0 family or network family, even on the
     two-bit encoding family.
   * Why this does not contradict the two-frame AC0 map: on a promised pair (Q, Game.encode y)
     the predecessor Q already carries the parity locally (promised_pred_parity), the
     two-frame network indeed outputs (0, parity y) there, and no AC0 family can produce
     such a promised predecessor from y (no_ac0_predecessor). -/

namespace NimAudit
namespace Barrier

open Game Rollout Prob Attain Recurrent AC0 AC0.Circ CorrBridge AttainCircuit Bridge SelectCircuit
  BinReadout Controller ControllerBits PriorityEncoder ThresholdNet ThresholdInst FiniteNet WholeGame
  Family ParityCircuit

/-- CLASSICAL WORST-CASE PARITY HARDNESS, family form (EXTERNAL HYPOTHESIS). -/
def ParityNotAC0 : Prop := ∀ d c k : Nat, ∃ m0 : Nat, ∀ m, m0 ≤ m → ParityHard d (c * m ^ k) m

/-! ## Extraction from the encoded boards only -/

/-- The selector plays a zero-restoring legal move on every encoded board with m bits. -/
def EncWin (S : BCirc) (m : Nat) : Prop :=
  ∀ y : List Bool, y.length = m → ∃ i v x, binMove S (m + 1) (Game.encode y) = some (i, v) ∧
    (Game.encode y)[i]? = some x ∧ v < x ∧ nimSum ((Game.encode y).set i v) = 0

/-- EXTRACTION ON THE ENCODING FAMILY: same formula, depth, size and inputs as phase 4,
    but assuming correct play only on the encoded boards. -/
theorem extraction_enc {S : BCirc} {m r d s : Nat} (hb : BBound S (m + 1) 2 r d s) (hS : EncWin S m) :
    (∀ y : List Bool, y.length = m → eval (vfun y) (parityFormula S m) = par y) ∧
    depth (parityFormula S m) ≤ d ∧ size (parityFormula S m) ≤ s ∧
    maxInput (parityFormula S m) ≤ m := by
  have hval1 : getC S.val 1 ∈ S.val := getC_mem (by rw [hb.val_len]; decide)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro y hy
    unfold parityFormula
    rw [eval_subst]
    have hz : (fun j => eval (vfun y) (parSubst m j)) = boardBits 2 (Game.encode y) := by
      funext j; exact parSubst_eval hy j
    rw [hz]
    obtain ⟨i, v, x, hmove, hx, hlt, hz0⟩ := hS y hy
    obtain ⟨_, hvp⟩ := winning_move_on_encode y hx hlt hz0
    unfold binMove binReadoutOf at hmove
    split at hmove
    · split at hmove
      · simp only [Option.some.injEq, Prod.mk.injEq] at hmove
        obtain ⟨_, hvdef⟩ := hmove
        rw [hvp] at hvdef
        have hl : (S.val.map (eval (boardBits 2 (Game.encode y)))).length = 2 := by simp [hb.val_len]
        have := low_bit_of_two hl hvdef
        rw [eval_getC, this, par_eq_parity]
      · cases hmove
    · cases hmove
  · unfold parityFormula
    rw [depth_subst_leaf _ (parSubst_leaf m)]
    exact hb.depth_val _ hval1
  · unfold parityFormula
    rw [size_subst_leaf _ (parSubst_leaf m)]
    exact hb.size_val _ hval1
  · exact maxInput_subst_le _ m (parSubst_max m) _

/-- BARRIER, CORE FORM: under ParityNotAC0, no family of binary selectors with BBound of
    fixed depth d and size s m ≤ c·m^k plays winning moves on all encoded boards. -/
theorem barrier_core (hard : ParityNotAC0) (S : Nat → BCirc) (r s : Nat → Nat) (d c k : Nat)
    (hb : ∀ m, 1 ≤ m → BBound (S m) (m + 1) 2 (r m) d (s m))
    (hs : ∀ m, 1 ≤ m → s m ≤ c * m ^ k)
    (hwin : ∀ m, 1 ≤ m → EncWin (S m) m) : False := by
  obtain ⟨m0, hm0⟩ := hard d c k
  have hm : 1 ≤ m0 + 1 := by omega
  obtain ⟨heval, hd, hsz, hmx⟩ := extraction_enc (hb (m0 + 1) hm) (hwin (m0 + 1) hm)
  obtain ⟨y, hy, hne⟩ := hm0 (m0 + 1) (by omega) _ hd (Nat.le_trans hsz (hs _ hm)) hmx
  exact hne (heval y (mem_bitvecs_length hy))

/-! ## From AC0 family certificates to BBound -/

theorem size_le_tsize {c : Circ} {cs : List Circ} (h : c ∈ cs) : size c ≤ tsize cs := by
  unfold tsize
  induction cs with
  | nil => cases h
  | cons a cs ih =>
    simp only [List.map_cons, List.sum_cons]
    rcases List.mem_cons.mp h with rfl | h'
    · omega
    · have := ih h'; omega

theorem bbound_of_forms {S : BCirc} {N B r d s : Nat} (hidx : S.idx.length = r) (hval : S.val.length = B)
    (hw : N ≤ 2 ^ r) (hd : ∀ c ∈ bForms S, depth c ≤ d) (hm : ∀ c ∈ bForms S, maxInput c ≤ B * N)
    (hs : tsize (bForms S) ≤ s) : BBound S N B r d s := by
  have hsz : ∀ c ∈ bForms S, size c ≤ s := fun c hc => Nat.le_trans (size_le_tsize hc) hs
  have m0 : S.valid ∈ bForms S := by simp [bForms]
  have mi : ∀ c ∈ S.idx, c ∈ bForms S := fun c hc => by simp [bForms, hc]
  have mv : ∀ c ∈ S.val, c ∈ bForms S := fun c hc => by simp [bForms, hc]
  exact ⟨hidx, hval, hw, hd _ m0, fun c hc => hd c (mi c hc), fun c hc => hd c (mv c hc), hsz _ m0,
    fun c hc => hsz c (mi c hc), fun c hc => hsz c (mv c hc), hm _ m0, fun c hc => hm c (mi c hc),
    fun c hc => hm c (mv c hc)⟩

theorem bbound_mono {S : BCirc} {N B r d s d' s' : Nat} (h : BBound S N B r d s) (hd : d ≤ d') (hs : s ≤ s') :
    BBound S N B r d' s' :=
  ⟨h.idx_len, h.val_len, h.width, Nat.le_trans h.depth_valid hd, fun c hc => Nat.le_trans (h.depth_idx c hc) hd,
    fun c hc => Nat.le_trans (h.depth_val c hc) hd, Nat.le_trans h.size_valid hs,
    fun c hc => Nat.le_trans (h.size_idx c hc) hs, fun c hc => Nat.le_trans (h.size_val c hc) hs,
    h.max_valid, h.max_idx, h.max_val⟩

/-- The encoding family: m parity bits, m + 1 heaps of 2 bits, input length 2(m+1). -/
def encAdm : Nat → Prop := fun m => 1 ≤ m
def encLen : Nat → Nat := fun m => 2 * (m + 1)

theorem enc_poly {c k m : Nat} (hm : 1 ≤ m) : c * encLen m ^ k ≤ c * 4 ^ k * m ^ k := by
  have h1 : encLen m ≤ 4 * m := by unfold encLen; omega
  have := Nat.pow_le_pow_left h1 k
  rw [Nat.mul_pow] at this
  have := Nat.mul_le_mul_left c this
  rw [Nat.mul_assoc]; exact this

/-- BARRIER FOR AC0 FORMULA FAMILIES on the encoding family. -/
theorem barrier_fam (hard : ParityNotAC0) (S : Nat → BCirc) (r : Nat → Nat) (d : Nat)
    (hfam : AC0Fam encAdm encLen (fun m => bForms (S m)) d)
    (hidx : ∀ m, 1 ≤ m → (S m).idx.length = r m ∧ (S m).val.length = 2 ∧ m + 1 ≤ 2 ^ r m)
    (hwin : ∀ m, 1 ≤ m → EncWin (S m) m) : False := by
  obtain ⟨c, k, hsz⟩ := hfam.size_poly
  apply barrier_core hard S r (fun m => c * encLen m ^ k) d (c * 4 ^ k) k _ (fun m hm => enc_poly hm) hwin
  intro m hm
  exact bbound_of_forms (hidx m hm).1 (hidx m hm).2.1 (hidx m hm).2.2 (hfam.depth_le m hm)
    (fun c' hc => hfam.reads m hm c' hc) (hsz m hm)

/-! ## Maps that win on the encoding family -/

/-- A move map plays a zero-restoring legal move on every encoded board. -/
def WinsOnEnc (F : List Nat → Option (Nat × Nat)) : Prop :=
  ∀ y : List Bool, ∃ i v x, F (Game.encode y) = some (i, v) ∧ (Game.encode y)[i]? = some x ∧ v < x ∧
    nimSum ((Game.encode y).set i v) = 0

theorem decisionMove_winsOnEnc : WinsOnEnc decisionMove := by
  intro y
  obtain ⟨i, v, hd, hz⟩ := (decision_correct (Game.encode y)).2.2 (nimSum_encode_ne y)
  obtain ⟨x, hx, hlt, _⟩ := (decision_correct (Game.encode y)).2.1 i v hd
  exact ⟨i, v, x, hd, hx, hlt, hz⟩

theorem winsOnEnc_congr {F G : List Nat → Option (Nat × Nat)} (h : ∀ y, F (Game.encode y) = G (Game.encode y))
    (hG : WinsOnEnc G) : WinsOnEnc F := by
  intro y; obtain ⟨i, v, x, h1, h2⟩ := hG y; exact ⟨i, v, x, by rw [h y, h1], h2⟩

/-- BARRIER FOR A MAP (formula families): if F wins on the encoding family, no AC0
    family of binary selectors computes F there. -/
theorem barrier_map (hard : ParityNotAC0) (F : List Nat → Option (Nat × Nat)) (hF : WinsOnEnc F)
    (S : Nat → BCirc) (r : Nat → Nat) (d : Nat)
    (hfam : AC0Fam encAdm encLen (fun m => bForms (S m)) d)
    (hidx : ∀ m, 1 ≤ m → (S m).idx.length = r m ∧ (S m).val.length = 2 ∧ m + 1 ≤ 2 ^ r m)
    (hcomp : ∀ m, 1 ≤ m → ∀ y : List Bool, y.length = m → binMove (S m) (m + 1) (Game.encode y) = F (Game.encode y)) :
    False := by
  apply barrier_fam hard S r d hfam hidx
  intro m hm y hy
  obtain ⟨i, v, x, h1, h2⟩ := hF y
  exact ⟨i, v, x, by rw [hcomp m hm y hy, h1], h2⟩

/-! ## Network families -/

theorem binMove_netBCirc {W N r : Nat} (ls : List Layer) (hv : NetValid W ls) {P : List Nat}
    (hP : P.length = N) : binMove (netBCirc W 2 N r ls) N P = netBinSem ls N r 2 (boardBits 2 P) := by
  unfold binMove
  rw [netReadout_eq (fun _ => ls) (fun _ => hv) hP false]
  rfl

/-- BARRIER FOR FIXED-SCALE NETWORK FAMILIES: under ParityNotAC0 no family of W-valid
    networks with at most L layers (W, L fixed) and polynomial widths/fan-ins, decoded as
    (valid, r index bits, 2 value bits), computes on all encoded boards a map that wins
    there.  (The network-to-AC0 compilation is applied to the same networks.) -/
theorem barrier_net (hard : ParityNotAC0) (F : List Nat → Option (Nat × Nat)) (hF : WinsOnEnc F)
    (net : Nat → List Layer) (r : Nat → Nat) (W L : Nat)
    (hnet : NetFam encAdm encLen net W L) (hr : ∀ m, 1 ≤ m → m + 1 ≤ 2 ^ r m)
    (hcomp : ∀ m, 1 ≤ m → ∀ y : List Bool, y.length = m →
      netBinSem (net m) (m + 1) (r m) 2 (boardBits 2 (Game.encode y)) = F (Game.encode y)) : False := by
  obtain ⟨c, k, hbd⟩ := hnet.bounded
  let s : Nat → Nat := fun m => 2 * ((2 * W + 3) ^ L * (c * encLen m ^ k + 1) ^ (W * L))
  have hpoly : PolyIn encAdm (fun m => m) s :=
    polyE (fun m hm => hm) (fun _ m => m) (fun _ _ _ => Nat.le_refl _)
      (2 * (PE.c (2 * W + 3) ^ L * (PE.c c * (2 * (vB + 1)) ^ k + 1) ^ (W * L))) s (fun _ => rfl)
  obtain ⟨c', k', hs⟩ := hpoly
  apply barrier_core hard (fun m => netBCirc W 2 (m + 1) (r m) (net m)) r s (3 * L) c' k' _ hs
  · intro m hm y hy
    obtain ⟨i, v, x, h1, h2⟩ := hF y
    refine ⟨i, v, x, ?_, h2⟩
    rw [binMove_netBCirc (net m) (hnet.valid m hm) (by rw [length_encode, hy]), hcomp m hm y hy, h1]
  · intro m hm
    have hb := netBCirc_BBound (B := 2) (N := m + 1) (r := r m) (net m) (hnet.valid m hm) (hbd m hm) (hr m hm)
    have hl := hnet.layers m hm
    refine bbound_mono hb (Nat.mul_le_mul_left 3 hl) ?_
    have e1 : (2 * W + 3) ^ (net m).length ≤ (2 * W + 3) ^ L := Nat.pow_le_pow_right (by omega) hl
    have e2 : (c * encLen m ^ k + 1) ^ (W * (net m).length) ≤ (c * encLen m ^ k + 1) ^ (W * L) :=
      Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_left W hl)
    have := Nat.mul_le_mul e1 e2
    show 2 * ((2 * W + 3) ^ (net m).length * (c * encLen m ^ k + 1) ^ (W * (net m).length)) ≤ s m
    simp only [s]; omega

/-! ## The complete multi-head and recurrent decision maps -/

/-- The COMPLETE multi-head decision map: B rollouts executed by the compiled policy
    networks (sequential), their outcome parities, then the compiled readout network. -/
def mhMove (B : Nat) (P : List Nat) : Option (Nat × Nat) :=
  netBinSem (mhNet B P.length (rIdx P.length)) P.length (rIdx P.length) B
    (obsIn B P.length P (fun j => rollOut B j P))

theorem mhMove_eq {B : Nat} {P : List Nat} (hw : Width B P) : mhMove B P = decisionMove P := by
  have ho : (fun j => rollOut B j P) = outcomes P := by funext j; exact rollOut_eq hw
  unfold mhMove; rw [ho]
  exact mhNet_correct (rIdx_width _) rfl hw

/-- The COMPLETE recurrent decision map: 2N + 2 threshold-controller updates from the
    initial state on rows, SEP, rows, SEP. -/
def recMove (B : Nat) (P : List Nat) : Option (Nat × Nat) :=
  (WholeGame.decide B (rIdx P.length) (sbits B (rIdx P.length) cinit) P).2

theorem cinit_fits (B N : Nat) : Fits B N cinit :=
  ⟨Nat.two_pow_pos B, Nat.two_pow_pos B, Nat.two_pow_pos B, Nat.zero_le _, by simp [cinit], by simp [cinit]⟩

theorem recMove_eq {B : Nat} {P : List Nat} (hw : Width B P) : recMove B P = decisionMove P := by
  unfold recMove
  rw [(decide_spec (rIdx_counter P.length) cinit_idle (cinit_fits B P.length) rfl hw).1]

theorem width2_encode (y : List Bool) : Width 2 (Game.encode y) := encode_width y

theorem mhMove_winsOnEnc : WinsOnEnc (mhMove 2) :=
  winsOnEnc_congr (fun y => mhMove_eq (width2_encode y)) decisionMove_winsOnEnc

theorem recMove_winsOnEnc : WinsOnEnc (recMove 2) :=
  winsOnEnc_congr (fun y => recMove_eq (width2_encode y)) decisionMove_winsOnEnc

/-- MULTI-HEAD BARRIER: under ParityNotAC0 the complete multi-head decision map is not
    computed by any single-frame AC0 formula family, even on the two-bit encoding family. -/
theorem no_ac0_mh (hard : ParityNotAC0) (S : Nat → BCirc) (r : Nat → Nat) (d : Nat)
    (hfam : AC0Fam encAdm encLen (fun m => bForms (S m)) d)
    (hidx : ∀ m, 1 ≤ m → (S m).idx.length = r m ∧ (S m).val.length = 2 ∧ m + 1 ≤ 2 ^ r m)
    (hcomp : ∀ m, 1 ≤ m → ∀ y : List Bool, y.length = m → binMove (S m) (m + 1) (Game.encode y) = mhMove 2 (Game.encode y)) :
    False :=
  barrier_map hard _ mhMove_winsOnEnc S r d hfam hidx hcomp

/-- RECURRENT BARRIER (formula families). -/
theorem no_ac0_rec (hard : ParityNotAC0) (S : Nat → BCirc) (r : Nat → Nat) (d : Nat)
    (hfam : AC0Fam encAdm encLen (fun m => bForms (S m)) d)
    (hidx : ∀ m, 1 ≤ m → (S m).idx.length = r m ∧ (S m).val.length = 2 ∧ m + 1 ≤ 2 ^ r m)
    (hcomp : ∀ m, 1 ≤ m → ∀ y : List Bool, y.length = m → binMove (S m) (m + 1) (Game.encode y) = recMove 2 (Game.encode y)) :
    False :=
  barrier_map hard _ recMove_winsOnEnc S r d hfam hidx hcomp

/-- Network forms of both barriers. -/
theorem no_net_mh (hard : ParityNotAC0) (net : Nat → List Layer) (r : Nat → Nat) (W L : Nat)
    (hnet : NetFam encAdm encLen net W L) (hr : ∀ m, 1 ≤ m → m + 1 ≤ 2 ^ r m)
    (hcomp : ∀ m, 1 ≤ m → ∀ y : List Bool, y.length = m →
      netBinSem (net m) (m + 1) (r m) 2 (boardBits 2 (Game.encode y)) = mhMove 2 (Game.encode y)) : False :=
  barrier_net hard _ mhMove_winsOnEnc net r W L hnet hr hcomp

theorem no_net_rec (hard : ParityNotAC0) (net : Nat → List Layer) (r : Nat → Nat) (W L : Nat)
    (hnet : NetFam encAdm encLen net W L) (hr : ∀ m, 1 ≤ m → m + 1 ≤ 2 ^ r m)
    (hcomp : ∀ m, 1 ≤ m → ∀ y : List Bool, y.length = m →
      netBinSem (net m) (m + 1) (r m) 2 (boardBits 2 (Game.encode y)) = recMove 2 (Game.encode y)) : False :=
  barrier_net hard _ recMove_winsOnEnc net r W L hnet hr hcomp

/-- "On all boards" corollary: agreement on all width-2 boards implies agreement on the
    encoded boards, so the barrier applies a fortiori. -/
theorem no_ac0_mh_allBoards (hard : ParityNotAC0) (S : Nat → BCirc) (r : Nat → Nat) (d : Nat)
    (hfam : AC0Fam encAdm encLen (fun m => bForms (S m)) d)
    (hidx : ∀ m, 1 ≤ m → (S m).idx.length = r m ∧ (S m).val.length = 2 ∧ m + 1 ≤ 2 ^ r m)
    (hcomp : ∀ m, 1 ≤ m → ∀ P : List Nat, P.length = m + 1 → Width 2 P → binMove (S m) (m + 1) P = mhMove 2 P) :
    False :=
  no_ac0_mh hard S r d hfam hidx (fun m hm y hy => hcomp m hm _ (by rw [length_encode, hy]) (width2_encode y))

theorem no_ac0_rec_allBoards (hard : ParityNotAC0) (S : Nat → BCirc) (r : Nat → Nat) (d : Nat)
    (hfam : AC0Fam encAdm encLen (fun m => bForms (S m)) d)
    (hidx : ∀ m, 1 ≤ m → (S m).idx.length = r m ∧ (S m).val.length = 2 ∧ m + 1 ≤ 2 ^ r m)
    (hcomp : ∀ m, 1 ≤ m → ∀ P : List Nat, P.length = m + 1 → Width 2 P → binMove (S m) (m + 1) P = recMove 2 P) :
    False :=
  no_ac0_rec hard S r d hfam hidx (fun m hm y hy => hcomp m hm _ (by rw [length_encode, hy]) (width2_encode y))

/-! ## Why the promised two-frame map is not a counterexample -/

/-- OR over heaps of the low bit of Q_i ⊕ P_i (a depth-4 local test on a pair). -/
def lowXorOr (Q P : List Nat) : Bool :=
  (List.range P.length).any (fun i => ((Q.getD i 0) ^^^ (P.getD i 0)).testBit 0)

theorem move_split {Q P : List Nat} (h : Move Q P) :
    ∃ pre x post z, Q = pre ++ x :: post ∧ P = pre ++ z :: post ∧ z < x := by
  obtain ⟨pre, x, post, z, h1, h2, h3⟩ := h; exact ⟨pre, x, post, z, h1, h2, h3⟩

theorem getD_split' (pre post : List Nat) (x i : Nat) :
    (pre ++ x :: post).getD i 0 = if i = pre.length then x else (pre ++ 0 :: post).getD i 0 := by
  by_cases hi : i = pre.length
  · subst hi; simp
  · rw [if_neg hi]
    simp only [List.getD_eq_getElem?_getD]
    rcases Nat.lt_or_ge i pre.length with h | h
    · rw [List.getElem?_append_left h, List.getElem?_append_left h]
    · rw [List.getElem?_append_right h, List.getElem?_append_right h]
      have : i - pre.length ≠ 0 := by omega
      obtain ⟨k, hk⟩ : ∃ k, i - pre.length = k + 1 := ⟨i - pre.length - 1, by omega⟩
      rw [hk]; simp

/-- PROMISED PREDECESSORS REVEAL PARITY LOCALLY: if nim(Q) = 0 and Q → Game.encode y is a
    legal move, then the pair-local test lowXorOr Q (Game.encode y) equals parity y. -/
theorem promised_pred_parity (y : List Bool) {Q : List Nat} (h0 : nimSum Q = 0) (hm : Move Q (Game.encode y)) :
    lowXorOr Q (Game.encode y) = parity y := by
  obtain ⟨pre, x, post, z, hQ, hP, _⟩ := move_split hm
  have hd : x ^^^ z = 2 ^^^ (parity y).toNat := by
    have e := one_heap_difference pre post x z
    rw [← hQ, ← hP, h0, Nat.zero_xor, nimSum_encode] at e
    exact e.symm
  have hlow : (x ^^^ z).testBit 0 = parity y := by
    rw [hd]; cases parity y <;> decide
  have hlen : (Game.encode y).length = pre.length + 1 + post.length := by rw [hP]; simp; omega
  unfold lowXorOr
  apply Bool.eq_iff_iff.mpr
  rw [List.any_eq_true]
  constructor
  · rintro ⟨i, _, hi⟩
    rw [hQ, hP, getD_split', getD_split' pre post z] at hi
    by_cases hc : i = pre.length
    · rw [if_pos hc, if_pos hc, hlow] at hi; exact hi
    · rw [if_neg hc, if_neg hc, Nat.xor_self] at hi; simp at hi
  · intro hpar
    refine ⟨pre.length, List.mem_range.mpr (by omega), ?_⟩
    rw [hQ, hP, getD_split', getD_split' pre post z, if_pos rfl, if_pos rfl, hlow, hpar]

/-- The local test as a formula over the predecessor's formulas G (bit wire 2i+1 is the
    low bit of heap i in the two-bit layout) and the inputs y. -/
def lowEnc (i : Nat) : Circ := if i = 0 then const false else input (i - 1)

def predParity (G : List Circ) (m : Nat) : Circ :=
  or ((List.range (m + 1)).map (fun i => xor2 (getC G (2 * i + 1)) (lowEnc i)))

theorem lowEnc_eval {y : List Bool} {i : Nat} (hi : i < y.length + 1) :
    eval (vfun y) (lowEnc i) = ((Game.encode y).getD i 0).testBit 0 := by
  unfold lowEnc Game.encode
  by_cases h0 : i = 0
  · subst h0; simp
  · rw [if_neg h0]
    obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
    simp only [eval_input, Nat.add_sub_cancel, List.getD_cons_succ, vfun]
    have hk : k < y.length := by omega
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD (l := List.map Bool.toNat y), List.getElem?_map,
      List.getElem?_eq_getElem hk]
    cases y[k] <;> simp

/-- NO AC0 FAMILY PRODUCES PROMISED PREDECESSORS: under ParityNotAC0 there is no AC0
    family G m (input: the m bits y; outputs: the 2(m+1) bits of a board Q) such that, for
    every y, Q is a predecessor of Game.encode y with nim(Q) = 0 reached by a legal move.  The
    two-frame selector is AC0 only because this promised frame is SUPPLIED. -/
theorem no_ac0_predecessor (hard : ParityNotAC0) (G : Nat → List Circ) (d : Nat)
    (hfam : AC0Fam encAdm (fun m => m) G d)
    (hpred : ∀ m, 1 ≤ m → ∀ y : List Bool, y.length = m → ∃ Q : List Nat, Q.length = m + 1 ∧
      nimSum Q = 0 ∧ Move Q (Game.encode y) ∧ ∀ w, w < 2 * (m + 1) → eval (vfun y) (getC (G m) w) = boardBits 2 Q w) :
    False := by
  have hp : ∀ m, encAdm m → 1 ≤ m := fun m hm => hm
  have hT : PolyIn encAdm (fun m => m) (fun m => tsize (G m)) := hfam.size_poly
  have hP : PolyIn encAdm (fun m => m) (fun m => (m + 1) * (2 * (tsize (G m) + 1) + 7) + 1) :=
    polyIn_add hp (polyIn_mul (polyIn_add hp (polyIn_leaf (fun _ _ => Nat.le_refl _)) (polyIn_const _ _ 1))
      (polyIn_add hp (polyIn_mul (polyIn_const _ _ 2) (polyIn_add hp hT (polyIn_const _ _ 1))) (polyIn_const _ _ 7)))
      (polyIn_const _ _ 1)
  obtain ⟨c, k, hsz⟩ := hP
  obtain ⟨m0, hm0⟩ := hard (d + 4) c k
  have hm : 1 ≤ m0 + 1 := by omega
  -- the parity formula computes parity on every y of length m0 + 1
  have heval : ∀ y : List Bool, y.length = m0 + 1 → eval (vfun y) (predParity (G (m0 + 1)) (m0 + 1)) = par y := by
    intro y hy
    obtain ⟨Q, hQl, h0, hmv, hbits⟩ := hpred (m0 + 1) hm y hy
    rw [par_eq_parity, ← promised_pred_parity y h0 hmv]
    unfold predParity lowXorOr
    simp only [eval_or, List.any_map, length_encode, hy]
    apply any_congr_mem
    intro i hi
    have hi' := List.mem_range.mp hi
    simp only [Function.comp_apply, eval_xor2]
    have hw := hbits (2 * i + 1) (by omega)
    rw [hw, lowEnc_eval (by omega)]
    unfold boardBits
    rw [hQl, if_pos (by omega)]
    have e1 : (2 * i + 1) / 2 = i := by omega
    have e2 : 2 - 1 - (2 * i + 1) % 2 = 0 := by omega
    rw [e1, e2, Nat.testBit_xor]
  -- resources of the parity formula
  have hget : ∀ w, depth (getC (G (m0 + 1)) w) ≤ d ∧ maxInput (getC (G (m0 + 1)) w) ≤ m0 + 1 ∧
      size (getC (G (m0 + 1)) w) ≤ tsize (G (m0 + 1)) + 1 := by
    intro w; unfold getC; rw [List.getD_eq_getElem?_getD]
    cases h : (G (m0 + 1))[w]? with
    | none => simp
    | some c' =>
      have hmem := List.mem_of_getElem? h
      exact ⟨hfam.depth_le _ hm c' hmem, hfam.reads _ hm c' hmem, Nat.le_succ_of_le (size_le_tsize hmem)⟩
  have hlow : ∀ i, i ≤ m0 + 1 → depth (lowEnc i) = 0 ∧ size (lowEnc i) = 1 ∧ maxInput (lowEnc i) ≤ m0 + 1 := by
    intro i hi; unfold lowEnc; split <;> simp <;> omega
  have hx : ∀ i, i ≤ m0 + 1 → depth (xor2 (getC (G (m0 + 1)) (2 * i + 1)) (lowEnc i)) ≤ d + 3 ∧
      size (xor2 (getC (G (m0 + 1)) (2 * i + 1)) (lowEnc i)) ≤ 2 * (tsize (G (m0 + 1)) + 1) + 7 ∧
      maxInput (xor2 (getC (G (m0 + 1)) (2 * i + 1)) (lowEnc i)) ≤ m0 + 1 := by
    intro i hi
    obtain ⟨a1, a2, a3⟩ := hget (2 * i + 1)
    obtain ⟨b1, b2, b3⟩ := hlow i hi
    simp only [xor2, depth_or, depth_and, depth_not, size_or, size_and, size_not, maxInput_or, maxInput_and,
      maxInput_not, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, b1, b2]
    simp only [listMax, List.foldr]
    refine ⟨by omega, by omega, by omega⟩
  have hd : depth (predParity (G (m0 + 1)) (m0 + 1)) ≤ d + 4 := by
    unfold predParity
    apply depth_or_le; intro c' hc'
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hc'
    exact (hx i (by have := List.mem_range.mp hi; omega)).1
  have hmx : maxInput (predParity (G (m0 + 1)) (m0 + 1)) ≤ m0 + 1 := by
    unfold predParity
    apply ControllerBits.maxInput_or_le; intro c' hc'
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hc'
    exact (hx i (by have := List.mem_range.mp hi; omega)).2.2
  have hs : size (predParity (G (m0 + 1)) (m0 + 1)) ≤ c * (m0 + 1) ^ k := by
    unfold predParity
    rw [size_or]
    have h1 := sum_le_len_mul (cs := (List.range (m0 + 1 + 1)).map
      (fun i => xor2 (getC (G (m0 + 1)) (2 * i + 1)) (lowEnc i))) (S := 2 * (tsize (G (m0 + 1)) + 1) + 7)
      (fun c' hc' => by
        obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hc'
        exact (hx i (by have := List.mem_range.mp hi; omega)).2.1)
    rw [List.length_map, List.length_range] at h1
    have h2 := hsz (m0 + 1) hm
    dsimp only at h2
    omega
  obtain ⟨y, hy, hne⟩ := hm0 (m0 + 1) (by omega) _ hd hs hmx
  exact hne (heval y (mem_bitvecs_length hy))

/-- On a promised pair (Q, Game.encode y) the two-frame network outputs heap 0 and the parity
    of y: the two-frame AC0 map does compute parity there, from the supplied frame Q. -/
theorem twoFrame_on_encoding (y : List Bool) {Q : List Nat} (hQ : Q.length = y.length + 1) (hw : Width 2 Q)
    (h0 : nimSum Q = 0) (hm : Move Q (Game.encode y)) :
    netBinSem (restN (2, y.length + 1)) (y.length + 1) (rIdx (y.length + 1)) 2
      (LocalRestore.tf 2 (y.length + 1) Q (Game.encode y)) = some (0, (parity y).toNat) := by
  obtain ⟨i, v, _, h2, _, h4, h5⟩ := rest_semantics (B := 2) hQ (by rw [length_encode]) hw (width2_encode y) h0 hm
  have hred := unique_zero_move y _ h4 h5
  cases i with
  | zero =>
    have := congrArg List.head? hred
    simp [Game.encode, reduced] at this
    rw [this] at h2; exact h2
  | succ k =>
    exfalso
    have := congrArg List.head? hred
    simp [Game.encode, reduced] at this
    have h2le := Bool.toNat_le (parity y)
    omega

/-! ## Axiom audit -/

#print axioms extraction_enc
#print axioms barrier_core
#print axioms size_le_tsize
#print axioms bbound_of_forms
#print axioms bbound_mono
#print axioms enc_poly
#print axioms barrier_fam
#print axioms decisionMove_winsOnEnc
#print axioms winsOnEnc_congr
#print axioms barrier_map
#print axioms binMove_netBCirc
#print axioms barrier_net
#print axioms mhMove_eq
#print axioms cinit_fits
#print axioms recMove_eq
#print axioms width2_encode
#print axioms mhMove_winsOnEnc
#print axioms recMove_winsOnEnc
#print axioms no_ac0_mh
#print axioms no_ac0_rec
#print axioms no_net_mh
#print axioms no_net_rec
#print axioms no_ac0_mh_allBoards
#print axioms no_ac0_rec_allBoards
#print axioms move_split
#print axioms getD_split'
#print axioms promised_pred_parity
#print axioms lowEnc_eval
#print axioms no_ac0_predecessor
#print axioms twoFrame_on_encoding


