import Bypass

/- Phase 6, Priority 3d: remaining paper-specific mathematical statements.  Written by
   Claude (10 October 2026).  Lean 4.26.0, core/Std only.

   A. Appendix app:weak (pairing strategy) and Definition def:mastery (weak mastery):
      on paired boards the second player answers every legal move by copying it on the
      partner heap; the reply is computed by a binary selector built from LOCAL two-heap
      comparisons (no nim-sum); it wins against every opponent (SecondWins, hence Lose
      for the player to move, hence nim-sum 0).
   B. The finite-state shootout controller (Figure fig:fsm-shootout-controller): generic
      finite-state controllers over rollout heads; the depicted controller outputs the OR
      of the queried channel bits, which for the exact structured heads is (nim(P) ≠ 0),
      using 1 + (index of the first 1) ≤ B queries.
   C. The single-head baseline numbers: among nonzero nim-sums of B bits exactly 2^{B−1}
      are detected by the r₀ classifier; for B = 4 this is 8 of 15 and the balanced
      accuracy is 23/30; with uniform boards the board-level recall is the same ratio.
   D. Remark rem:noisy-rollout-decay: for independent Bernoulli(ε) flips E₁..E_L,
      Pr[Y ⊕ E₁ ⊕ … ⊕ E_L = Y] = (1 + (1 − 2ε)^L)/2 (exact finite probability model); for
      ε = 1/100, L = 50 the value lies in [0.682, 0.6822].  (No claim is made about
      erroneous game moves or learned heads.)
   E. Section sec:spectral-view: characters are orthonormal on {0,1}^n (char_orth), i.e.
      the Fourier coefficient of PARITY_S at T is 1 if T = S and 0 otherwise; nim-sum bit j
      is the parity of a mask with exactly N ones (a degree-N character); a single-heap
      change makes each delta bit a two-coordinate character.  (No Fourier-tail theorem
      for AC0 is stated: Linial–Mansour–Nisan stays external and unused.)
   F. The initialisation boundary (Section sec:search-gap): the completed matching-delta
      policy plays (2) → (1) → (0) and loses from the winning position (2).
   G. Proposition prop:single-policy-bound: a one-heap modification shifts the channel
      bit by the known correction ℓ_j(h ⊕ h'). -/

namespace NimAudit
namespace Misc

attribute [local simp] Rat.add_zero Rat.zero_add Rat.mul_one Rat.one_mul Rat.mul_zero Rat.zero_mul

open Game Rollout Prob Attain Recurrent AC0 AC0.Circ CorrBridge AttainCircuit Bridge SelectCircuit
  BinReadout Controller ControllerBits PriorityEncoder ThresholdNet ThresholdInst FiniteNet WholeGame
  Family

/-! ## A. Pairing strategy and weak mastery -/

/-- Partner of heap k in the pairs (0,1), (2,3), … -/
def partner (k : Nat) : Nat := if k % 2 = 0 then k + 1 else k - 1

theorem partner_partner (k : Nat) : partner (partner k) = k := by unfold partner; split <;> split <;> omega
theorem partner_ne (k : Nat) : partner k ≠ k := by unfold partner; split <;> omega
theorem partner_lt {k N : Nat} (hk : k < N) (hN : N % 2 = 0) : partner k < N := by unfold partner; split <;> omega

/-- Paired boards (a, a, b, b, …). -/
def Paired (P : List Nat) : Prop := P.length % 2 = 0 ∧ ∀ k, k < P.length → P.getD k 0 = P.getD (partner k) 0

/-- Second-player guarantee for a reply rule: every legal opponent move is answered
    legally and the guarantee persists (weak mastery for the second-player role). -/
inductive SecondWins (sel : List Nat → Option (List Nat)) : List Nat → Prop
  | intro (P : List Nat) :
      (∀ Q, Move P Q → (sel Q).isSome = true) →
      (∀ Q R, Move P Q → sel Q = some R → Move Q R) →
      (∀ Q R, Move P Q → sel Q = some R → SecondWins sel R) → SecondWins sel P

theorem secondWins_sound {sel : List Nat → Option (List Nat)} {P : List Nat} (h : SecondWins sel P) : Lose P := by
  induction h with
  | intro P hsome hmove _ ih =>
    refine Lose.intro P (fun Q hm => ?_)
    cases hr : sel Q with
    | none => have := hsome Q hm; rw [hr] at this; cases this
    | some R => exact Win.intro Q R (hmove Q R hm hr) (ih Q R hm hr)

theorem getD_set_ne' (P : List Nat) {i k : Nat} (v : Nat) (h : k ≠ i) : (P.set i v).getD k 0 = P.getD k 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_set, Ne.symm h]

theorem getD_set_eq' (P : List Nat) {i : Nat} (v : Nat) (h : i < P.length) : (P.set i v).getD i 0 = v := by
  simp [List.getD_eq_getElem?_getD, h]

/-- After one legal move from a paired board, exactly one heap is larger than its partner:
    the partner j of the changed heap i; the mirror reply sets heap j to the new value. -/
theorem paired_move {P Q : List Nat} (hp : Paired P) (hm : Move P Q) :
    ∃ i y, i < P.length ∧ Q = P.set i y ∧ y < P.getD i 0 ∧ Q.length = P.length ∧
      (∀ k, k < Q.length → (Q.getD (partner k) 0 < Q.getD k 0 ↔ k = partner i)) ∧
      Paired (Q.set (partner i) y) ∧ Move Q (Q.set (partner i) y) := by
  obtain ⟨pre, x, post, y, hP, hQ, hlt⟩ := hm
  let i := pre.length
  have hi : i < P.length := by rw [hP]; simp [i]
  have hPi : P.getD i 0 = x := by rw [hP]; simp [i]
  have hQset : Q = P.set i y := by rw [hQ, hP]; simp [i]
  have hQl : Q.length = P.length := by rw [hQset]; simp
  have hNe := hp.1
  have hj : partner i < P.length := partner_lt hi hNe
  have hQi : Q.getD i 0 = y := by rw [hQset]; exact getD_set_eq' P y hi
  have hQj : Q.getD (partner i) 0 = x := by
    rw [hQset, getD_set_ne' P y (partner_ne i), ← hp.2 i hi, hPi]
  refine ⟨i, y, hi, hQset, by rw [hPi]; exact hlt, hQl, fun k hk => ?_, ⟨?_, fun k hk => ?_⟩, ?_⟩
  · constructor
    · intro h
      by_cases hki : k = i
      · subst hki; rw [hQi, hQj] at h; omega
      · by_cases hkj : k = partner i
        · exact hkj
        · exfalso
          have hpk : partner k ≠ i := fun e => hkj (by rw [← e, partner_partner])
          rw [hQset, getD_set_ne' P y hpk, getD_set_ne' P y hki, ← hp.2 k (by omega)] at h
          omega
    · intro h; subst h; rw [partner_partner, hQi, hQj]; exact hlt
  · simp [hQl, hNe]
  · simp only [List.length_set] at hk
    by_cases hk1 : k = partner i
    · subst hk1; rw [partner_partner, getD_set_eq' Q y (by omega), getD_set_ne' Q y (Ne.symm (partner_ne i)), hQi]
    · by_cases hk2 : k = i
      · subst hk2; rw [getD_set_ne' Q y (Ne.symm (partner_ne _)), hQi, getD_set_eq' Q y (by omega)]
      · have hpk : partner k ≠ partner i := fun e => hk2 (by rw [← partner_partner k, e, partner_partner])
        have hpk2 : partner k ≠ i := fun e => hk1 (by rw [← e, partner_partner])
        rw [getD_set_ne' Q y hk1, getD_set_ne' Q y hpk, hQset, getD_set_ne' P y hk2, getD_set_ne' P y hpk2]
        exact hp.2 k (by omega)
  · apply set_move (x := x)
    · rw [List.getElem?_eq_getElem (by omega)]
      have := hQj; rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)] at this
      simpa using this
    · exact hlt

/-! ### The local mirror circuit -/

/-- Comparison formulas: heap partner(k) < heap k (both big-endian B-bit blocks). -/
def cmpR (B k : Nat) : RCirc := ⟨const true, [], (List.range B).map (fun p => heapC B (partner k) p)⟩
def flagC (B k : Nat) : Circ := ltC (cmpR B k) B k

/-- The mirror selector: flag k = (partner k < k); the value is the flagged heap's partner. -/
def pairR (B N : Nat) : RCirc :=
  ⟨or ((List.range N).map (flagC B)), (List.range N).map (flagC B),
   (List.range B).map (fun p => or ((List.range N).map (fun k => and [flagC B k, heapC B (partner k) p])))⟩

/-- The binary mirror selector and the reply rule it defines. -/
def pairBin (B N r : Nat) : BCirc := encode (pairR B N) N r
def pairSel (B : Nat) (Q : List Nat) : Option (List Nat) :=
  applyM Q (binSem (pairBin B Q.length (rIdx Q.length)) Q.length (boardBits B Q))

theorem toNatBE_heap {B N : Nat} {Q : List Nat} (hQ : Q.length = N) (hw : Width B Q) {k : Nat} (hk : k < N) :
    toNatBE ((List.range B).map (fun p => boardBits B Q (B * k + p))) = Q.getD k 0 := by
  have hlt : Q.getD k 0 < 2 ^ B := by
    apply hw; rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; simp
  rw [toNatBE_eq_iff _ (by simpa using hlt)]
  intro q hq
  simp only [List.length_map, List.length_range] at hq ⊢
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hq]
  simp only [Option.map_some, Option.getD_some]
  exact boardBits_heap hQ hk hq

theorem flagC_eval {B N : Nat} {Q : List Nat} (hQ : Q.length = N) (hw : Width B Q) (hN : N % 2 = 0)
    {k : Nat} (hk : k < N) : eval (boardBits B Q) (flagC B k) = decide (Q.getD (partner k) 0 < Q.getD k 0) := by
  unfold flagC
  rw [ltC_eval hQ hw (by simp [cmpR]) hk]
  congr 2
  simp only [cmpR, List.map_map, Function.comp_def, heapC, eval_input]
  exact toNatBE_heap hQ hw (partner_lt hk hN)

/-- MIRROR CIRCUIT CORRECTNESS: after a legal move from a paired board, the selector
    outputs (partner of the changed heap, new value). -/
theorem pairR_correct {B : Nat} {P Q : List Nat} (hp : Paired P) (hw : Width B P) (hm : Move P Q) :
    ∃ i y, Q = P.set i y ∧ selReadout (pairR B Q.length) (boardBits B Q) = some (partner i, y) ∧
      Paired (Q.set (partner i) y) ∧ Move Q (Q.set (partner i) y) := by
  obtain ⟨i, y, hi, hQ, hy, hQl, hflag, hpair, hmv⟩ := paired_move hp hm
  refine ⟨i, y, hQ, ?_, hpair, hmv⟩
  have hN : Q.length % 2 = 0 := by rw [hQl]; exact hp.1
  have hwQ : Width B Q := width_move hw (by
    obtain ⟨pre, x, post, z, h1, h2, h3⟩ := hm; exact ⟨pre, x, post, z, h1, h2, h3⟩)
  have hj : partner i < Q.length := by rw [hQl]; exact partner_lt hi hp.1
  have hfl : ∀ k, k < Q.length → eval (boardBits B Q) (flagC B k) = decide (k = partner i) := by
    intro k hk; rw [flagC_eval rfl hwQ hN hk]; exact decide_eq_decide.mpr (hflag k hk)
  unfold selReadout pairR
  simp only
  have hvalid : eval (boardBits B Q) (or ((List.range Q.length).map (flagC B))) = true := by
    rw [eval_or, List.any_eq_true]
    exact ⟨flagC B (partner i), List.mem_map.mpr ⟨_, List.mem_range.mpr hj, rfl⟩, by rw [hfl _ hj]; simp⟩
  rw [if_pos hvalid]
  have hft : firstTrue (((List.range Q.length).map (flagC B)).map (eval (boardBits B Q))) = some (partner i) := by
    rw [firstTrue_some_iff]
    simp only [List.map_map, List.length_map, List.length_range]
    refine ⟨hj, ?_, fun i' hi' => ?_⟩
    · rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj]
      simp [hfl _ hj]
    · rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by omega)]
      simp [hfl _ (by omega : i' < Q.length)]; omega
  rw [hft]
  simp only [Option.some.injEq, Prod.mk.injEq, true_and]
  -- the value bits are the bits of heap i (the flagged heap's partner)
  have hval : ((List.range B).map (fun p => or ((List.range Q.length).map
      (fun k => and [flagC B k, heapC B (partner k) p])))).map (eval (boardBits B Q)) =
      (List.range B).map (fun p => boardBits B Q (B * i + p)) := by
    simp only [List.map_map]
    apply List.map_congr_left
    intro p hp
    simp only [Function.comp_apply, eval_or, List.any_map]
    apply Bool.eq_iff_iff.mpr
    rw [List.any_eq_true]
    constructor
    · rintro ⟨k, hk, he⟩
      have hk' := List.mem_range.mp hk
      simp only [Function.comp_apply, eval_and, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
        hfl k hk', decide_eq_true_eq, heapC, eval_input] at he
      obtain ⟨rfl, h2⟩ := he
      rw [partner_partner] at h2; exact h2
    · intro h
      refine ⟨partner i, List.mem_range.mpr hj, ?_⟩
      simp only [Function.comp_apply, eval_and, List.all_cons, List.all_nil, Bool.and_true, hfl _ hj, decide_true,
        Bool.true_and, heapC, eval_input, partner_partner]
      exact h
  rw [hval, toNatBE_heap rfl hwQ (by omega)]
  rw [hQ, getD_set_eq' P y hi]

/-- PAIRING STRATEGY (weak mastery for the second player): from every paired board of
    width B, the reply rule computed by the local binary mirror circuit wins against every
    legal opponent. -/
theorem pairing_wins {B : Nat} : ∀ P : List Nat, Paired P → Width B P → SecondWins (pairSel B) P := by
  intro P
  induction P using (measure List.sum).wf.induction with
  | h P ih =>
    intro hp hw
    have key : ∀ Q, Move P Q → ∃ i y, pairSel B Q = some (Q.set (partner i) y) ∧
        Paired (Q.set (partner i) y) ∧ Move Q (Q.set (partner i) y) := by
      intro Q hm
      obtain ⟨i, y, _, hsel, hpair, hmv⟩ := pairR_correct hp hw hm
      refine ⟨i, y, ?_, hpair, hmv⟩
      unfold pairSel
      rw [pairBin, encode_correct _ Q.length _ (by simp [pairR]) (rIdx_width _), hsel]; rfl
    refine SecondWins.intro P (fun Q hm => ?_) (fun Q R hm hR => ?_) (fun Q R hm hR => ?_)
    · obtain ⟨i, y, h1, _⟩ := key Q hm; rw [h1]; rfl
    · obtain ⟨i, y, h1, _, h3⟩ := key Q hm; rw [h1] at hR; cases hR; exact h3
    · obtain ⟨i, y, h1, h2, h3⟩ := key Q hm
      rw [h1] at hR; cases hR
      have e1 := move_sum_lt hm; have e2 := move_sum_lt h3
      exact ih _ (by show (Q.set (partner i) y).sum < P.sum; omega) h2 (width_move (width_move hw hm) h3)

theorem paired_lose {B : Nat} {P : List Nat} (hp : Paired P) (hw : Width B P) : Lose P ∧ nimSum P = 0 :=
  ⟨secondWins_sound (pairing_wins (B := B) P hp hw), (lose_iff P).1 (secondWins_sound (pairing_wins (B := B) P hp hw))⟩

/-- The mirror circuit uses no nim-sum: every formula reads only board bits. -/
theorem pairR_reads (B N : Nat) (hN : N % 2 = 0) : ∀ c ∈ (pairR B N).valid :: ((pairR B N).sel ++ (pairR B N).val),
    maxInput c ≤ B * N := by
  have hflag : ∀ k, k < N → maxInput (flagC B k) ≤ B * N := by
    intro k hk
    unfold flagC ltC
    apply maxInput_or_le; intro c hc
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hc
    have hp' := List.mem_range.mp hp
    have hpk := partner_lt hk hN
    have hv : ∀ q, q < B → maxInput (valC (cmpR B k) q) ≤ B * N := by
      intro q hq
      simp only [valC, cmpR, getC, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hq,
        Option.map_some, Option.getD_some, heapC, maxInput_input]
      have := Nat.mul_le_mul_left B (show partner k + 1 ≤ N by omega); rw [Nat.mul_add, Nat.mul_one] at this; omega
    have hh : ∀ q, q < B → maxInput (heapC B k q) ≤ B * N := by
      intro q hq; simp only [heapC, maxInput_input]
      have := Nat.mul_le_mul_left B (show k + 1 ≤ N by omega); rw [Nat.mul_add, Nat.mul_one] at this; omega
    apply maxInput_and_le; intro c hc
    simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false, List.mem_map, List.mem_range] at hc
    rcases hc with (rfl | rfl) | ⟨q, hq, rfl⟩
    · simpa using hv p hp'
    · exact hh p hp'
    · simp only [eqC, maxInput_or, maxInput_and, maxInput_not, List.map_cons, List.map_nil, listMax, List.foldr]
      have := hv q (by omega); have := hh q (by omega); omega
  intro c hc
  simp only [pairR, List.mem_cons, List.mem_append, List.mem_map, List.mem_range] at hc
  rcases hc with rfl | ⟨k, hk, rfl⟩ | ⟨p, hp, rfl⟩
  · apply maxInput_or_le; intro c hc; obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hc; exact hflag k (List.mem_range.mp hk)
  · exact hflag k hk
  · apply maxInput_or_le; intro c hc
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hc
    have hk' := List.mem_range.mp hk
    apply maxInput_and_le; intro c hc
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc
    rcases hc with rfl | rfl
    · exact hflag k hk'
    · simp only [heapC, maxInput_input]
      have := Nat.mul_le_mul_left B (show partner k + 1 ≤ N by have := partner_lt hk' hN; omega)
      rw [Nat.mul_add, Nat.mul_one] at this; omega

/-- Size bound for one mirror flag (a B-bit comparison of a heap with its partner). -/
def pairF (B : Nat) : Nat := B * ((2 + B) * 9 + 1) + 1

theorem valC_cmpR_res (B k q : Nat) : depth (valC (cmpR B k) q) = 0 ∧ size (valC (cmpR B k) q) = 1 := by
  by_cases hq : q < B
  · simp only [valC, cmpR, getC, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hq,
      Option.map_some, Option.getD_some, heapC, depth_input, size_input]
    exact ⟨trivial, trivial⟩
  · have : ((List.range B).map (fun p => heapC B (partner k) p))[q]? = none := by
      rw [List.getElem?_eq_none]; simp; omega
    simp only [valC, cmpR, getC, List.getD_eq_getElem?_getD, this, Option.getD_none, depth_const, size_const]
    exact ⟨trivial, trivial⟩

theorem flagC_res (B k : Nat) : depth (flagC B k) ≤ 5 ∧ size (flagC B k) ≤ pairF B := by
  have hv := valC_cmpR_res B k
  have hin : ∀ p, p < B → ∀ c ∈ [not (valC (cmpR B k) p), heapC B k p] ++
      (List.range p).map (fun p' => eqC (valC (cmpR B k) p') (heapC B k p')), depth c ≤ 3 ∧ size c ≤ 9 := by
    intro p hp c hc
    simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false, List.mem_map, List.mem_range] at hc
    rcases hc with (rfl | rfl) | ⟨q, hq, rfl⟩
    · simp only [depth_not, size_not]; have := hv p; omega
    · simp [heapC]
    · have := hv q
      simp only [eqC, heapC, depth_or, depth_and, depth_not, depth_input, size_or, size_and, size_not,
        size_input, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, listMax, List.foldr]
      omega
  constructor
  · unfold flagC ltC
    apply depth_or_le (D := 4); intro c hc
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hc
    apply depth_and_le (D := 3); intro c hc; exact (hin p (List.mem_range.mp hp) c hc).1
  · unfold flagC ltC pairF
    have h1 := ControllerBits.size_or_le' (S := (2 + B) * 9 + 1)
      (cs := (List.range B).map (fun p => and ([not (valC (cmpR B k) p), heapC B k p] ++
        (List.range p).map (fun p' => eqC (valC (cmpR B k) p') (heapC B k p'))))) (by
        intro c hc
        obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hc
        have hp' := List.mem_range.mp hp
        have h2 := ControllerBits.size_and_le' (S := 9) (fun c hc => (hin p hp' c hc).2)
        simp only [List.length_append, List.length_cons, List.length_nil, List.length_map,
          List.length_range] at h2
        omega)
    rw [List.length_map, List.length_range] at h1; exact h1

/-- RESOURCES of the mirror selector: every formula has depth ≤ 7 and size ≤ N(2F+1)+1
    with F = pairF B = O(B²). -/
theorem pairR_res (B N : Nat) : ∀ c ∈ (pairR B N).valid :: ((pairR B N).sel ++ (pairR B N).val),
    depth c ≤ 7 ∧ size c ≤ N * (2 * pairF B + 1) + 1 := by
  intro c hc
  simp only [pairR, List.mem_cons, List.mem_append, List.mem_map, List.mem_range] at hc
  rcases hc with rfl | ⟨k, hk, rfl⟩ | ⟨p, hp, rfl⟩
  · constructor
    · apply depth_or_le (D := 6); intro c hc
      obtain ⟨k, _, rfl⟩ := List.mem_map.mp hc; have := (flagC_res B k).1; omega
    · have h1 := ControllerBits.size_or_le' (cs := (List.range N).map (flagC B)) (S := pairF B)
        (fun c hc => by obtain ⟨k, _, rfl⟩ := List.mem_map.mp hc; exact (flagC_res B k).2)
      rw [List.length_map, List.length_range] at h1
      have := Nat.mul_le_mul_left N (show pairF B ≤ 2 * pairF B + 1 by omega); omega
  · refine ⟨by have := (flagC_res B k).1; omega, ?_⟩
    have h2 := (flagC_res B k).2
    have : 2 * pairF B + 1 ≤ N * (2 * pairF B + 1) := Nat.le_mul_of_pos_left _ (by omega)
    omega
  · constructor
    · apply depth_or_le (D := 6); intro c hc; obtain ⟨k, _, rfl⟩ := List.mem_map.mp hc
      apply depth_and_le (D := 5); intro c hc
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc
      rcases hc with rfl | rfl
      · exact (flagC_res B k).1
      · simp [heapC]
    · have h1 := ControllerBits.size_or_le'
        (cs := (List.range N).map (fun k => and [flagC B k, heapC B (partner k) p])) (S := 2 * pairF B + 1) (by
          intro c hc; obtain ⟨k, _, rfl⟩ := List.mem_map.mp hc
          simp only [size_and, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, heapC, size_input]
          have := (flagC_res B k).2; have : 1 ≤ pairF B := by unfold pairF; omega
          omega)
      rw [List.length_map, List.length_range] at h1; exact h1

/-- The binary mirror selector is a constant-depth (≤ 10), polynomial-size formula family
    reading only the B·N board bits. -/
theorem pairBin_bound (B N r : Nat) (hr : N ≤ 2 ^ r) (hN : N % 2 = 0) :
    BinBound (pairBin B N r) N B r 10 (4 * ((N + 2) * (N * (2 * pairF B + 1) + 1 + 2)) ^ 3) (B * N) :=
  encode_bound (pairR B N) (by simp [pairR]) (by simp [pairR]) hr
    (fun c hc => ⟨(pairR_res B N c hc).1, (pairR_res B N c hc).2, pairR_reads B N hN c hc⟩)

/-! ## B. Finite-state shootout controllers -/

/-- A finite-state controller over rollout heads: states are numbers; `head s` is the head
    queried in state s; `next s b` is the successor after outcome b; `out s` is the
    decision of a halting state. -/
structure FSM where
  init : Nat
  head : Nat → Nat
  next : Nat → Bool → Nat
  out : Nat → Option Bool

/-- Run with fuel against outcome oracle o: decision and number of queries. -/
def FSM.run (C : FSM) (o : Nat → Bool) : Nat → Nat → Option Bool × Nat
  | 0, _ => (none, 0)
  | f + 1, s => match C.out s with
    | some d => (some d, 0)
    | none => ((C.run o f (C.next s (o (C.head s)))).1, (C.run o f (C.next s (o (C.head s)))).2 + 1)

/-- The controller of the figure: states 0..B−1 query heads 0..B−1 in turn; state B
    declares σ ≠ 0 (N-position), state B+1 declares σ = 0 (P-position). -/
def shootout (B : Nat) : FSM :=
  ⟨0, id, fun s b => if b then B else if s + 1 < B then s + 1 else B + 1,
   fun s => if s = B then some true else if s = B + 1 then some false else none⟩

/-- Index of the first true outcome among heads j..B−1 (B if none). -/
def firstHit (o : Nat → Bool) (B : Nat) : Nat → Nat
  | j => if h : j < B then (if o j then j else firstHit o B (j + 1)) else B
termination_by j => B - j

theorem firstHit_ge (o : Nat → Bool) (B : Nat) : ∀ j, j ≤ B → j ≤ firstHit o B j := by
  intro j
  induction j using (measure (fun j => B - j)).wf.induction with
  | h j ih =>
    intro hj
    rw [firstHit]
    by_cases h : j < B
    · simp only [h, dif_pos]
      split
      · omega
      · have := ih (j + 1) (by show B - (j + 1) < B - j; omega) (by omega); omega
    · simp only [h, dif_neg, not_false_eq_true]; omega

theorem run_query {B j : Nat} (o : Nat → Bool) (hj : j < B) (f : Nat) :
    (shootout B).run o (f + 1) j =
      (((shootout B).run o f (if o j then B else if j + 1 < B then j + 1 else B + 1)).1,
       ((shootout B).run o f (if o j then B else if j + 1 < B then j + 1 else B + 1)).2 + 1) := by
  have hout : (shootout B).out j = none := by
    simp only [shootout]; rw [if_neg (by omega), if_neg (by omega)]
  simp only [FSM.run, hout]; rfl

theorem run_yes (B : Nat) (o : Nat → Bool) (f : Nat) : (shootout B).run o (f + 1) B = (some true, 0) := by
  simp [FSM.run, shootout]

theorem run_no (B : Nat) (o : Nat → Bool) (f : Nat) : (shootout B).run o (f + 1) (B + 1) = (some false, 0) := by
  simp [FSM.run, shootout]

theorem firstHit_hit {o : Nat → Bool} {B j : Nat} (hj : j < B) (ho : o j = true) : firstHit o B j = j := by
  rw [firstHit]; simp [hj, ho]

theorem firstHit_miss {o : Nat → Bool} {B j : Nat} (hj : j < B) (ho : o j = false) :
    firstHit o B j = firstHit o B (j + 1) := by
  rw [firstHit]; simp [hj, ho]

theorem firstHit_end {o : Nat → Bool} {B j : Nat} (hj : B ≤ j) : firstHit o B j = B := by
  rw [firstHit, dif_neg (by omega)]

/-- RUN OF THE SHOOTOUT CONTROLLER from head j with k = B − j heads left: the decision is
    the OR of the queried outcomes; the number of queries is 1 + (first hit) − j, or the
    number of remaining heads if there is no hit. -/
theorem shootout_from {B : Nat} (o : Nat → Bool) : ∀ (k j : Nat), j + (k + 1) = B →
    (shootout B).run o (k + 2) j = (some ((List.range' j (k + 1)).any o), min (firstHit o B j) (B - 1) - j + 1) := by
  intro k
  induction k with
  | zero =>
    intro j h
    obtain rfl : B = j + 1 := by omega
    rw [run_query o (by omega)]
    cases ho : o j with
    | true => simp [run_yes, ho, firstHit_hit (show j < j + 1 by omega) ho]
    | false =>
      rw [if_neg (by simp), if_neg (by omega), run_no]
      simp [ho, firstHit_miss (show j < j + 1 by omega) ho, firstHit_end (o := o) (show j + 1 ≤ j + 1 by omega)]
  | succ k ih =>
    intro j h
    rw [run_query o (by omega)]
    cases ho : o j with
    | true =>
      simp only [if_true, run_yes, List.range'_succ, List.any_cons, ho, Bool.true_or, firstHit_hit (show j < B by omega) ho]
      simp; omega
    | false =>
      rw [if_neg (by simp), if_pos (by omega), ih (j + 1) (by omega)]
      have hge := firstHit_ge o B (j + 1) (by omega)
      simp only [List.range'_succ, List.any_cons, ho, Bool.false_or, firstHit_miss (show j < B by omega) ho,
        Prod.mk.injEq, true_and]
      omega

/-- SHOOTOUT CONTROLLER THEOREM: started at head 0 with fuel B + 1 it outputs the OR of the
    B outcome bits, using at most B queries (one query if head 0 reports 1). -/
theorem shootout_spec {B : Nat} (hB : 1 ≤ B) (o : Nat → Bool) :
    ((shootout B).run o (B + 1) 0).1 = some ((List.range B).any o) ∧
    ((shootout B).run o (B + 1) 0).2 ≤ B ∧
    (o 0 = true → ((shootout B).run o (B + 1) 0).2 = 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, B = k + 1 := ⟨B - 1, by omega⟩
  have h := shootout_from (B := k + 1) o k 0 (by omega)
  rw [show k + 1 + 1 = k + 2 by omega, h, List.range_eq_range']
  refine ⟨rfl, by simp; omega, fun h0 => ?_⟩
  simp [firstHit_hit (show 0 < k + 1 by omega) h0]

/-- With the exact structured heads, the OR of the channel bits is (nim(P) ≠ 0). -/
theorem channels_or {B : Nat} (hB : 1 ≤ B) {P : List Nat} (hw : Width B P) :
    (List.range B).any (fun j => rolloutWinner j P) = decide (nimSum P ≠ 0) := by
  have hσ := nimSum_lt hw
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true, List.mem_range, decide_eq_true_iff, rolloutWinner_channel, channel]
  constructor
  · rintro ⟨j, hj, h⟩ h0
    rw [h0] at h; split at h <;> simp at h
  · intro h0
    by_cases h1 : (nimSum P).testBit 0 = true
    · exact ⟨0, by omega, by simp [h1]⟩
    · obtain ⟨k, hk, hbit⟩ := (pos_iff_bitLE hσ).1 (by omega)
      have hk0 : k ≠ 0 := by intro e; subst e; exact h1 hbit
      refine ⟨k, hk, ?_⟩
      simp [hk0, hbit, show (nimSum P).testBit 0 = false by simpa using h1]

/-- The shootout over the exact structured heads decides whether P is an N-position. -/
theorem shootout_decides {B : Nat} (hB : 1 ≤ B) {P : List Nat} (hw : Width B P) :
    ((shootout B).run (fun j => rolloutWinner j P) (B + 1) 0).1 = some (decide (nimSum P ≠ 0)) ∧
    ((shootout B).run (fun j => rolloutWinner j P) (B + 1) 0).2 ≤ B := by
  obtain ⟨h1, h2, _⟩ := shootout_spec hB (fun j => rolloutWinner j P)
  exact ⟨by rw [h1, channels_or hB hw], h2⟩

/-! ## C. Single-head baseline numbers -/

theorem odd_count (n : Nat) : ((List.range (2 * n)).filter (fun σ => σ % 2 == 1)).length = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by omega, List.range_succ, List.range_succ]
    simp only [List.filter_append, List.length_append, ih]
    simp <;> omega

/-- Among the 2^B − 1 nonzero nim-sums of B ≥ 1 bits, exactly 2^{B−1} have σ₀ = 1, i.e.
    are detected by the classifier "declare N iff r₀ = 1" (r₀ = σ₀). -/
theorem detected_count {B : Nat} (hB : 1 ≤ B) :
    ((List.range (2 ^ B)).filter (fun σ => σ % 2 == 1)).length = 2 ^ (B - 1) ∧
    ((List.range (2 ^ B)).filter (fun σ => σ != 0)).length = 2 ^ B - 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, B = k + 1 := ⟨B - 1, by omega⟩
  refine ⟨by rw [Nat.pow_succ, Nat.mul_comm, show k + 1 - 1 = k by omega]; exact odd_count _, ?_⟩
  have : ∀ n, ((List.range (n + 1)).filter (fun σ => σ != 0)).length = n := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => rw [List.range_succ, List.filter_append, List.length_append, ih]; simp
  have hp : 2 ^ (k + 1) = (2 ^ (k + 1) - 1) + 1 := by have := Nat.one_le_two_pow (n := k + 1); omega
  have h2 := this (2 ^ (k + 1) - 1)
  rw [← hp] at h2; exact h2

theorem baseline_numbers :
    ((List.range (2 ^ 4)).filter (fun σ => σ % 2 == 1)).length = 8 ∧
    ((List.range (2 ^ 4)).filter (fun σ => σ != 0)).length = 15 ∧
    (1 / 2 : Rat) * 1 + 1 / 2 * (8 / 15) = 23 / 30 := by
  refine ⟨by decide, by decide, by grind⟩

/-- The r₀ classifier never errs on P-positions: σ = 0 has σ₀ = 0. -/
theorem baseline_P (P : List Nat) (h : nimSum P = 0) : rolloutWinner 0 P = false := by
  rw [rolloutWinner_channel, h]; simp [channel]

/-! ## D. Independent outcome flips -/

/-- Product Bernoulli(ε) weight of a flip pattern. -/
def bw (ε : Rat) : List Bool → Rat
  | [] => 1
  | b :: e => (if b then ε else 1 - ε) * bw ε e

theorem bw_total (ε : Rat) : ∀ L, rsum (bitvecs L) (bw ε) = 1
  | 0 => by simp [bitvecs, bw]
  | L + 1 => by
    rw [rsum_bitvecs_succ]
    simp only [bw, Bool.false_eq_true, if_false, if_true]
    rw [rsum_mul_left, rsum_mul_left, bw_total ε L]; grind

theorem bw_sign (ε : Rat) : ∀ L, rsum (bitvecs L) (fun e => bw ε e * sgn (par e)) = (1 - 2 * ε) ^ L
  | 0 => by simp [bitvecs, bw, par, sgn]
  | L + 1 => by
    rw [rsum_bitvecs_succ]
    have e1 : rsum (bitvecs L) (fun v => bw ε (false :: v) * sgn (par (false :: v))) =
        (1 - ε) * rsum (bitvecs L) (fun v => bw ε v * sgn (par v)) := by
      rw [← rsum_mul_left]; apply rsum_congr; intro v _; simp [bw, par]; grind
    have e2 : rsum (bitvecs L) (fun v => bw ε (true :: v) * sgn (par (true :: v))) =
        (-ε) * rsum (bitvecs L) (fun v => bw ε v * sgn (par v)) := by
      rw [← rsum_mul_left]; apply rsum_congr; intro v _
      simp only [bw, if_true, par, Bool.true_xor]
      cases par v <;> simp [sgn] <;> grind
    rw [e1, e2, bw_sign ε L, Rat.pow_succ]; grind

/-- OUTCOME-FLIP FORMULA: Pr[Y ⊕ E₁ ⊕ … ⊕ E_L = Y] = (1 + (1 − 2ε)^L)/2 for independent
    Bernoulli(ε) flips (exact, for every rational ε). -/
theorem flip_agree (ε : Rat) (L : Nat) :
    rsum (bitvecs L) (fun e => bw ε e * (if par e then 0 else 1)) = (1 + (1 - 2 * ε) ^ L) / 2 := by
  have h : ∀ e : List Bool, bw ε e * (if par e then 0 else 1) = (1 / 2) * bw ε e + (1 / 2) * (bw ε e * sgn (par e)) := by
    intro e; cases par e <;> simp [sgn] <;> grind
  rw [rsum_congr (fun e _ => h e), rsum_add, rsum_mul_left, rsum_mul_left, bw_total, bw_sign]; grind

theorem flip_agree_noisy (ε : Rat) (L : Nat) (Y : Bool) :
    rsum (bitvecs L) (fun e => bw ε e * (if xor Y (par e) = Y then 1 else 0)) = (1 + (1 - 2 * ε) ^ L) / 2 := by
  rw [← flip_agree]; apply rsum_congr; intro e _; cases Y <;> cases par e <;> simp

theorem par_append : ∀ x y : List Bool, par (x ++ y) = xor (par x) (par y)
  | [], y => by simp [par]
  | b :: x, y => by simp only [List.cons_append, par, par_append x y, Bool.xor_assoc]

/-- CORRELATED FLIPS CAN CANCEL (Remark rem:noisy-rollout-decay): if the flips come in
    identical pairs, their XOR is always 0, so the observed bit always equals Y and there
    is no decay, whatever the flip probability. -/
theorem paired_flips_cancel (Y : Bool) (e : List Bool) : xor Y (par (e ++ e)) = Y := by
  rw [par_append]; cases par e <;> simp

/-- Numerical example: ε = 1/100, L = 50 gives agreement in [0.682, 0.6822]. -/
theorem flip_example_nat : 364 * 50 ^ 50 ≤ 1000 * 49 ^ 50 ∧ 10000 * 49 ^ 50 ≤ 3644 * 50 ^ 50 := by
  constructor <;> decide

/-! ## E. Spectral facts -/

theorem pm_zipWith : ∀ (S T x : List Bool), S.length = T.length →
    pm (List.zipWith xor S T) x = xor (pm S x) (pm T x)
  | [], [], _, _ => by simp [pm]
  | s :: S, t :: T, [], _ => by simp [pm]
  | s :: S, t :: T, b :: x, h => by
    simp only [List.zipWith_cons_cons, pm]
    rw [pm_zipWith S T x (by simpa using h)]
    cases s <;> cases t <;> cases b <;> simp
  | [], _ :: _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h

/-- Character sums: Σ_x (−1)^{⟨U,x⟩} = 2^n if U = 0, and 0 otherwise. -/
theorem char_sum : ∀ U : List Bool,
    rsum (bitvecs U.length) (fun x => sgn (pm U x)) = if U.all (fun b => b == false) then (2 : Rat) ^ U.length else 0
  | [] => by simp [bitvecs, pm, sgn]
  | u :: U => by
    simp only [List.length_cons]
    rw [rsum_bitvecs_succ]
    simp only [pm, Bool.and_false, Bool.false_xor, Bool.and_true]
    rw [char_sum U]
    cases u
    · simp only [Bool.false_xor, List.all_cons, beq_self_eq_true, Bool.true_and]
      have : rsum (bitvecs U.length) (fun v => sgn (pm U v)) = if U.all (fun b => b == false) then (2 : Rat) ^ U.length else 0 :=
        char_sum U
      rw [this]; split <;> simp [Rat.pow_succ] <;> grind
    · have e : rsum (bitvecs U.length) (fun v => sgn (xor true (pm U v))) =
          (-1) * rsum (bitvecs U.length) (fun v => sgn (pm U v)) := by
        rw [← rsum_mul_left]; apply rsum_congr; intro v _; cases pm U v <;> simp [sgn] <;> grind
      rw [e, char_sum U]
      simp only [List.all_cons]
      split <;> simp <;> grind

theorem zipWith_xor_all_false : ∀ (S T : List Bool), S.length = T.length →
    ((List.zipWith xor S T).all (fun b => b == false) = true ↔ S = T)
  | [], [], _ => by simp
  | s :: S, t :: T, h => by
    simp only [List.zipWith_cons_cons, List.all_cons, Bool.and_eq_true, List.cons.injEq]
    rw [zipWith_xor_all_false S T (by simpa using h)]
    cases s <;> cases t <;> simp
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

/-- ORTHONORMALITY of the characters χ_S(x) = (−1)^{⟨S,x⟩} on {0,1}^n. -/
theorem char_orth (S T : List Bool) (h : S.length = T.length) :
    rsum (bitvecs S.length) (fun x => sgn (pm S x) * sgn (pm T x)) / (2 : Rat) ^ S.length = if S = T then 1 else 0 := by
  have e : ∀ x, sgn (pm S x) * sgn (pm T x) = sgn (pm (List.zipWith xor S T) x) := by
    intro x; rw [pm_zipWith S T x h]; cases pm S x <;> cases pm T x <;> simp [sgn] <;> grind
  rw [rsum_congr (fun x _ => e x)]
  have hl : (List.zipWith xor S T).length = S.length := by simp [h]
  have hs := char_sum (List.zipWith xor S T)
  rw [hl] at hs
  rw [hs]
  have hpos := two_pow_pos' S.length
  have hne : (2 : Rat) ^ S.length ≠ 0 := Rat.ne_of_gt hpos
  by_cases hST : S = T
  · rw [if_pos ((zipWith_xor_all_false S T h).2 hST), if_pos hST]
    rw [Rat.div_def]; exact Rat.mul_inv_cancel _ hne
  · have : ¬ ((List.zipWith xor S T).all (fun b => b == false) = true) := fun h' => hST ((zipWith_xor_all_false S T h).1 h')
    rw [if_neg this, if_neg hST]
    rw [Rat.div_def, Rat.zero_mul]

theorem dotB_low {j : Nat} (v : Nat) : ∀ B, B ≤ j → dotB B (2 ^ j) v = false
  | 0, _ => rfl
  | B + 1, h => by
    simp only [dotB, Nat.testBit_two_pow, dotB_low (j := j) v B (by omega)]
    simp; omega

theorem dotB_pow {j : Nat} (v : Nat) : ∀ B, j < B → dotB B (2 ^ j) v = v.testBit j
  | 0, h => by omega
  | B + 1, h => by
    simp only [dotB, Nat.testBit_two_pow]
    by_cases hj : j = B
    · subst hj; rw [dotB_low v j (Nat.le_refl _)]; simp
    · rw [dotB_pow (j := j) v B (by omega)]; simp [hj]

theorem count_eq_one (j : Nat) : ∀ B, ((List.range B).filter (fun k => decide (j = k))).length = if j < B then 1 else 0
  | 0 => by simp
  | B + 1 => by
    rw [List.range_succ, List.filter_append, List.length_append, count_eq_one j B]
    by_cases h1 : j < B
    · rw [if_pos h1, if_pos (by omega)]; simp; omega
    · by_cases h2 : j = B
      · subst h2; simp
      · rw [if_neg h1, if_neg (by omega)]; simp; omega

theorem ones_toBitsBE_count : ∀ (B u : Nat), Bridge.ones (toBitsBE B u) = ((List.range B).filter (fun k => u.testBit k)).length
  | 0, u => by simp [toBitsBE, Bridge.ones]
  | B + 1, u => by
    simp only [toBitsBE, Bridge.ones, List.filter_cons, List.range_succ, List.filter_append, List.length_append]
    have := ones_toBitsBE_count B u
    unfold Bridge.ones at this
    cases h : u.testBit B <;> simp [h, this] <;> omega

/-- NIM-SUM BITS ARE DEGREE-N CHARACTERS: bit j of nim(P) is the parity of the inputs on
    a mask with exactly N ones (one coordinate per heap). -/
theorem nimsum_bit_character {B N j : Nat} (hj : j < B) {x : List Bool} (hx : x ∈ bitvecs (B * N)) :
    (nimSum (decodeBoard B N x)).testBit j = pm (maskU B N (2 ^ j)) x ∧ Bridge.ones (maskU B N (2 ^ j)) = N := by
  refine ⟨by rw [← chi_parity B N (2 ^ j) hx]; exact (dotB_pow _ B hj).symm, ?_⟩
  rw [ones_maskU, ones_toBitsBE_count]
  have : (List.range B).filter (fun k => (2 ^ j).testBit k) = (List.range B).filter (fun k => decide (j = k)) := by
    apply List.filter_congr; intro k _; rw [Nat.testBit_two_pow]
  rw [this, count_eq_one, if_pos hj, Nat.mul_one]

/-- DELTA BITS ARE TWO-COORDINATE CHARACTERS: across one legal move (heap value a → b),
    bit k of the difference is a_k ⊕ b_k. -/
theorem delta_bit_local {Q Q' : List Nat} (hm : Move Q Q') :
    ∃ pre a post b, Q = pre ++ a :: post ∧ Q' = pre ++ b :: post ∧
      ∀ k, (nimSum Q ^^^ nimSum Q').testBit k = xor (a.testBit k) (b.testBit k) := by
  obtain ⟨pre, a, post, b, h1, h2, _⟩ := hm
  refine ⟨pre, a, post, b, h1, h2, fun k => ?_⟩
  rw [h1, h2, one_heap_difference, Nat.testBit_xor]

/-! ## F. The initialisation boundary -/

/-- The matching-delta policy completed by "subtract one from the first nonempty heap"
    whenever there is no previous frame or no matching response. -/
def mdPolicy (prev : Option (List Nat)) (cur : List Nat) : Option (List Nat) :=
  match prev with
  | none => subFirstPos cur
  | some Q => match cancelFirst (nimSum Q ^^^ nimSum cur) cur with
    | some R => some R
    | none => subFirstPos cur

/-- From the winning position (2) the completed matching-delta policy plays (2) → (1) and
    then (as the next mover, delta 2 ⊕ 1 = 3 is not realisable from (1)) (1) → (0): the
    first player loses although (2) is winning. -/
theorem init_counterexample :
    Win [2] ∧ mdPolicy none [2] = some [1] ∧ cancelFirst (nimSum [2] ^^^ nimSum [1]) [1] = none ∧
    mdPolicy (some [2]) [1] = some [0] ∧ Win [1] ∧ Lose [0] := by
  refine ⟨(win_iff _).2 (by decide), by decide, by decide, by decide, (win_iff _).2 (by decide),
    (lose_iff _).2 (by decide)⟩

/-! ## G. Single-policy information bound (one-heap correction) -/

theorem single_policy_correction (j : Nat) (pre post : List Nat) (h h' : Nat) :
    rolloutWinner j (pre ++ h' :: post) = xor (rolloutWinner j (pre ++ h :: post)) (channel j (h ^^^ h')) := by
  rw [rolloutWinner_channel, rolloutWinner_channel, one_heap_update pre post h h', Nat.xor_assoc, channel_xor]


/-! ### Board-level recall and the numerical flip example -/

theorem rsum_filter_count (l : List Nat) (p : Nat → Bool) (c : Rat) :
    rsum l (fun a => if p a then c else 0) = ((l.filter p).length : Rat) * c := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [rsum_cons, List.filter_cons]
    rw [ih]; cases p a <;> simp <;> grind

/-- For uniform boards of N+1 heaps, the number of boards whose nim-sum satisfies a
    predicate p is (#values a < 2^B with p a) · (2^B)^N (nim-sum is exactly uniform). -/
theorem boards_count (B N : Nat) (p : Nat → Bool) :
    rsum (boards (2 ^ B) (N + 1)) (fun P => if p (nimSum P) then 1 else 0) =
      (((List.range (2 ^ B)).filter p).length : Rat) * ((2 ^ B : Nat) : Rat) ^ N := by
  have hexp : ∀ P ∈ boards (2 ^ B) (N + 1), (if p (nimSum P) then (1 : Rat) else 0) =
      rsum (List.range (2 ^ B)) (fun a => if a = nimSum P then (if p a then 1 else 0) else 0) := by
    intro P hP
    rw [rsum_range_ite (2 ^ B) (nimSum P) (fun a => if p a then 1 else 0), if_pos (sigma_lt hP)]
  rw [rsum_congr hexp, rsum_comm]
  have hin : ∀ a ∈ List.range (2 ^ B),
      rsum (boards (2 ^ B) (N + 1)) (fun P => if a = nimSum P then (if p a then (1 : Rat) else 0) else 0) =
        (if p a then ((2 ^ B : Nat) : Rat) ^ N else 0) := by
    intro a ha
    have hu := sigma_uniform B N a (List.mem_range.mp ha)
    cases hpa : p a
    · simp only [Bool.false_eq_true, if_false]; rw [rsum_congr (fun _ _ => by split <;> rfl)]; simp [rsum_zero]
    · simp only [if_true]
      rw [← hu]; apply rsum_congr; intro P _
      by_cases h : a = nimSum P
      · rw [if_pos h, if_pos h.symm]
      · rw [if_neg h, if_neg (Ne.symm h)]
  rw [rsum_congr hin, rsum_filter_count]

/-- BOARD-LEVEL RECALL OF THE r₀ CLASSIFIER: among uniform boards with nonzero nim-sum the
    detected fraction is 2^{B−1}/(2^B − 1); for B = 4 it is 8/15. -/
theorem board_recall {B : Nat} (hB : 1 ≤ B) (N : Nat) :
    rsum (boards (2 ^ B) (N + 1)) (fun P => if (nimSum P % 2 == 1) then 1 else 0) =
      ((2 ^ (B - 1) : Nat) : Rat) * ((2 ^ B : Nat) : Rat) ^ N ∧
    rsum (boards (2 ^ B) (N + 1)) (fun P => if (nimSum P != 0) then 1 else 0) =
      ((2 ^ B - 1 : Nat) : Rat) * ((2 ^ B : Nat) : Rat) ^ N := by
  obtain ⟨h1, h2⟩ := detected_count hB
  refine ⟨?_, ?_⟩
  · rw [boards_count B N (fun σ => σ % 2 == 1), h1]
  · rw [boards_count B N (fun σ => σ != 0), h2]

theorem pow_frac (a b : Nat) (hb : 0 < b) : ∀ n : Nat, ((a : Rat) / b) ^ n * (b : Rat) ^ n = (a : Rat) ^ n
  | 0 => by simp
  | n + 1 => by
    have hb' : (b : Rat) ≠ 0 := by exact_mod_cast (show b ≠ 0 by omega)
    have ih := pow_frac a b hb n
    rw [Rat.pow_succ, Rat.pow_succ, Rat.pow_succ]
    have e : ((a : Rat) / b) * b = a := by rw [Rat.div_def, Rat.mul_assoc, Rat.inv_mul_cancel _ hb', Rat.mul_one]
    calc ((a : Rat) / b) ^ n * (a / b) * ((b : Rat) ^ n * b) = (((a : Rat) / b) ^ n * (b : Rat) ^ n) * ((a / b) * b) := by
          grind
      _ = (a : Rat) ^ n * a := by rw [ih, e]

theorem le_div_of_mul_le' {x y d : Rat} (hd : 0 < d) (h : y * d ≤ x) : y ≤ x / d := by
  apply Rat.le_of_mul_le_mul_right _ hd
  have e : x / d * d = x := by
    rw [Rat.div_def, Rat.mul_assoc, Rat.inv_mul_cancel _ (Rat.ne_of_gt hd), Rat.mul_one]
  rw [e]; exact h

/-- NUMERICAL EXAMPLE of Remark rem:noisy-rollout-decay: for ε = 1/100 and L = 50 the
    agreement probability lies between 0.682 and 0.6822. -/
theorem flip_example :
    (682 / 1000 : Rat) ≤ (1 + (1 - 2 * (1 / 100 : Rat)) ^ 50) / 2 ∧
    (1 + (1 - 2 * (1 / 100 : Rat)) ^ 50) / 2 ≤ 6822 / 10000 := by
  have e1 : (1 - 2 * (1 / 100 : Rat)) = ((49 : Nat) : Rat) / ((50 : Nat) : Rat) := by grind
  rw [e1]
  have hq := pow_frac 49 50 (by decide) 50
  generalize (((49 : Nat) : Rat) / ((50 : Nat) : Rat)) ^ 50 = q at hq ⊢
  have hT : (0 : Rat) < ((50 : Nat) : Rat) ^ 50 := Rat.pow_pos (by decide)
  obtain ⟨n1, n2⟩ := flip_example_nat
  have c1 : (364 : Rat) * ((50 : Nat) : Rat) ^ 50 ≤ 1000 * ((49 : Nat) : Rat) ^ 50 := by exact_mod_cast n1
  have c2 : (10000 : Rat) * ((49 : Nat) : Rat) ^ 50 ≤ 3644 * ((50 : Nat) : Rat) ^ 50 := by exact_mod_cast n2
  rw [← hq] at c1 c2
  generalize ((50 : Nat) : Rat) ^ 50 = T at hT c1 c2
  have d1 : (364 : Rat) ≤ 1000 * q := by
    apply Rat.le_of_mul_le_mul_right _ hT
    have : 1000 * (q * T) = (1000 * q) * T := by grind
    rw [← this]; exact c1
  have d2 : 10000 * q ≤ (3644 : Rat) := by
    apply Rat.le_of_mul_le_mul_right _ hT
    have : 10000 * (q * T) = (10000 * q) * T := by grind
    rw [← this]; exact c2
  have two : (0 : Rat) < 2 := by decide
  constructor
  · have ea : (682 / 1000 : Rat) = (1364 / 1000) / 2 := by grind
    rw [ea]
    apply div_le_div_of_le two
    apply le_div_of_mul_le (by decide)
    have : (1 + q) * 1000 = 1000 + 1000 * q := by grind
    rw [this]; grind
  · have eb : (6822 / 10000 : Rat) = (13644 / 10000) / 2 := by grind
    rw [eb]
    apply div_le_div_of_le two
    apply le_div_of_mul_le' (by decide)
    have : (1 + q) * 10000 = 10000 + 10000 * q := by grind
    rw [this]; grind

/-! ## H. Two small worked claims -/

/-- FIGURE fig:restoration-example: from (3,5,6) (nim-sum 0) the opponent plays 5 → 4
    (nim-sum 1, δ = 1); the restoration rule answers 3 → 2, restoring nim-sum 0. -/
theorem restoration_figure :
    nimSum [3, 5, 6] = 0 ∧ Move [3, 5, 6] [3, 4, 6] ∧ nimSum [3, 4, 6] = 1 ∧ (5 ^^^ 4 : Nat) = 1 ∧
    restore [3, 5, 6] [3, 4, 6] = some [2, 4, 6] ∧ Move [3, 4, 6] [2, 4, 6] ∧ nimSum [2, 4, 6] = 0 := by
  refine ⟨by decide, ⟨[3], 5, [6], 4, rfl, rfl, by decide⟩, by decide, by decide, by decide,
    ⟨[], 3, [4, 6], 2, rfl, rfl, by decide⟩, by decide⟩

theorem nimSum_bitBoard (k : Nat) : ∀ P : List Nat,
    (nimSum (P.map (fun h => if h.testBit k then 1 else 0))).testBit 0 = (nimSum P).testBit k
  | [] => by simp [nimSum]
  | h :: P => by
    have ih := nimSum_bitBoard k P
    simp only [List.map_cons, nimSum] at ih ⊢
    rw [Nat.testBit_xor, Nat.testBit_xor, ih]
    by_cases hb : h.testBit k <;> simp [hb]

/-- WHY ARBITRARY START POSITIONS ARE EXCLUDED (Definition def:agent-types): a single
    rollout of π₀ on the board whose heaps are the k-th bits of P returns σ_k(P). -/
theorem bitBoard_query (k : Nat) (P : List Nat) :
    rolloutWinner 0 (P.map (fun h => if h.testBit k then 1 else 0)) = (nimSum P).testBit k := by
  rw [rolloutWinner_channel]; simp only [channel, if_true]; exact nimSum_bitBoard k P

/-! ## Axiom audit -/

#print axioms partner_partner
#print axioms partner_ne
#print axioms partner_lt
#print axioms secondWins_sound
#print axioms getD_set_ne'
#print axioms getD_set_eq'
#print axioms paired_move
#print axioms toNatBE_heap
#print axioms flagC_eval
#print axioms pairR_correct
#print axioms pairing_wins
#print axioms paired_lose
#print axioms pairR_reads
#print axioms valC_cmpR_res
#print axioms flagC_res
#print axioms pairR_res
#print axioms pairBin_bound
#print axioms firstHit_ge
#print axioms run_query
#print axioms run_yes
#print axioms run_no
#print axioms firstHit_hit
#print axioms firstHit_miss
#print axioms firstHit_end
#print axioms shootout_from
#print axioms shootout_spec
#print axioms channels_or
#print axioms shootout_decides
#print axioms odd_count
#print axioms detected_count
#print axioms baseline_numbers
#print axioms baseline_P
#print axioms bw_total
#print axioms bw_sign
#print axioms flip_agree
#print axioms flip_agree_noisy
#print axioms par_append
#print axioms paired_flips_cancel
#print axioms flip_example_nat
#print axioms pm_zipWith
#print axioms char_sum
#print axioms zipWith_xor_all_false
#print axioms char_orth
#print axioms dotB_low
#print axioms dotB_pow
#print axioms count_eq_one
#print axioms ones_toBitsBE_count
#print axioms nimsum_bit_character
#print axioms delta_bit_local
#print axioms init_counterexample
#print axioms single_policy_correction
#print axioms rsum_filter_count
#print axioms boards_count
#print axioms board_recall
#print axioms pow_frac
#print axioms le_div_of_mul_le'
#print axioms flip_example
#print axioms restoration_figure
#print axioms nimSum_bitBoard
#print axioms bitBoard_query


