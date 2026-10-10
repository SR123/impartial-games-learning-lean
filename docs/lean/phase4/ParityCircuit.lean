import BinaryReadout

/- Phase 4, Priority 2c: the concrete parity reduction.  Written by Claude
   (10 October 2026).  Lean 4.26.0, core/Std only.

   Replaces the phase-2 generic closure/hardness packaging by an explicit circuit
   composition.  A binary move selector (BCirc, B = 2 bits per heap, N = m+1 heaps)
   that plays a winning move on every winning 2-bit board yields, by LEAF
   SUBSTITUTION (two-bit heap encoding of (2, b_1, ..., b_m)), a formula of the SAME
   depth and size, reading only the m parity inputs, that computes b_1 XOR ... XOR b_m.
   Hence the classical statement "no formula of depth ≤ d and size ≤ s computes parity
   of m bits" (ParityHard) rules out such selectors.  ParityHard itself follows from
   the correlation premise with error ε < 1/2, so the single remaining assumption is
   the classical AC0 parity theorem. -/

namespace NimAudit
namespace ParityCircuit

open Prob AC0 AC0.Circ Game Bridge Rollout CorrBridge BinReadout

attribute [local simp] Rat.add_zero Rat.zero_add

/-- The move of a binary selector (no observed bit). -/
def binMove (S : BCirc) (N : Nat) (P : List Nat) : Option (Nat × Nat) :=
  binReadoutOf 2 N (fun _ => S) P false

/-- Strong mastery on 2-bit boards with N heaps: from every winning position the
    selector outputs a legal move to a losing position. -/
def StrongMastery (S : BCirc) (N : Nat) : Prop :=
  ∀ P : List Nat, P.length = N → Width 2 P → Win P →
    ∃ i v x, binMove S N P = some (i, v) ∧ P[i]? = some x ∧ v < x ∧ Lose (P.set i v)

theorem par_eq_parity : ∀ y : List Bool, par y = parity y
  | [] => rfl
  | b :: y => by simp [par, parity, par_eq_parity y]

theorem length_encode (bs : List Bool) : (encode bs).length = bs.length + 1 := by
  simp [encode]

theorem encode_width (bs : List Bool) : Width 2 (encode bs) := by
  intro x hx
  simp only [encode, List.mem_cons, List.mem_map] at hx
  rcases hx with rfl | ⟨b, _, rfl⟩
  · decide
  · have := Bool.toNat_le b; omega

/-- A winning move from (2, b_1, ..., b_m) is (index 0, new value parity). -/
theorem winning_move_on_encode (bs : List Bool) {i v x : Nat} (hx : (encode bs)[i]? = some x)
    (hv : v < x) (hz : nimSum ((encode bs).set i v) = 0) : i = 0 ∧ v = (parity bs).toNat := by
  have hred := unique_zero_move bs _ (set_move hx hv) hz
  cases i with
  | zero =>
    refine ⟨rfl, ?_⟩
    have := congrArg List.head? hred
    simp [encode, reduced] at this
    exact this
  | succ i =>
    exfalso
    have := congrArg List.head? hred
    simp [encode, reduced] at this
    have := Bool.toNat_le (parity bs)
    omega

/-- Two big-endian bits encoding 0 or 1: the high bit is 0 and the low bit is the value. -/
theorem low_bit_of_two {l : List Bool} (hl : l.length = 2) {p : Bool} (h : toNatBE l = p.toNat) :
    l.getD 1 false = p := by
  match l, hl with
  | [a, c], _ =>
    simp only [toNatBE, List.length_cons, List.length_nil] at h
    cases a <;> cases c <;> cases p <;> simp_all

/-- Leaf substitution realising the two-bit encoding of (2, y_1, ..., y_m). -/
def parSubst (m : Nat) : Nat → Circ := fun j =>
  if j = 0 then const true
  else if j < 2 * (m + 1) then (if j % 2 = 1 ∧ 2 ≤ j then input (j / 2 - 1) else const false)
  else const false

theorem parSubst_leaf (m j : Nat) : IsLeaf (parSubst m j) := by
  unfold parSubst; split
  · simp [IsLeaf]
  · split
    · split <;> simp [IsLeaf]
    · simp [IsLeaf]

theorem parSubst_eval {m : Nat} {y : List Bool} (hy : y.length = m) (j : Nat) :
    eval (vfun y) (parSubst m j) = boardBits 2 (encode y) j := by
  unfold parSubst boardBits
  rw [length_encode, hy]
  by_cases h0 : j = 0
  · subst h0; simp [encode]; decide
  · simp only [h0, if_false]
    by_cases hj : j < 2 * (m + 1)
    · simp only [hj, if_true, show j < 2 * (m + 1) from hj]
      have hpos : 1 ≤ j / 2 ∨ j = 1 := by omega
      rcases hpos with hpos | h1
      · have hget : (encode y).getD (j / 2) 0 = (y.getD (j / 2 - 1) false).toNat := by
          simp only [encode, List.getD_eq_getElem?_getD]
          rw [show j / 2 = (j / 2 - 1) + 1 by omega, List.getElem?_cons_succ, List.getElem?_map]
          have : j / 2 - 1 < y.length := by rw [hy]; omega
          simp [List.getElem?_eq_getElem this]
        rw [hget]
        rcases Nat.mod_two_eq_zero_or_one j with hm | hm
        · have : ¬ (j % 2 = 1 ∧ 2 ≤ j) := by omega
          simp only [this, if_false, eval_const]
          first | rw [show 2 - 1 - j % 2 = 1 by omega] | skip
          cases y.getD (j / 2 - 1) false <;> rfl
        · have : j % 2 = 1 ∧ 2 ≤ j := ⟨hm, by omega⟩
          simp only [this, and_self, if_true, eval_input, vfun]
          first | rw [show 2 - 1 - j % 2 = 0 by omega] | skip
          cases y.getD (j / 2 - 1) false <;> rfl
      · subst h1; simp [encode]
    · simp [hj]

theorem parSubst_max (m j : Nat) : maxInput (parSubst m j) ≤ m := by
  unfold parSubst; split
  · simp
  · split
    · split
      · simp; omega
      · simp
    · simp

/-- The parity formula extracted from a selector: the low value bit, restricted to
    the encoded boards. -/
def parityFormula (S : BCirc) (m : Nat) : Circ := subst (parSubst m) (getC S.val 1)

/-- EXTRACTION THEOREM.  If a binary selector with BBound (depth ≤ d, size ≤ s,
    2 value bits) has strong mastery on 2-bit boards with m+1 heaps, then
    parityFormula S m computes parity of every y ∈ {0,1}^m, has depth ≤ d and size
    ≤ s, and reads only the m parity inputs. -/
theorem extraction {S : BCirc} {m r d s : Nat} (hb : BBound S (m + 1) 2 r d s)
    (hS : StrongMastery S (m + 1)) :
    (∀ y : List Bool, y.length = m → eval (vfun y) (parityFormula S m) = par y) ∧
    depth (parityFormula S m) ≤ d ∧ size (parityFormula S m) ≤ s ∧
    maxInput (parityFormula S m) ≤ m := by
  have hval1 : getC S.val 1 ∈ S.val := getC_mem (by rw [hb.val_len]; decide)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro y hy
    unfold parityFormula
    rw [eval_subst]
    have hz : (fun j => eval (vfun y) (parSubst m j)) = boardBits 2 (encode y) := by
      funext j; exact parSubst_eval hy j
    rw [hz]
    have hW : Win (encode y) := (win_iff _).2 (nimSum_encode_ne y)
    obtain ⟨i, v, x, hmove, hx, hlt, hlose⟩ :=
      hS (encode y) (by rw [length_encode, hy]) (encode_width y) hW
    have hz0 := (lose_iff _).1 hlose
    obtain ⟨_, hvp⟩ := winning_move_on_encode y hx hlt hz0
    -- read the value bits off the selector's output
    unfold binMove binReadoutOf at hmove
    split at hmove
    · split at hmove
      · simp only [Option.some.injEq, Prod.mk.injEq] at hmove
        obtain ⟨_, hvdef⟩ := hmove
        rw [hvp] at hvdef
        have hl : (S.val.map (eval (boardBits 2 (encode y)))).length = 2 := by simp [hb.val_len]
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

/-- The CLASSICAL HARDNESS STATEMENT for given depth, size and input length: no
    formula of depth ≤ d and size ≤ s reading m inputs computes parity of m bits. -/
def ParityHard (d s m : Nat) : Prop :=
  ∀ C : Circ, depth C ≤ d → size C ≤ s → maxInput C ≤ m →
    ∃ y ∈ bitvecs m, eval (vfun y) C ≠ par y

/-- SINGLE-FRAME BARRIER (circuit form).  Under ParityHard d s m, no binary selector
    with BBound (depth ≤ d, size ≤ s) has strong mastery on 2-bit boards with m+1
    heaps. -/
theorem no_small_strong_master {S : BCirc} {m r d s : Nat} (hb : BBound S (m + 1) 2 r d s)
    (hard : ParityHard d s m) : ¬ StrongMastery S (m + 1) := by
  intro hS
  obtain ⟨heval, hd, hs, hm⟩ := extraction hb hS
  obtain ⟨y, hy, hne⟩ := hard _ hd hs hm
  exact hne (heval y (mem_bitvecs_length hy))

/-! ## The correlation premise implies hardness -/

theorem rsum_odd (n : Nat) :
    rsum (bitvecs (n + 1)) (fun y => if par y then (1 : Rat) else 0) = (2 : Rat) ^ n := by
  have hsplit : ∀ k, rsum (bitvecs k) (fun y => if par y then (1 : Rat) else 0) +
      rsum (bitvecs k) (fun y => if par y then (0 : Rat) else 1) = (2 : Rat) ^ k := by
    intro k
    rw [← rsum_add, ← count_bitvecs k]
    apply rsum_congr; intro y _; cases par y <;> simp
  rw [rsum_bitvecs_succ]
  have e1 : rsum (bitvecs n) (fun v => if par (false :: v) then (1 : Rat) else 0) =
      rsum (bitvecs n) (fun y => if par y then (1 : Rat) else 0) := by
    apply rsum_congr; intro v _; simp [par]
  have e2 : rsum (bitvecs n) (fun v => if par (true :: v) then (1 : Rat) else 0) =
      rsum (bitvecs n) (fun y => if par y then (0 : Rat) else 1) := by
    apply rsum_congr; intro v _; cases h : par v <;> simp [par, h]
  rw [e1, e2, hsplit]

/-- A formula computing parity on m ≥ 1 inputs has correlation −1/2 with parity
    (in the premise's 0/1-indicator convention); so the premise with ε < 1/2
    implies ParityHard. -/
theorem hard_of_premise {d s m : Nat} {ε : Rat} (hm : 1 ≤ m) (hε : ε < 1 / 2)
    (h : ParityCorrPremise d s m ε) : ParityHard d s m := by
  intro C hd hs hmx
  by_cases hall : ∀ y ∈ bitvecs m, eval (vfun y) C = par y
  · exfalso
    obtain ⟨k1, _⟩ := h C hd hs hmx
    have e : rsum (bitvecs m) (fun y => ind (eval (vfun y) C) * sgn (par y)) =
        (-1) * rsum (bitvecs m) (fun y => if par y then (1 : Rat) else 0) := by
      rw [← rsum_mul_left]
      apply rsum_congr; intro y hy
      rw [hall y hy]; unfold ind sgn; cases par y <;> simp <;> grind
    obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
    rw [e, rsum_odd, Rat.pow_succ] at k1
    have hp := two_pow_pos' n
    have hp' : (2 : Rat) ^ n ≠ 0 := Rat.ne_of_gt hp
    have : (-1) * (2 : Rat) ^ n / ((2 : Rat) ^ n * 2) = -(1 / 2) := by grind
    rw [this] at k1
    grind
  · -- some y disagrees
    apply Classical.byContradiction
    intro hno
    apply hall
    intro y hy
    by_cases hq : eval (vfun y) C = par y
    · exact hq
    · exact absurd ⟨y, hy, hq⟩ hno

/-- SINGLE-FRAME BARRIER UNDER THE CORRELATION PREMISE: if the classical parity-
    correlation premise holds at depth d, size s, input length m ≥ 1 with ε < 1/2,
    no binary selector with BBound (d, s) has strong mastery on 2-bit boards with
    m + 1 heaps. -/
theorem no_strong_master_of_premise {S : BCirc} {m r d s : Nat} {ε : Rat}
    (hb : BBound S (m + 1) 2 r d s) (hm : 1 ≤ m) (hε : ε < 1 / 2)
    (h : ParityCorrPremise d s m ε) : ¬ StrongMastery S (m + 1) :=
  no_small_strong_master hb (hard_of_premise hm hε h)


/-! ## Axiom audit -/

#print axioms par_eq_parity
#print axioms length_encode
#print axioms encode_width
#print axioms winning_move_on_encode
#print axioms low_bit_of_two
#print axioms parSubst_leaf
#print axioms parSubst_eval
#print axioms parSubst_max
#print axioms extraction
#print axioms no_small_strong_master
#print axioms rsum_odd
#print axioms hard_of_premise
#print axioms no_strong_master_of_premise
end ParityCircuit
end NimAudit
