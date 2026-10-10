import Controller
import NimCorrBridge

/- Phase 4, Priority 3 (bit level): per-update circuits for the two-pass controller
   and their refinement.  Written by Claude (10 October 2026).  Lean 4.26.0, core/Std.

   State layout (B value bits, r counter bits; little-endian bit k at offset + k):
     mode 0 | acc 1.. | prev 1+B.. | valid 1+2B | sig 2+2B.. | idx 2+3B.. |
     selF 2+3B+r | selI 3+3B+r.. | selV 3+3B+2r.. | fnzF 3+4B+2r | fnzI 4+4B+2r.. |
     fnzV 4+4B+3r..   — 4 + 5B + 3r state bits;
   token bits: isRow 4+5B+3r, isReset 5+5B+3r, x 6+5B+3r.. .
   Each next-state bit and each output bit is an explicit formula of depth ≤ 8.
   REFINEMENT: decoding the evaluated next-state formulas gives exactly the semantic
   next state, and decoding the output formulas gives exactly the semantic output,
   for every state whose registers fit their fields (and no counter overflow). -/

namespace NimAudit
namespace ControllerBits

open Game Rollout Prob Attain Recurrent AC0 AC0.Circ Controller CorrBridge AttainCircuit

def optI : Option (Nat × Nat) → Nat
  | some m => m.1
  | none => 0

def optV : Option (Nat × Nat) → Nat
  | some m => m.2
  | none => 0

def tokRow : Tok → Bool
  | .row _ => true
  | _ => false

def tokRst : Tok → Bool
  | .reset => true
  | _ => false

def tokX : Tok → Nat
  | .row x => x
  | _ => 0

/-- The register layout, generic in the payload (bits or circuits). -/
def layout {α : Type} (B r : Nat) (dflt m : α) (acc prev : Nat → α) (valid : α) (sig idx : Nat → α)
    (selF : α) (selI selV : Nat → α) (fnzF : α) (fnzI fnzV : Nat → α) (j : Nat) : α :=
  if j = 0 then m
  else if j < 1 + B then acc (j - 1)
  else if j < 1 + 2 * B then prev (j - (1 + B))
  else if j = 1 + 2 * B then valid
  else if j < 2 + 3 * B then sig (j - (2 + 2 * B))
  else if j < 2 + 3 * B + r then idx (j - (2 + 3 * B))
  else if j = 2 + 3 * B + r then selF
  else if j < 3 + 3 * B + 2 * r then selI (j - (3 + 3 * B + r))
  else if j < 3 + 4 * B + 2 * r then selV (j - (3 + 3 * B + 2 * r))
  else if j = 3 + 4 * B + 2 * r then fnzF
  else if j < 4 + 4 * B + 3 * r then fnzI (j - (4 + 4 * B + 2 * r))
  else if j < 4 + 5 * B + 3 * r then fnzV (j - (4 + 4 * B + 3 * r))
  else dflt

theorem layout_map {α β : Type} (f : α → β) (B r : Nat) (d m : α) (acc prev : Nat → α) (valid : α)
    (sig idx : Nat → α) (selF : α) (selI selV : Nat → α) (fnzF : α) (fnzI fnzV : Nat → α) (j : Nat) :
    f (layout B r d m acc prev valid sig idx selF selI selV fnzF fnzI fnzV j) =
      layout B r (f d) (f m) (fun k => f (acc k)) (fun k => f (prev k)) (f valid) (fun k => f (sig k))
        (fun k => f (idx k)) (f selF) (fun k => f (selI k)) (fun k => f (selV k)) (f fnzF)
        (fun k => f (fnzI k)) (fun k => f (fnzV k)) j := by
  simp only [layout, apply_ite f]

theorem layout_congr {α : Type} {B r : Nat} {d m d' m' : α} {acc prev acc' prev' : Nat → α}
    {valid valid' : α} {sig idx sig' idx' : Nat → α} {selF selF' : α} {selI selV selI' selV' : Nat → α}
    {fnzF fnzF' : α} {fnzI fnzV fnzI' fnzV' : Nat → α}
    (hd : d = d') (hm : m = m') (hacc : ∀ k < B, acc k = acc' k) (hprev : ∀ k < B, prev k = prev' k)
    (hvalid : valid = valid') (hsig : ∀ k < B, sig k = sig' k) (hidx : ∀ q < r, idx q = idx' q)
    (hselF : selF = selF') (hselI : ∀ q < r, selI q = selI' q) (hselV : ∀ k < B, selV k = selV' k)
    (hfnzF : fnzF = fnzF') (hfnzI : ∀ q < r, fnzI q = fnzI' q) (hfnzV : ∀ k < B, fnzV k = fnzV' k)
    (j : Nat) :
    layout B r d m acc prev valid sig idx selF selI selV fnzF fnzI fnzV j =
      layout B r d' m' acc' prev' valid' sig' idx' selF' selI' selV' fnzF' fnzI' fnzV' j := by
  simp only [layout]
  by_cases h1 : j = 0
  · simp only [if_pos h1]; exact hm
  by_cases h2 : j < 1 + B
  · simp only [if_neg h1, if_pos h2]; exact hacc _ (by omega)
  by_cases h3 : j < 1 + 2 * B
  · simp only [if_neg h1, if_neg h2, if_pos h3]; exact hprev _ (by omega)
  by_cases h4 : j = 1 + 2 * B
  · simp only [if_neg h1, if_neg h2, if_neg h3, if_pos h4]; exact hvalid
  by_cases h5 : j < 2 + 3 * B
  · simp only [if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_pos h5]; exact hsig _ (by omega)
  by_cases h6 : j < 2 + 3 * B + r
  · simp only [if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_pos h6]; exact hidx _ (by omega)
  by_cases h7 : j = 2 + 3 * B + r
  · simp only [if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_neg h6, if_pos h7]; exact hselF
  by_cases h8 : j < 3 + 3 * B + 2 * r
  · simp only [if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_neg h6, if_neg h7, if_pos h8]; exact hselI _ (by omega)
  by_cases h9 : j < 3 + 4 * B + 2 * r
  · simp only [if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_neg h6, if_neg h7, if_neg h8, if_pos h9]; exact hselV _ (by omega)
  by_cases h10 : j = 3 + 4 * B + 2 * r
  · simp only [if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_neg h6, if_neg h7, if_neg h8, if_neg h9, if_pos h10]; exact hfnzF
  by_cases h11 : j < 4 + 4 * B + 3 * r
  · simp only [if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_neg h6, if_neg h7, if_neg h8, if_neg h9, if_neg h10, if_pos h11]; exact hfnzI _ (by omega)
  by_cases h12 : j < 4 + 5 * B + 3 * r
  · simp only [if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_neg h6, if_neg h7, if_neg h8, if_neg h9, if_neg h10, if_neg h11, if_pos h12]; exact hfnzV _ (by omega)
  simp only [if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_neg h6, if_neg h7, if_neg h8, if_neg h9, if_neg h10, if_neg h11, if_neg h12]; exact hd

/-- The canonical state vector (4 + 5B + 3r bits; false beyond). -/
def sbits (B r : Nat) (s : CState) : Nat → Bool :=
  layout B r false s.replayMode s.acc.testBit s.prev.testBit s.valid s.sig.testBit s.idx.testBit
    s.sel.isSome (optI s.sel).testBit (optV s.sel).testBit s.fnz.isSome (optI s.fnz).testBit
    (optV s.fnz).testBit

/-- Token wires. -/
def tbits (B r : Nat) (t : Tok) (j : Nat) : Bool :=
  if j = 4 + 5 * B + 3 * r then tokRow t
  else if j = 5 + 5 * B + 3 * r then tokRst t
  else (tokX t).testBit (j - (6 + 5 * B + 3 * r))

/-- The input vector of the per-update circuits: an arbitrary state vector v on the
    state wires, the token on the token wires. -/
def inp (B r : Nat) (v : Nat → Bool) (t : Tok) (j : Nat) : Bool :=
  if j < 4 + 5 * B + 3 * r then v j else tbits B r t j

/-- Canonical bit encoding of (state, token). -/
def enc (B r : Nat) (s : CState) (t : Tok) : Nat → Bool := inp B r (sbits B r s) t

section EncLemmas
variable (B r : Nat) (s : CState) (t : Tok)

theorem e_mode : enc B r s t 0 = s.replayMode := by
  simp (disch := omega) only [enc, inp, sbits, layout, if_pos, ↓reduceIte]
theorem e_acc {k : Nat} (hk : k < B) : enc B r s t (1 + k) = s.acc.testBit k := by
  simp (disch := omega) only [enc, inp, sbits, layout, tbits, if_neg, if_pos, ↓reduceIte]; congr 1; omega
theorem e_prev {k : Nat} (hk : k < B) : enc B r s t (1 + B + k) = s.prev.testBit k := by
  simp (disch := omega) only [enc, inp, sbits, layout, tbits, if_neg, if_pos, ↓reduceIte]; congr 1; omega
theorem e_valid : enc B r s t (1 + 2 * B) = s.valid := by
  simp (disch := omega) only [enc, inp, sbits, layout, tbits, if_neg, if_pos, ↓reduceIte]
theorem e_sig {k : Nat} (hk : k < B) : enc B r s t (2 + 2 * B + k) = s.sig.testBit k := by
  simp (disch := omega) only [enc, inp, sbits, layout, tbits, if_neg, if_pos, ↓reduceIte]; congr 1; omega
theorem e_idx {q : Nat} (hq : q < r) : enc B r s t (2 + 3 * B + q) = s.idx.testBit q := by
  simp (disch := omega) only [enc, inp, sbits, layout, tbits, if_neg, if_pos, ↓reduceIte]; congr 1; omega
theorem e_selF : enc B r s t (2 + 3 * B + r) = s.sel.isSome := by
  simp (disch := omega) only [enc, inp, sbits, layout, tbits, if_neg, if_pos, ↓reduceIte]
theorem e_selI {q : Nat} (hq : q < r) : enc B r s t (3 + 3 * B + r + q) = (optI s.sel).testBit q := by
  simp (disch := omega) only [enc, inp, sbits, layout, tbits, if_neg, if_pos, ↓reduceIte]; congr 1; omega
theorem e_selV {k : Nat} (hk : k < B) : enc B r s t (3 + 3 * B + 2 * r + k) = (optV s.sel).testBit k := by
  simp (disch := omega) only [enc, inp, sbits, layout, tbits, if_neg, if_pos, ↓reduceIte]; congr 1; omega
theorem e_fnzF : enc B r s t (3 + 4 * B + 2 * r) = s.fnz.isSome := by
  simp (disch := omega) only [enc, inp, sbits, layout, tbits, if_neg, if_pos, ↓reduceIte]
theorem e_fnzI {q : Nat} (hq : q < r) : enc B r s t (4 + 4 * B + 2 * r + q) = (optI s.fnz).testBit q := by
  simp (disch := omega) only [enc, inp, sbits, layout, tbits, if_neg, if_pos, ↓reduceIte]; congr 1; omega
theorem e_fnzV {k : Nat} (hk : k < B) : enc B r s t (4 + 4 * B + 3 * r + k) = (optV s.fnz).testBit k := by
  simp (disch := omega) only [enc, inp, sbits, layout, tbits, if_neg, if_pos, ↓reduceIte]; congr 1; omega
theorem e_row : enc B r s t (4 + 5 * B + 3 * r) = tokRow t := by
  simp (disch := omega) only [enc, inp, sbits, layout, tbits, if_neg, if_pos, ↓reduceIte]
theorem e_rst : enc B r s t (5 + 5 * B + 3 * r) = tokRst t := by
  simp (disch := omega) only [enc, inp, sbits, layout, tbits, if_neg, if_pos, ↓reduceIte]
theorem e_x (k : Nat) : enc B r s t (6 + 5 * B + 3 * r + k) = (tokX t).testBit k := by
  simp (disch := omega) only [enc, inp, sbits, layout, tbits, if_neg, if_pos, ↓reduceIte]; congr 1; omega

end EncLemmas

/-! ## Arithmetic facts -/

theorem testBit_succ : ∀ (q n : Nat),
    (n + 1).testBit q = xor (n.testBit q) (decide (∀ t < q, n.testBit t = true))
  | 0, n => by rw [testBit0_succ]; simp
  | q + 1, n => by
    rw [← Nat.testBit_div_two (n + 1) q, ← Nat.testBit_div_two n q]
    rcases Nat.mod_two_eq_zero_or_one n with h | h
    · rw [show (n + 1) / 2 = n / 2 by omega]
      have : ¬ ∀ t < q + 1, n.testBit t = true := by
        intro hall; have := hall 0 (by omega); simp [Nat.testBit_zero, h] at this
      simp [this]
    · rw [show (n + 1) / 2 = n / 2 + 1 by omega, testBit_succ q (n / 2)]
      congr 1
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_iff]
      constructor
      · intro hall t ht
        cases t with
        | zero => simp [Nat.testBit_zero, h]
        | succ t => rw [← Nat.testBit_div_two]; exact hall t (by omega)
      · intro hall t ht; rw [Nat.testBit_div_two]; exact hall (t + 1) (by omega)

theorem top_bit {σ k : Nat} (hσ0 : σ ≠ 0) (hk : σ.testBit k = true)
    (habove : ∀ k', k < k' → σ.testBit k' = false) : σ.log2 = k := by
  rw [Nat.log2_eq_iff hσ0]
  refine ⟨Nat.ge_two_pow_of_testBit hk, ?_⟩
  apply Nat.lt_pow_two_of_testBit
  intro i hi; exact habove i (by omega)

theorem canc_iff {σ x B : Nat} (hσ : σ < 2 ^ B) :
    (σ ≠ 0 ∧ x ^^^ σ < x) ↔ ∃ k < B, σ.testBit k = true ∧ x.testBit k = true ∧
      ∀ t < B - 1 - k, σ.testBit (k + 1 + t) = false := by
  have above : ∀ i, B ≤ i → σ.testBit i = false := fun i hi =>
    Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hσ (Nat.pow_le_pow_right (by decide) hi))
  constructor
  · rintro ⟨h0, hlt⟩
    have hx := (cancel_iff_bit h0).1 hlt
    have htop : σ.testBit σ.log2 = true := by
      cases hb : σ.testBit σ.log2 with
      | true => rfl
      | false =>
        exfalso
        have : σ < 2 ^ σ.log2 := by
          apply Nat.lt_pow_two_of_testBit
          intro i hi
          by_cases hik : i = σ.log2
          · subst hik; exact hb
          · exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le Nat.lt_log2_self
              (Nat.pow_le_pow_right (by decide) (by omega)))
        exact absurd (Nat.log2_self_le h0) (Nat.not_le.mpr this)
    have hkB : σ.log2 < B := by
      rcases Nat.lt_or_ge σ.log2 B with h | h
      · exact h
      · rw [above _ h] at htop; cases htop
    refine ⟨σ.log2, hkB, htop, hx, fun t _ => ?_⟩
    exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le Nat.lt_log2_self
      (Nat.pow_le_pow_right (by decide) (by omega)))
  · rintro ⟨k, hk, hσk, hxk, habove⟩
    have h0 : σ ≠ 0 := by intro h; subst h; simp at hσk
    have hlog : σ.log2 = k := by
      apply top_bit h0 hσk
      intro k' hk'
      rcases Nat.lt_or_ge k' B with h | h
      · have := habove (k' - k - 1) (by omega)
        rwa [show k + 1 + (k' - k - 1) = k' by omega] at this
      · exact above k' h
    refine ⟨h0, (cancel_iff_bit h0).2 ?_⟩
    rw [hlog]; exact hxk

theorem pos_iff_bitLE {x B : Nat} (hx : x < 2 ^ B) : 0 < x ↔ ∃ k < B, x.testBit k = true := by
  constructor
  · intro h
    obtain ⟨i, hi⟩ := Nat.exists_testBit_of_ne_zero (Nat.pos_iff_ne_zero.mp h)
    refine ⟨i, ?_, hi⟩
    rcases Nat.lt_or_ge i B with h' | h'
    · exact h'
    · rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) h'))] at hi
      cases hi
  · rintro ⟨k, _, hk⟩
    rcases Nat.eq_zero_or_pos x with h | h
    · subst h; simp at hk
    · exact h

/-! ## The circuits -/

section Circuits
variable (B r : Nat)

def Rc : Circ := input (5 + 5 * B + 3 * r)
def Wc : Circ := and [input (4 + 5 * B + 3 * r), not (input (5 + 5 * B + 3 * r))]
def Ec : Circ := and [not (input (4 + 5 * B + 3 * r)), not (input (5 + 5 * B + 3 * r))]
def Mc : Circ := input 0
def mux (c a b : Circ) : Circ := or [and [c, a], and [not c, b]]
def xI (k : Nat) : Circ := input (6 + 5 * B + 3 * r + k)

/-- σ ≠ 0 ∧ x XOR σ < x for the stored summary σ and the row x. -/
def cancC : Circ :=
  or ((List.range B).map (fun k => and ([input (2 + 2 * B + k), xI B r k] ++
    (List.range (B - 1 - k)).map (fun t => not (input (2 + 2 * B + (k + 1 + t)))))))

def nzC : Circ := or ((List.range B).map (fun k => xI B r k))

/-- Bit k of x − 1. -/
def decC (k : Nat) : Circ := xor2 (xI B r k) (and ((List.range k).map (fun t => not (xI B r t))))

/-- Bit q of idx + 1. -/
def incC (q : Nat) : Circ :=
  xor2 (input (2 + 3 * B + q)) (and ((List.range q).map (fun t => input (2 + 3 * B + t))))

def modeN : Circ := and [not (Rc B r), or [and [Wc B r, Mc], and [Ec B r, not Mc]]]
def accN (k : Nat) : Circ :=
  and [not (Rc B r), or [and [Wc B r, not Mc, xor2 (input (1 + k)) (xI B r k)],
    and [Wc B r, Mc, input (1 + k)], and [Ec B r, Mc, input (1 + k)]]]
def prevN (k : Nat) : Circ :=
  and [not (Rc B r), mux (and [Ec B r, not Mc]) (input (1 + k)) (input (1 + B + k))]
def validN : Circ := and [not (Rc B r), or [and [Ec B r, not Mc], input (1 + 2 * B)]]
def sigN (k : Nat) : Circ :=
  and [not (Rc B r), mux (and [Ec B r, not Mc]) (input (1 + k)) (input (2 + 2 * B + k))]
def idxN (q : Nat) : Circ := and [not (Rc B r), Wc B r, mux Mc (incC B q) (input (2 + 3 * B + q))]
def selFN : Circ := and [not (Rc B r), Wc B r, or [input (2 + 3 * B + r), and [Mc, cancC B r]]]
def selIN (q : Nat) : Circ :=
  and [not (Rc B r), Wc B r, or [and [input (2 + 3 * B + r), input (3 + 3 * B + r + q)],
    and [not (input (2 + 3 * B + r)), Mc, cancC B r, input (2 + 3 * B + q)]]]
def selVN (k : Nat) : Circ :=
  and [not (Rc B r), Wc B r, or [and [input (2 + 3 * B + r), input (3 + 3 * B + 2 * r + k)],
    and [not (input (2 + 3 * B + r)), Mc, cancC B r, xor2 (xI B r k) (input (2 + 2 * B + k))]]]
def fnzFN : Circ := and [not (Rc B r), Wc B r, or [input (3 + 4 * B + 2 * r), and [Mc, nzC B r]]]
def fnzIN (q : Nat) : Circ :=
  and [not (Rc B r), Wc B r, or [and [input (3 + 4 * B + 2 * r), input (4 + 4 * B + 2 * r + q)],
    and [not (input (3 + 4 * B + 2 * r)), Mc, nzC B r, input (2 + 3 * B + q)]]]
def fnzVN (k : Nat) : Circ :=
  and [not (Rc B r), Wc B r, or [and [input (3 + 4 * B + 2 * r), input (4 + 4 * B + 3 * r + k)],
    and [not (input (3 + 4 * B + 2 * r)), Mc, nzC B r, decC B r k]]]

/-- Output formulas. -/
def sumOutC : Circ := and [Ec B r, not Mc]
def sumBitC (k : Nat) : Circ := input (1 + k)
def diffBitC (k : Nat) : Circ := xor2 (input (1 + B + k)) (input (1 + k))
def diffValidC : Circ := input (1 + 2 * B)
def moveOutC : Circ := and [Ec B r, Mc]
def moveValidC : Circ := or [input (2 + 3 * B + r), input (3 + 4 * B + 2 * r)]
def moveIC (q : Nat) : Circ := mux (input (2 + 3 * B + r)) (input (3 + 3 * B + r + q)) (input (4 + 4 * B + 2 * r + q))
def moveVC (k : Nat) : Circ :=
  mux (input (2 + 3 * B + r)) (input (3 + 3 * B + 2 * r + k)) (input (4 + 4 * B + 3 * r + k))

end Circuits

/-- Decoded output from the evaluated output formulas. -/
def decodeOut (B r : Nat) (z : Nat → Bool) : Option COut :=
  if eval z (sumOutC B r) then
    some (COut.summary (ofBits B (fun k => eval z (sumBitC k)))
      (if eval z (diffValidC B) then some (ofBits B (fun k => eval z (diffBitC B k))) else none))
  else if eval z (moveOutC B r) then
    some (COut.move (if eval z (moveValidC B r) then
      some (ofBits r (fun q => eval z (moveIC B r q)), ofBits B (fun k => eval z (moveVC B r k))) else none))
  else none

/-! ## Evaluation of the arithmetic sub-circuits -/

section Eval
variable {B r : Nat} {s : CState} {t : Tok}

theorem ev_inc {q : Nat} (hq : q < r) : eval (enc B r s t) (incC B q) = (s.idx + 1).testBit q := by
  rw [incC, eval_xor2, testBit_succ, eval_input, e_idx B r s t hq]
  congr 1
  apply Bool.eq_iff_iff.mpr
  simp only [eval_and, List.all_map, List.all_eq_true, List.mem_range, Function.comp_apply, eval_input,
    decide_eq_true_iff]
  constructor
  · intro h u hu; rw [← e_idx B r s t (show u < r by omega)]; exact h u hu
  · intro h u hu; rw [e_idx B r s t (show u < r by omega)]; exact h u hu

theorem ev_canc (hσ : s.sig < 2 ^ B) :
    eval (enc B r s t) (cancC B r) = decide (s.sig ≠ 0 ∧ tokX t ^^^ s.sig < tokX t) := by
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_iff, canc_iff hσ]
  simp only [cancC, xI, eval_or, eval_and, eval_not, eval_input, List.any_map, List.all_append,
    List.all_cons, List.all_nil, List.all_map, List.any_eq_true, List.all_eq_true, List.mem_range,
    Function.comp_apply, Bool.and_eq_true, Bool.not_eq_true', e_x, Bool.and_true]
  constructor
  · rintro ⟨k, hk, ⟨h1, h2⟩, h3⟩
    refine ⟨k, hk, ?_, h2, fun u hu => ?_⟩
    · rwa [e_sig B r s t hk] at h1
    · have := h3 u hu; rwa [e_sig B r s t (show k + 1 + u < B by omega)] at this
  · rintro ⟨k, hk, h1, h2, h3⟩
    refine ⟨k, hk, ⟨?_, h2⟩, fun u hu => ?_⟩
    · rwa [e_sig B r s t hk]
    · rw [e_sig B r s t (show k + 1 + u < B by omega)]; exact h3 u hu

theorem ev_nz (hx : tokX t < 2 ^ B) : eval (enc B r s t) (nzC B r) = decide (0 < tokX t) := by
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_iff, pos_iff_bitLE hx]
  simp only [nzC, xI, eval_or, eval_input, List.any_map, List.any_eq_true, List.mem_range,
    Function.comp_apply, e_x]

theorem ev_dec (hx : 0 < tokX t) (k : Nat) : eval (enc B r s t) (decC B r k) = (tokX t - 1).testBit k := by
  rw [decC, eval_xor2, testBit_pred _ hx, xI, eval_input, e_x]
  congr 1
  apply Bool.eq_iff_iff.mpr
  simp only [eval_and, List.all_map, List.all_eq_true, List.mem_range, Function.comp_apply, eval_not,
    eval_input, xI, e_x, decide_eq_true_iff, Bool.not_eq_true']

end Eval

/-! ## Bit-level correctness of every next-state formula -/

section Fields
variable {B r : Nat} {s : CState} {t : Tok}

theorem f_mode : eval (enc B r s t) (modeN B r) = (cstep s t).1.replayMode := by
  cases t <;> cases hm : s.replayMode <;>
    simp [modeN, Rc, Wc, Ec, Mc, e_mode, e_row, e_rst, tokRow, tokRst, cstep, cinit, hm]

theorem f_acc {k : Nat} (hk : k < B) : eval (enc B r s t) (accN B r k) = (cstep s t).1.acc.testBit k := by
  cases t <;> cases hm : s.replayMode <;>
    simp [accN, Rc, Wc, Ec, Mc, xI, e_mode, e_row, e_rst, e_acc, e_x, hk, tokRow, tokRst, tokX, cstep,
      cinit, hm, eval_xor2, Nat.testBit_xor]

theorem f_prev {k : Nat} (hk : k < B) : eval (enc B r s t) (prevN B r k) = (cstep s t).1.prev.testBit k := by
  cases t <;> cases hm : s.replayMode <;>
    simp [prevN, mux, Rc, Wc, Ec, Mc, e_mode, e_row, e_rst, e_acc, e_prev, hk, tokRow, tokRst, cstep,
      cinit, hm]

theorem f_valid : eval (enc B r s t) (validN B r) = (cstep s t).1.valid := by
  cases t <;> cases hm : s.replayMode <;>
    simp [validN, Rc, Wc, Ec, Mc, e_mode, e_row, e_rst, e_valid, tokRow, tokRst, cstep, cinit, hm]

theorem f_sig {k : Nat} (hk : k < B) : eval (enc B r s t) (sigN B r k) = (cstep s t).1.sig.testBit k := by
  cases t <;> cases hm : s.replayMode <;>
    simp [sigN, mux, Rc, Wc, Ec, Mc, e_mode, e_row, e_rst, e_acc, e_sig, hk, tokRow, tokRst, cstep,
      cinit, hm]

theorem f_idx {q : Nat} (hq : q < r) : eval (enc B r s t) (idxN B r q) = (cstep s t).1.idx.testBit q := by
  cases t <;> cases hm : s.replayMode <;>
    simp [idxN, mux, Rc, Wc, Ec, Mc, e_mode, e_row, e_rst, e_idx, hq, ev_inc hq, tokRow, tokRst, cstep,
      cinit, hm, replayStep]

theorem f_selF (hσ : s.sig < 2 ^ B) : eval (enc B r s t) (selFN B r) = (cstep s t).1.sel.isSome := by
  cases t with
  | reset => simp [selFN, Rc, e_rst, tokRst, cstep, cinit]
  | sep => cases hm : s.replayMode <;> simp [selFN, Rc, Wc, e_rst, e_row, tokRst, tokRow, cstep, hm]
  | row x =>
    cases hm : s.replayMode <;> cases hs : s.sel <;>
      simp [selFN, Rc, Wc, Mc, e_rst, e_row, e_mode, e_selF, ev_canc hσ, tokRst, tokRow, tokX, cstep, hm, hs,
        replayStep] <;>
      (by_cases h1 : s.sig = 0 <;> by_cases h2 : x ^^^ s.sig < x <;> simp [h1, h2])

theorem f_selI {q : Nat} (hq : q < r) (hσ : s.sig < 2 ^ B) :
    eval (enc B r s t) (selIN B r q) = (optI (cstep s t).1.sel).testBit q := by
  cases t with
  | reset => simp [selIN, Rc, e_rst, tokRst, cstep, cinit, optI]
  | sep => cases hm : s.replayMode <;> simp [selIN, Rc, Wc, e_rst, e_row, tokRst, tokRow, cstep, hm, optI]
  | row x =>
    cases hm : s.replayMode <;> cases hs : s.sel <;>
      simp [selIN, Rc, Wc, Mc, e_rst, e_row, e_mode, e_selF, e_selI, e_idx, hq, ev_canc hσ, tokRst, tokRow,
        tokX, cstep, hm, hs, replayStep, optI] <;>
      (by_cases h1 : s.sig = 0 <;> by_cases h2 : x ^^^ s.sig < x <;> simp [h1, h2, optI])

theorem f_selV {k : Nat} (hk : k < B) (hσ : s.sig < 2 ^ B) :
    eval (enc B r s t) (selVN B r k) = (optV (cstep s t).1.sel).testBit k := by
  cases t with
  | reset => simp [selVN, Rc, e_rst, tokRst, cstep, cinit, optV]
  | sep => cases hm : s.replayMode <;> simp [selVN, Rc, Wc, e_rst, e_row, tokRst, tokRow, cstep, hm, optV]
  | row x =>
    cases hm : s.replayMode <;> cases hs : s.sel <;>
      simp [selVN, Rc, Wc, Mc, xI, e_rst, e_row, e_mode, e_selF, e_selV, e_sig, e_x, hk, ev_canc hσ, tokRst,
        tokRow, tokX, cstep, hm, hs, replayStep, optV, eval_xor2, Nat.testBit_xor] <;>
      (by_cases h1 : s.sig = 0 <;> by_cases h2 : x ^^^ s.sig < x <;> simp [h1, h2, optV, Nat.testBit_xor])

theorem f_fnzF (hx : tokX t < 2 ^ B) : eval (enc B r s t) (fnzFN B r) = (cstep s t).1.fnz.isSome := by
  cases t with
  | reset => simp [fnzFN, Rc, e_rst, tokRst, cstep, cinit]
  | sep => cases hm : s.replayMode <;> simp [fnzFN, Rc, Wc, e_rst, e_row, tokRst, tokRow, cstep, hm]
  | row x =>
    cases hm : s.replayMode <;> cases hs : s.fnz <;>
      simp [fnzFN, Rc, Wc, Mc, e_rst, e_row, e_mode, e_fnzF, ev_nz hx, tokRst, tokRow, tokX, cstep, hm, hs,
        replayStep] <;>
      (by_cases h1 : 0 < x <;> simp [h1])

theorem f_fnzI {q : Nat} (hq : q < r) (hx : tokX t < 2 ^ B) :
    eval (enc B r s t) (fnzIN B r q) = (optI (cstep s t).1.fnz).testBit q := by
  cases t with
  | reset => simp [fnzIN, Rc, e_rst, tokRst, cstep, cinit, optI]
  | sep => cases hm : s.replayMode <;> simp [fnzIN, Rc, Wc, e_rst, e_row, tokRst, tokRow, cstep, hm, optI]
  | row x =>
    cases hm : s.replayMode <;> cases hs : s.fnz <;>
      simp [fnzIN, Rc, Wc, Mc, e_rst, e_row, e_mode, e_fnzF, e_fnzI, e_idx, hq, ev_nz hx, tokRst, tokRow,
        tokX, cstep, hm, hs, replayStep, optI] <;>
      (by_cases h1 : 0 < x <;> simp [h1, optI])

theorem f_fnzV {k : Nat} (hk : k < B) (hx : tokX t < 2 ^ B) :
    eval (enc B r s t) (fnzVN B r k) = (optV (cstep s t).1.fnz).testBit k := by
  cases t with
  | reset => simp [fnzVN, Rc, e_rst, tokRst, cstep, cinit, optV]
  | sep => cases hm : s.replayMode <;> simp [fnzVN, Rc, Wc, e_rst, e_row, tokRst, tokRow, cstep, hm, optV]
  | row x =>
    by_cases hx0 : 0 < x
    · have hd := fun k => ev_dec (B := B) (r := r) (s := s) (t := Tok.row x) (by simpa [tokX] using hx0) k
      simp only [tokX] at hd
      cases hm : s.replayMode <;> cases hs : s.fnz <;>
        simp [fnzVN, Rc, Wc, Mc, e_rst, e_row, e_mode, e_fnzF, e_fnzV, hk, ev_nz hx, hd, hx0, tokRst, tokRow,
          tokX, cstep, hm, hs, replayStep, optV]
    · have hx0' : x = 0 := by omega
      subst hx0'
      cases hm : s.replayMode <;> cases hs : s.fnz <;>
        simp [fnzVN, Rc, Wc, Mc, e_rst, e_row, e_mode, e_fnzF, e_fnzV, hk, ev_nz hx, tokRst, tokRow,
          tokX, cstep, hm, hs, replayStep, optV]

end Fields

/-! ## The per-update circuit and its refinement -/

/-- The next-state circuit for wire j (constant false beyond the 4 + 5B + 3r state wires). -/
def nextC (B r : Nat) : Nat → Circ :=
  layout B r (const false) (modeN B r) (accN B r) (prevN B r) (validN B r) (sigN B r) (idxN B r)
    (selFN B r) (selIN B r) (selVN B r) (fnzFN B r) (fnzIN B r) (fnzVN B r)

/-- One update of the bit-level machine: evaluate the next-state circuits and the output
    circuits on (state vector, token). -/
def bstep (B r : Nat) (v : Nat → Bool) (t : Tok) : (Nat → Bool) × Option COut :=
  (fun j => eval (inp B r v t) (nextC B r j), decodeOut B r (inp B r v t))

/-- Field-width hypotheses needed for one exact update. -/
structure Decodable (B r : Nat) (s : CState) (t : Tok) : Prop where
  acc : s.acc < 2 ^ B
  prev : s.prev < 2 ^ B
  sig : s.sig < 2 ^ B
  sel : ∀ i v, s.sel = some (i, v) → i < 2 ^ r ∧ v < 2 ^ B
  fnz : ∀ i v, s.fnz = some (i, v) → i < 2 ^ r ∧ v < 2 ^ B
  tok : tokX t < 2 ^ B

section Refine
variable {B r : Nat} {s : CState} {t : Tok}

theorem step_state (hd : Decodable B r s t) :
    (fun j => eval (enc B r s t) (nextC B r j)) = sbits B r (cstep s t).1 := by
  funext j
  unfold nextC sbits
  rw [layout_map (eval (enc B r s t))]
  apply layout_congr
  · simp
  · exact f_mode
  · intro k hk; exact f_acc hk
  · intro k hk; exact f_prev hk
  · exact f_valid
  · intro k hk; exact f_sig hk
  · intro q hq; exact f_idx hq
  · exact f_selF hd.sig
  · intro q hq; exact f_selI hq hd.sig
  · intro k hk; exact f_selV hk hd.sig
  · exact f_fnzF hd.tok
  · intro q hq; exact f_fnzI hq hd.tok
  · intro k hk; exact f_fnzV hk hd.tok

theorem step_out (hd : Decodable B r s t) : decodeOut B r (enc B r s t) = (cstep s t).2 := by
  cases t with
  | reset => simp [decodeOut, sumOutC, moveOutC, Ec, Mc, e_row, e_rst, tokRow, tokRst, cstep]
  | row x =>
    cases hm : s.replayMode <;>
      simp [decodeOut, sumOutC, moveOutC, Ec, Mc, e_row, e_rst, tokRow, tokRst, cstep, hm]
  | sep =>
    have hA : ofBits B (fun k => eval (enc B r s Tok.sep) (sumBitC k)) = s.acc :=
      ofBits_testBit_eq hd.acc _ (fun k hk => by simp [sumBitC, e_acc, hk])
    have hD : ofBits B (fun k => eval (enc B r s Tok.sep) (diffBitC B k)) = s.prev ^^^ s.acc :=
      ofBits_testBit_eq (Nat.xor_lt_two_pow hd.prev hd.acc) _
        (fun k hk => by simp [diffBitC, eval_xor2, e_acc, e_prev, hk, Nat.testBit_xor])
    cases hm : s.replayMode
    · simp [decodeOut, sumOutC, Ec, Mc, e_mode, e_row, e_rst, tokRow, tokRst, cstep, hm, hA, hD,
        diffValidC, e_valid]
    · cases hs : s.sel with
      | some p =>
        obtain ⟨i, v⟩ := p
        have hb := hd.sel i v hs
        have hI : ofBits r (fun q => eval (enc B r s Tok.sep) (moveIC B r q)) = i :=
          ofBits_testBit_eq hb.1 _ (fun q hq => by simp [moveIC, mux, e_selF, e_selI, hq, hs, optI])
        have hV : ofBits B (fun k => eval (enc B r s Tok.sep) (moveVC B r k)) = v :=
          ofBits_testBit_eq hb.2 _ (fun k hk => by simp [moveVC, mux, e_selF, e_selV, hk, hs, optV])
        simp [decodeOut, sumOutC, moveOutC, moveValidC, Ec, Mc, e_mode, e_row, e_rst, e_selF, tokRow,
          tokRst, cstep, hm, hs, hI, hV, firstSome]
      | none =>
        cases hf : s.fnz with
        | none =>
          simp [decodeOut, sumOutC, moveOutC, moveValidC, Ec, Mc, e_mode, e_row, e_rst, e_selF, e_fnzF,
            tokRow, tokRst, cstep, hm, hs, hf, firstSome]
        | some p =>
          obtain ⟨i, v⟩ := p
          have hb := hd.fnz i v hf
          have hI : ofBits r (fun q => eval (enc B r s Tok.sep) (moveIC B r q)) = i :=
            ofBits_testBit_eq hb.1 _ (fun q hq => by simp [moveIC, mux, e_selF, e_fnzI, hq, hs, hf, optI])
          have hV : ofBits B (fun k => eval (enc B r s Tok.sep) (moveVC B r k)) = v :=
            ofBits_testBit_eq hb.2 _ (fun k hk => by simp [moveVC, mux, e_selF, e_fnzV, hk, hs, hf, optV])
          simp [decodeOut, sumOutC, moveOutC, moveValidC, Ec, Mc, e_mode, e_row, e_rst, e_selF, e_fnzF,
            tokRow, tokRst, cstep, hm, hs, hf, hI, hV, firstSome]

/-- ONE-STEP REFINEMENT: on the canonical encoding of a state, one evaluation of the
    per-update circuits yields the canonical encoding of the semantic successor state and
    (after decoding the output wires) exactly the semantic output. -/
theorem step_refines (hd : Decodable B r s t) :
    bstep B r (sbits B r s) t = (sbits B r (cstep s t).1, (cstep s t).2) := by
  show ((fun j => eval (enc B r s t) (nextC B r j)), decodeOut B r (enc B r s t)) = _
  rw [step_state hd, step_out hd]

end Refine

/-! ## Lossless decoding of the state vector -/

def decodeS (B r : Nat) (v : Nat → Bool) : CState :=
  ⟨v 0, ofBits B (fun k => v (1 + k)), ofBits B (fun k => v (1 + B + k)), v (1 + 2 * B),
   ofBits B (fun k => v (2 + 2 * B + k)), ofBits r (fun q => v (2 + 3 * B + q)),
   if v (2 + 3 * B + r) then
     some (ofBits r (fun q => v (3 + 3 * B + r + q)), ofBits B (fun k => v (3 + 3 * B + 2 * r + k)))
   else none,
   if v (3 + 4 * B + 2 * r) then
     some (ofBits r (fun q => v (4 + 4 * B + 2 * r + q)), ofBits B (fun k => v (4 + 4 * B + 3 * r + k)))
   else none⟩

/-- All registers fit their B-bit and r-bit fields. -/
structure FitsR (B r : Nat) (s : CState) : Prop where
  acc : s.acc < 2 ^ B
  prev : s.prev < 2 ^ B
  sig : s.sig < 2 ^ B
  idx : s.idx < 2 ^ r
  sel : ∀ i v, s.sel = some (i, v) → i < 2 ^ r ∧ v < 2 ^ B
  fnz : ∀ i v, s.fnz = some (i, v) → i < 2 ^ r ∧ v < 2 ^ B

/-- LOSSLESS: the 4 + 5B + 3r state wires determine the semantic state exactly. -/
theorem decodeS_sbits {B r : Nat} {s : CState} (h : FitsR B r s) : decodeS B r (sbits B r s) = s := by
  have es : ∀ j, j < 4 + 5 * B + 3 * r → sbits B r s j = enc B r s Tok.sep j := fun j hj => by
    simp [enc, inp, hj]
  have hm : sbits B r s 0 = s.replayMode := by rw [es 0 (by omega)]; exact e_mode B r s _
  have ha : ofBits B (fun k => sbits B r s (1 + k)) = s.acc :=
    ofBits_testBit_eq h.acc _ (fun k hk => by rw [es (1 + k) (by omega)]; exact e_acc B r s _ hk)
  have hp : ofBits B (fun k => sbits B r s (1 + B + k)) = s.prev :=
    ofBits_testBit_eq h.prev _ (fun k hk => by rw [es (1 + B + k) (by omega)]; exact e_prev B r s _ hk)
  have hv : sbits B r s (1 + 2 * B) = s.valid := by rw [es (1 + 2 * B) (by omega)]; exact e_valid B r s _
  have hg : ofBits B (fun k => sbits B r s (2 + 2 * B + k)) = s.sig :=
    ofBits_testBit_eq h.sig _ (fun k hk => by rw [es (2 + 2 * B + k) (by omega)]; exact e_sig B r s _ hk)
  have hi : ofBits r (fun q => sbits B r s (2 + 3 * B + q)) = s.idx :=
    ofBits_testBit_eq h.idx _ (fun q hq => by rw [es (2 + 3 * B + q) (by omega)]; exact e_idx B r s _ hq)
  have hsel : (if sbits B r s (2 + 3 * B + r) then
      some (ofBits r (fun q => sbits B r s (3 + 3 * B + r + q)),
        ofBits B (fun k => sbits B r s (3 + 3 * B + 2 * r + k))) else none) = s.sel := by
    rw [es (2 + 3 * B + r) (by omega), e_selF]
    cases hs : s.sel with
    | none => rfl
    | some p =>
      obtain ⟨i, v⟩ := p
      obtain ⟨hi', hv'⟩ := h.sel i v hs
      simp only [Option.isSome_some, if_true]
      rw [ofBits_testBit_eq hi' _ (fun q hq => by
            rw [es (3 + 3 * B + r + q) (by omega), e_selI B r s _ hq, hs]; rfl),
          ofBits_testBit_eq hv' _ (fun k hk => by
            rw [es (3 + 3 * B + 2 * r + k) (by omega), e_selV B r s _ hk, hs]; rfl)]
  have hfnz : (if sbits B r s (3 + 4 * B + 2 * r) then
      some (ofBits r (fun q => sbits B r s (4 + 4 * B + 2 * r + q)),
        ofBits B (fun k => sbits B r s (4 + 4 * B + 3 * r + k))) else none) = s.fnz := by
    rw [es (3 + 4 * B + 2 * r) (by omega), e_fnzF]
    cases hs : s.fnz with
    | none => rfl
    | some p =>
      obtain ⟨i, v⟩ := p
      obtain ⟨hi', hv'⟩ := h.fnz i v hs
      simp only [Option.isSome_some, if_true]
      rw [ofBits_testBit_eq hi' _ (fun q hq => by
            rw [es (4 + 4 * B + 2 * r + q) (by omega), e_fnzI B r s _ hq, hs]; rfl),
          ofBits_testBit_eq hv' _ (fun k hk => by
            rw [es (4 + 4 * B + 3 * r + k) (by omega), e_fnzV B r s _ hk, hs]; rfl)]
  simp only [decodeS]
  rw [hm, ha, hp, hv, hg, hi, hsel, hfnz]

/-! ## Runs of the bit-level machine -/

def brun (B r : Nat) : (Nat → Bool) → List Tok → (Nat → Bool) × List COut
  | v, [] => (v, [])
  | v, t :: ts => ((brun B r (bstep B r v t).1 ts).1, (bstep B r v t).2.toList ++ (brun B r (bstep B r v t).1 ts).2)

theorem brun_append (B r : Nat) (v : Nat → Bool) (ts us : List Tok) :
    brun B r v (ts ++ us) =
      ((brun B r (brun B r v ts).1 us).1, (brun B r v ts).2 ++ (brun B r (brun B r v ts).1 us).2) := by
  induction ts generalizing v with
  | nil => simp [brun]
  | cons t ts ih => simp only [List.cons_append, brun, ih, List.append_assoc]

/-- Every visited (state, token) pair satisfies the one-step width hypotheses. -/
def AllDec (B r : Nat) : CState → List Tok → Prop
  | _, [] => True
  | s, t :: ts => Decodable B r s t ∧ AllDec B r (cstep s t).1 ts

/-- RUN REFINEMENT: started on the canonical encoding of s, the bit-level machine tracks
    the semantic controller exactly along the whole token stream. -/
theorem brun_refines {B r : Nat} : ∀ (s : CState) (ts : List Tok), AllDec B r s ts →
    brun B r (sbits B r s) ts = (sbits B r (crun s ts).1, (crun s ts).2)
  | s, [], _ => rfl
  | s, t :: ts, ⟨hd, hrest⟩ => by
    simp only [brun, crun]
    rw [step_refines hd, brun_refines _ ts hrest]

theorem self_mem_crunStates (s : CState) (ts : List Tok) : s ∈ crunStates s ts := by
  cases ts <;> simp [crunStates]

theorem allDec_of_fits {B r N : Nat} (hN : N < 2 ^ r) : ∀ (s : CState) (ts : List Tok),
    (∀ st ∈ crunStates s ts, Fits B N st) → (∀ t ∈ ts, tokX t < 2 ^ B) → AllDec B r s ts
  | _, [], _, _ => trivial
  | s, t :: ts, hf, ht => by
    have hs : Fits B N s := hf s (by simp [crunStates])
    obtain ⟨h1, h2, h3, _, h5, h6⟩ := hs
    refine ⟨⟨h1, h2, h3, fun i v hiv => ?_, fun i v hiv => ?_, ht t (by simp)⟩,
      allDec_of_fits hN _ ts (fun st hst => hf st (by simp [crunStates, hst]))
        (fun t' ht' => ht t' (by simp [ht']))⟩
    · obtain ⟨a, b⟩ := h5 i v hiv; exact ⟨by omega, b⟩
    · obtain ⟨a, b⟩ := h6 i v hiv; exact ⟨by omega, b⟩

theorem tok_bound_stream {B : Nat} (Ps : List (List Nat)) (hP : ∀ P ∈ Ps, Width B P) :
    ∀ t ∈ stream Ps, tokX t < 2 ^ B := by
  intro t ht
  simp only [stream, List.mem_flatMap, dtoks, List.mem_append, List.mem_map, List.mem_singleton] at ht
  obtain ⟨P, hP', hm⟩ := ht
  rcases hm with ((⟨x, hx, rfl⟩ | rfl) | ⟨x, hx, rfl⟩) | rfl
  · exact hP P hP' x hx
  · exact Nat.two_pow_pos B
  · exact hP P hP' x hx
  · exact Nat.two_pow_pos B

/-- STREAM THEOREM (bit level): on any well-formed stream of N-heap, B-bit boards with
    N < 2^r, the bit-level machine started in the all-zero vector (the encoding of the
    initial state) produces exactly the semantic outputs: for each board, the summary
    (with the difference to the previous summary) and the replay move. -/
theorem bits_stream {B r N : Nat} (hN : N < 2 ^ r) (Ps : List (List Nat))
    (hP : ∀ P ∈ Ps, P.length = N ∧ Width B P) :
    (brun B r (sbits B r cinit) (stream Ps)).2 = ctrlOuts false 0 Ps := by
  have hfit : Fits B N cinit := by
    refine ⟨Nat.two_pow_pos B, Nat.two_pow_pos B, Nat.two_pow_pos B, Nat.zero_le _, ?_, ?_⟩ <;>
      simp [cinit]
  have hall := allDec_of_fits (B := B) hN cinit (stream Ps) (stream_fits cinit cinit_idle hfit Ps hP)
    (tok_bound_stream Ps (fun P h => (hP P h).2))
  rw [brun_refines _ _ hall, (crun_stream cinit cinit_idle Ps).1]
  rfl

/-! ## Reset from an arbitrary vector, and streams of games -/

theorem inp_row (B r : Nat) (v : Nat → Bool) (t : Tok) : inp B r v t (4 + 5 * B + 3 * r) = tokRow t := by
  simp (disch := omega) only [inp, tbits, if_neg, if_pos, ↓reduceIte]
theorem inp_rst (B r : Nat) (v : Nat → Bool) (t : Tok) : inp B r v t (5 + 5 * B + 3 * r) = tokRst t := by
  simp (disch := omega) only [inp, tbits, if_neg, if_pos, ↓reduceIte]

/-- RESET: from ANY state vector whatsoever (not necessarily a valid encoding), a reset
    token produces the all-zero encoding of the initial state and no output. -/
theorem bstep_reset (B r : Nat) (v : Nat → Bool) : bstep B r v Tok.reset = (sbits B r cinit, none) := by
  have h1 : (fun j => eval (inp B r v Tok.reset) (nextC B r j)) = sbits B r cinit := by
    funext j
    unfold nextC sbits
    rw [layout_map (eval (inp B r v Tok.reset))]
    apply layout_congr <;> intros <;>
      simp [modeN, accN, prevN, validN, sigN, idxN, selFN, selIN, selVN, fnzFN, fnzIN, fnzVN, Rc,
        inp_rst, tokRst, cinit, optI, optV]
  have h2 : decodeOut B r (inp B r v Tok.reset) = none := by
    simp [decodeOut, sumOutC, moveOutC, Ec, inp_row, inp_rst, tokRow, tokRst]
  show ((fun j => eval (inp B r v Tok.reset) (nextC B r j)), decodeOut B r (inp B r v Tok.reset)) = _
  rw [h1, h2]

/-- GAMES THEOREM (bit level): from an ARBITRARY initial state vector, a stream of games,
    each preceded by a reset and each consisting of well-formed boards with some number
    N < 2^r of heaps, yields game by game exactly the outputs of a fresh controller. -/
theorem bits_games (B r : Nat) (v : Nat → Bool) (gs : List (List (List Nat)))
    (h : ∀ g ∈ gs, ∃ N, N < 2 ^ r ∧ ∀ P ∈ g, P.length = N ∧ Width B P) :
    (brun B r v (gameStream gs)).2 = gs.flatMap (ctrlOuts false 0) := by
  induction gs generalizing v with
  | nil => rfl
  | cons g gs ih =>
    have e : gameStream (g :: gs) = (Tok.reset :: stream g) ++ gameStream gs := by simp [gameStream]
    have h1 : brun B r v (Tok.reset :: stream g) = brun B r (sbits B r cinit) (stream g) := by
      simp only [brun, bstep_reset, Option.toList, List.nil_append]
    obtain ⟨N, hN, hg⟩ := h g (by simp)
    rw [e, brun_append, h1, List.flatMap_cons, bits_stream hN g hg,
      ih _ (fun g' hg' => h g' (by simp [hg']))]

/-- LOSSLESS ON REACHABLE STATES: along a well-formed stream every reachable semantic
    state fits the fields (counter included: idx ≤ N < 2^r, so no overflow) and is
    recovered exactly from its 4 + 5B + 3r state bits. -/
theorem reachable_lossless {B r N : Nat} (hN : N < 2 ^ r) (Ps : List (List Nat))
    (hP : ∀ P ∈ Ps, P.length = N ∧ Width B P) :
    ∀ st ∈ crunStates cinit (stream Ps), FitsR B r st ∧ decodeS B r (sbits B r st) = st := by
  have hfit : Fits B N cinit := by
    refine ⟨Nat.two_pow_pos B, Nat.two_pow_pos B, Nat.two_pow_pos B, Nat.zero_le _, ?_, ?_⟩ <;>
      simp [cinit]
  intro st hst
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := stream_fits cinit cinit_idle hfit Ps hP st hst
  have hr : FitsR B r st := ⟨h1, h2, h3, by omega, fun i v hiv => ⟨by have := (h5 i v hiv).1; omega,
    (h5 i v hiv).2⟩, fun i v hiv => ⟨by have := (h6 i v hiv).1; omega, (h6 i v hiv).2⟩⟩
  exact ⟨hr, decodeS_sbits hr⟩

/-- Logical update counts: one circuit evaluation per token; a decision on an N-heap board
    takes exactly 2N + 2 updates, a stream of D such boards D(2N + 2). -/
theorem dtoks_length (P : List Nat) : (dtoks P).length = 2 * P.length + 2 := by
  simp [dtoks]; omega

theorem stream_length {N : Nat} (Ps : List (List Nat)) (hP : ∀ P ∈ Ps, P.length = N) :
    (stream Ps).length = Ps.length * (2 * N + 2) := by
  induction Ps with
  | nil => simp [stream]
  | cons P Ps ih =>
    have e : stream (P :: Ps) = dtoks P ++ stream Ps := by simp [stream]
    rw [e, List.length_append, dtoks_length, hP P (by simp), ih (fun Q hQ => hP Q (by simp [hQ])),
      List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

theorem brun_length (B r : Nat) (v : Nat → Bool) : ∀ ts : List Tok,
    (brun B r v ts).2.length ≤ ts.length := by
  intro ts
  induction ts generalizing v with
  | nil => simp [brun]
  | cons t ts ih =>
    simp only [brun, List.length_append, List.length_cons]
    have := ih (bstep B r v t).1
    cases (bstep B r v t).2 <;> simp [Option.toList] <;> omega

/-- ONE BOARD (bit level): from the all-zero vector, the 2N + 2 updates for a board P
    with N < 2^r heaps of B bits output the summary and then `decisionMove P`, which by
    `Controller.decision_correct` is legal, reaches nim-sum 0 from every nonzero position,
    and is `none` exactly on terminal boards. -/
theorem bits_one_board {B r : Nat} (P : List Nat) (hN : P.length < 2 ^ r) (hw : Width B P) :
    (brun B r (sbits B r cinit) (dtoks P)).2 = [COut.summary (nimSum P) none, COut.move (decisionMove P)] := by
  have h := bits_stream (B := B) hN [P] (by simp [hw])
  simpa [stream, ctrlOuts, decisionMove] using h

/-! ## Memory and resource bounds -/

/-- Number of state wires. -/
def stateWidth (B r : Nat) : Nat := 4 + 5 * B + 3 * r

theorem sbits_beyond (B r : Nat) (s : CState) (j : Nat) (hj : stateWidth B r ≤ j) : sbits B r s j = false := by
  unfold stateWidth at hj
  simp (disch := omega) only [sbits, layout, if_neg]

theorem nextC_beyond (B r : Nat) (j : Nat) (hj : stateWidth B r ≤ j) : nextC B r j = const false := by
  unfold stateWidth at hj
  simp (disch := omega) only [nextC, layout, if_neg]

/-- With r = log₂N + 1 the counter never overflows; memory is 7 + 5B + 3·log₂N bits. -/
theorem counter_width (N : Nat) : N < 2 ^ (N.log2 + 1) ∧ stateWidth B (N.log2 + 1) = 7 + 5 * B + 3 * N.log2 := by
  refine ⟨Nat.lt_log2_self, ?_⟩
  unfold stateWidth; omega

theorem layout_forall {α : Type} (P : α → Prop) {B r : Nat} {d m : α} {acc prev : Nat → α}
    {valid : α} {sig idx : Nat → α} {selF : α} {selI selV : Nat → α} {fnzF : α} {fnzI fnzV : Nat → α}
    (hd : P d) (hm : P m) (hacc : ∀ k < B, P (acc k)) (hprev : ∀ k < B, P (prev k))
    (hvalid : P valid) (hsig : ∀ k < B, P (sig k)) (hidx : ∀ q < r, P (idx q))
    (hselF : P selF) (hselI : ∀ q < r, P (selI q)) (hselV : ∀ k < B, P (selV k))
    (hfnzF : P fnzF) (hfnzI : ∀ q < r, P (fnzI q)) (hfnzV : ∀ k < B, P (fnzV k)) (j : Nat) :
    P (layout B r d m acc prev valid sig idx selF selI selV fnzF fnzI fnzV j) := by
  simp only [layout]
  by_cases h1 : j = 0
  · simp only [if_pos h1]; exact hm
  by_cases h2 : j < 1 + B
  · simp only [if_neg h1, if_pos h2]; exact hacc _ (by omega)
  by_cases h3 : j < 1 + 2 * B
  · simp only [if_neg h1, if_neg h2, if_pos h3]; exact hprev _ (by omega)
  by_cases h4 : j = 1 + 2 * B
  · simp only [if_neg h1, if_neg h2, if_neg h3, if_pos h4]; exact hvalid
  by_cases h5 : j < 2 + 3 * B
  · simp only [if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_pos h5]; exact hsig _ (by omega)
  by_cases h6 : j < 2 + 3 * B + r
  · simp only [if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_pos h6]; exact hidx _ (by omega)
  by_cases h7 : j = 2 + 3 * B + r
  · simp only [if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_neg h6, if_pos h7]; exact hselF
  by_cases h8 : j < 3 + 3 * B + 2 * r
  · simp only [if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_neg h6, if_neg h7, if_pos h8]; exact hselI _ (by omega)
  by_cases h9 : j < 3 + 4 * B + 2 * r
  · simp only [if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_neg h6, if_neg h7, if_neg h8, if_pos h9]; exact hselV _ (by omega)
  by_cases h10 : j = 3 + 4 * B + 2 * r
  · simp only [if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_neg h6, if_neg h7, if_neg h8, if_neg h9, if_pos h10]; exact hfnzF
  by_cases h11 : j < 4 + 4 * B + 3 * r
  · simp only [if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_neg h6, if_neg h7, if_neg h8, if_neg h9, if_neg h10, if_pos h11]; exact hfnzI _ (by omega)
  by_cases h12 : j < 4 + 5 * B + 3 * r
  · simp only [if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_neg h6, if_neg h7, if_neg h8, if_neg h9, if_neg h10, if_neg h11, if_pos h12]; exact hfnzV _ (by omega)
  simp only [if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_neg h6, if_neg h7, if_neg h8, if_neg h9, if_neg h10, if_neg h11, if_neg h12]; exact hd

section Resources
open AC0.Circ

theorem size_and_le' {cs : List Circ} {S : Nat} (h : ∀ c ∈ cs, size c ≤ S) :
    size (and cs) ≤ cs.length * S + 1 := by
  simp only [size_and]; have := sum_le_len_mul h; omega

theorem size_or_le' {cs : List Circ} {S : Nat} (h : ∀ c ∈ cs, size c ≤ S) :
    size (or cs) ≤ cs.length * S + 1 := by
  simp only [size_or]; have := sum_le_len_mul h; omega

theorem maxInput_and_le {cs : List Circ} {M : Nat} (h : ∀ c ∈ cs, maxInput c ≤ M) :
    maxInput (and cs) ≤ M := by
  simp only [maxInput_and]; apply listMax_le; intro a ha
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ha; exact h c hc

theorem maxInput_or_le {cs : List Circ} {M : Nat} (h : ∀ c ∈ cs, maxInput c ≤ M) :
    maxInput (or cs) ≤ M := by
  simp only [maxInput_or]; apply listMax_le; intro a ha
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ha; exact h c hc

def cancSize (B : Nat) : Nat := B * (2 * B + 3) + 1

variable (B r : Nat)

theorem size_cancC : size (cancC B r) ≤ cancSize B := by
  unfold cancC cancSize
  have := size_or_le' (S := 2 * B + 3) (cs := (List.range B).map (fun k => and ([input (2 + 2 * B + k), xI B r k] ++
    (List.range (B - 1 - k)).map (fun t => not (input (2 + 2 * B + (k + 1 + t))))))) (by
      intro c hc
      obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hc
      have hk' := List.mem_range.mp hk
      have h2 := size_and_le' (S := 2) (cs := [input (2 + 2 * B + k), xI B r k] ++
        (List.range (B - 1 - k)).map (fun t => not (input (2 + 2 * B + (k + 1 + t))))) (by
          intro c hc
          simp only [List.mem_append, List.mem_cons, List.mem_map, List.mem_range] at hc
          rcases hc with (rfl | rfl | h) | ⟨t, _, rfl⟩
          · simp
          · simp [xI]
          · simp at h
          · simp)
      simp only [List.length_append, List.length_cons, List.length_nil, List.length_map,
        List.length_range] at h2
      have : (B - 1 - k + 2) * 2 + 1 ≤ 2 * B + 3 := by omega
      omega)
  simpa using this

theorem depth_cancC : depth (cancC B r) ≤ 3 := by
  unfold cancC
  apply depth_or_le; intro c hc
  obtain ⟨k, _, rfl⟩ := List.mem_map.mp hc
  apply depth_and_le; intro c hc
  simp only [List.mem_append, List.mem_cons, List.mem_map, List.mem_range] at hc
  rcases hc with (rfl | rfl | h) | ⟨t, _, rfl⟩
  · simp
  · simp [xI]
  · simp at h
  · simp

theorem max_cancC : maxInput (cancC B r) ≤ 6 + 6 * B + 3 * r := by
  unfold cancC
  apply maxInput_or_le; intro c hc
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hc
  have hk' := List.mem_range.mp hk
  apply maxInput_and_le; intro c hc
  simp only [List.mem_append, List.mem_cons, List.mem_map, List.mem_range] at hc
  rcases hc with (rfl | rfl | h) | ⟨t, ht, rfl⟩
  · simp; omega
  · simp [xI]; omega
  · simp at h
  · simp; omega

theorem size_nzC : size (nzC B r) ≤ B + 1 := by
  unfold nzC
  have := size_or_le' (S := 1) (cs := (List.range B).map (fun k => xI B r k)) (by
    intro c hc; obtain ⟨k, _, rfl⟩ := List.mem_map.mp hc; simp [xI])
  simpa using this

theorem depth_nzC : depth (nzC B r) ≤ 1 := by
  unfold nzC; apply depth_or_le; intro c hc; obtain ⟨k, _, rfl⟩ := List.mem_map.mp hc; simp [xI]

theorem max_nzC : maxInput (nzC B r) ≤ 6 + 6 * B + 3 * r := by
  unfold nzC; apply maxInput_or_le; intro c hc; obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hc
  have := List.mem_range.mp hk; simp [xI]; omega

theorem size_decC (k : Nat) : size (decC B r k) ≤ 4 * k + 9 := by
  unfold decC xor2
  have := size_and_le' (S := 2) (cs := (List.range k).map (fun t => not (xI B r t))) (by
    intro c hc; obtain ⟨t, _, rfl⟩ := List.mem_map.mp hc; simp [xI])
  simp only [List.length_map, List.length_range] at this
  generalize and ((List.range k).map (fun t => not (xI B r t))) = A at this ⊢
  simp only [size_or, size_and, size_not, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, xI,
    size_input]
  omega

theorem depth_decC (k : Nat) : depth (decC B r k) ≤ 5 := by
  unfold decC xor2
  have h : depth (and ((List.range k).map (fun t => not (xI B r t)))) ≤ 2 := by
    apply depth_and_le; intro c hc; obtain ⟨t, _, rfl⟩ := List.mem_map.mp hc; simp [xI]
  generalize and ((List.range k).map (fun t => not (xI B r t))) = A at h ⊢
  simp only [depth_or, depth_and, depth_not, List.map_cons, List.map_nil, listMax, List.foldr_cons,
    List.foldr_nil, xI, depth_input]
  omega

theorem max_decC {k : Nat} (hk : k < B) : maxInput (decC B r k) ≤ 6 + 6 * B + 3 * r := by
  unfold decC xor2
  have h : maxInput (and ((List.range k).map (fun t => not (xI B r t)))) ≤ 6 + 6 * B + 3 * r := by
    apply maxInput_and_le; intro c hc; obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hc
    have := List.mem_range.mp ht; simp [xI]; omega
  generalize and ((List.range k).map (fun t => not (xI B r t))) = A at h ⊢
  simp only [maxInput_or, maxInput_and, maxInput_not, List.map_cons, List.map_nil, listMax,
    List.foldr_cons, List.foldr_nil, xI, maxInput_input]
  omega

theorem size_incC (q : Nat) : size (incC B q) ≤ 2 * q + 9 := by
  unfold incC xor2
  have := size_and_le' (S := 1) (cs := (List.range q).map (fun t => input (2 + 3 * B + t))) (by
    intro c hc; obtain ⟨t, _, rfl⟩ := List.mem_map.mp hc; simp)
  simp only [List.length_map, List.length_range] at this
  generalize and ((List.range q).map (fun t => input (2 + 3 * B + t))) = A at this ⊢
  simp only [size_or, size_and, size_not, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    size_input]
  omega

theorem depth_incC (q : Nat) : depth (incC B q) ≤ 5 := by
  unfold incC xor2
  have h : depth (and ((List.range q).map (fun t => input (2 + 3 * B + t)))) ≤ 1 := by
    apply depth_and_le; intro c hc; obtain ⟨t, _, rfl⟩ := List.mem_map.mp hc; simp
  generalize and ((List.range q).map (fun t => input (2 + 3 * B + t))) = A at h ⊢
  simp only [depth_or, depth_and, depth_not, List.map_cons, List.map_nil, listMax, List.foldr_cons,
    List.foldr_nil, depth_input]
  omega

theorem max_incC {q : Nat} (hq : q < r) : maxInput (incC B q) ≤ 6 + 6 * B + 3 * r := by
  unfold incC xor2
  have h : maxInput (and ((List.range q).map (fun t => input (2 + 3 * B + t)))) ≤ 6 + 6 * B + 3 * r := by
    apply maxInput_and_le; intro c hc; obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hc
    have := List.mem_range.mp ht; simp; omega
  generalize and ((List.range q).map (fun t => input (2 + 3 * B + t))) = A at h ⊢
  simp only [maxInput_or, maxInput_and, maxInput_not, List.map_cons, List.map_nil, listMax,
    List.foldr_cons, List.foldr_nil, maxInput_input]
  omega

/-- Uniform size bound for every next-state formula. -/
def cellSize (B r : Nat) : Nat := cancSize B + 5 * B + 2 * r + 40

/-- Every next-state formula has depth ≤ 8, size ≤ cellSize B r and reads only the
    6 + 6B + 3r input wires (state wires and token wires). -/
theorem nextC_resources (j : Nat) :
    size (nextC B r j) ≤ cellSize B r ∧ depth (nextC B r j) ≤ 8 ∧
      maxInput (nextC B r j) ≤ 6 + 6 * B + 3 * r := by
  have c1 := size_cancC B r
  have c2 := depth_cancC B r
  have c3 := max_cancC B r
  have n1 := size_nzC B r
  have n2 := depth_nzC B r
  have n3 := max_nzC B r
  unfold nextC
  refine layout_forall (fun c => size c ≤ cellSize B r ∧ depth c ≤ 8 ∧ maxInput c ≤ 6 + 6 * B + 3 * r)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ j
  · simp [cellSize]
  · simp [modeN, Rc, Wc, Ec, Mc, listMax, cellSize] <;> omega
  · intro k hk; simp [accN, Rc, Wc, Ec, Mc, xI, xor2, listMax, cellSize] <;> omega
  · intro k hk; simp [prevN, mux, Rc, Wc, Ec, Mc, listMax, cellSize] <;> omega
  · simp [validN, Rc, Wc, Ec, Mc, listMax, cellSize] <;> omega
  · intro k hk; simp [sigN, mux, Rc, Wc, Ec, Mc, listMax, cellSize] <;> omega
  · intro q hq
    have i1 := size_incC B q; have i2 := depth_incC B q; have i3 := max_incC B r hq
    simp [idxN, mux, Rc, Wc, Mc, listMax, cellSize] <;> omega
  · simp [selFN, Rc, Wc, Mc, listMax, cellSize] <;> omega
  · intro q hq; simp [selIN, Rc, Wc, Mc, listMax, cellSize] <;> omega
  · intro k hk; simp [selVN, Rc, Wc, Mc, xI, xor2, listMax, cellSize] <;> omega
  · simp [fnzFN, Rc, Wc, Mc, listMax, cellSize] <;> omega
  · intro q hq; simp [fnzIN, Rc, Wc, Mc, listMax, cellSize] <;> omega
  · intro k hk
    have d1 := size_decC B r k; have d2 := depth_decC B r k; have d3 := max_decC B r hk
    simp [fnzVN, Rc, Wc, Mc, listMax, cellSize] <;> omega

/-- The output wires: summary flag, B summary bits, B difference bits, difference-valid
    flag, move flag, move-valid flag, r move-index bits, B move-value bits. -/
def outC (B r : Nat) : List Circ :=
  [sumOutC B r] ++ (List.range B).map sumBitC ++ (List.range B).map (diffBitC B) ++
    [diffValidC B, moveOutC B r, moveValidC B r] ++ (List.range r).map (moveIC B r) ++
    (List.range B).map (moveVC B r)

theorem outC_length : (outC B r).length = 4 + 3 * B + r := by
  simp [outC]; omega

theorem outC_resources : ∀ c ∈ outC B r, size c ≤ 16 ∧ depth c ≤ 3 ∧ maxInput c ≤ 6 + 6 * B + 3 * r := by
  intro c hc
  simp only [outC, List.mem_append, List.mem_cons, List.mem_map, List.mem_range, List.not_mem_nil,
    or_false] at hc
  rcases hc with (((((rfl | ⟨k, hk, rfl⟩) | ⟨k, hk, rfl⟩) | (rfl | rfl | rfl)) | ⟨q, hq, rfl⟩) | ⟨k, hk, rfl⟩)
  · simp [sumOutC, Ec, Mc, listMax] <;> omega
  · simp [sumBitC] <;> omega
  · simp [diffBitC, xor2, listMax] <;> omega
  · simp [diffValidC] <;> omega
  · simp [moveOutC, Ec, Mc, listMax] <;> omega
  · simp [moveValidC, listMax] <;> omega
  · simp [moveIC, mux, listMax] <;> omega
  · simp [moveVC, mux, listMax] <;> omega

/-- PER-UPDATE CIRCUIT: 4 + 5B + 3r next-state formulas and 4 + 3B + r output formulas,
    all of depth ≤ 8, over 6 + 6B + 3r input wires; total size at most
    (4 + 5B + 3r)·cellSize + 16·(4 + 3B + r), where cellSize = B(2B+3) + 5B + 2r + 41. -/
theorem per_update_size :
    ((List.range (stateWidth B r)).map (fun j => size (nextC B r j))).sum +
      ((outC B r).map size).sum ≤ stateWidth B r * cellSize B r + 16 * (4 + 3 * B + r) := by
  have h1 := sum_le_len_mul (cs := (List.range (stateWidth B r)).map (nextC B r)) (S := cellSize B r) (by
    intro c hc; obtain ⟨j, _, rfl⟩ := List.mem_map.mp hc; exact (nextC_resources B r j).1)
  have h2 := sum_le_len_mul (cs := outC B r) (S := 16) (fun c hc => (outC_resources B r c hc).1)
  simp only [List.map_map, List.length_map, List.length_range, outC_length] at h1 h2
  have e : (List.map (fun j => size (nextC B r j)) (List.range (stateWidth B r))) =
      List.map (size ∘ nextC B r) (List.range (stateWidth B r)) := rfl
  rw [e]
  omega

/-- The summary mechanism (mode, acc, prev, valid) has constant size per bit, hence O(B)
    in total; the quadratic term of cellSize comes only from the cancellation test. -/
theorem summary_resources (k : Nat) :
    size (modeN B r) ≤ 18 ∧ size (accN B r k) ≤ 35 ∧ size (prevN B r k) ≤ 25 ∧ size (validN B r) ≤ 13 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [modeN, accN, prevN, validN, mux, Rc, Wc, Ec, Mc, xI, xor2]

end Resources


/-! ## Axiom audit -/

#print axioms layout_map
#print axioms layout_congr
#print axioms e_mode
#print axioms e_acc
#print axioms e_prev
#print axioms e_valid
#print axioms e_sig
#print axioms e_idx
#print axioms e_selF
#print axioms e_selI
#print axioms e_selV
#print axioms e_fnzF
#print axioms e_fnzI
#print axioms e_fnzV
#print axioms e_row
#print axioms e_rst
#print axioms e_x
#print axioms testBit_succ
#print axioms top_bit
#print axioms canc_iff
#print axioms pos_iff_bitLE
#print axioms ev_inc
#print axioms ev_canc
#print axioms ev_nz
#print axioms ev_dec
#print axioms f_mode
#print axioms f_acc
#print axioms f_prev
#print axioms f_valid
#print axioms f_sig
#print axioms f_idx
#print axioms f_selF
#print axioms f_selI
#print axioms f_selV
#print axioms f_fnzF
#print axioms f_fnzI
#print axioms f_fnzV
#print axioms step_state
#print axioms step_out
#print axioms step_refines
#print axioms decodeS_sbits
#print axioms brun_append
#print axioms brun_refines
#print axioms self_mem_crunStates
#print axioms allDec_of_fits
#print axioms tok_bound_stream
#print axioms bits_stream
#print axioms inp_row
#print axioms inp_rst
#print axioms bstep_reset
#print axioms bits_games
#print axioms reachable_lossless
#print axioms dtoks_length
#print axioms stream_length
#print axioms brun_length
#print axioms bits_one_board
#print axioms sbits_beyond
#print axioms nextC_beyond
#print axioms counter_width
#print axioms layout_forall
#print axioms size_and_le'
#print axioms size_or_le'
#print axioms maxInput_and_le
#print axioms maxInput_or_le
#print axioms size_cancC
#print axioms depth_cancC
#print axioms max_cancC
#print axioms size_nzC
#print axioms depth_nzC
#print axioms max_nzC
#print axioms size_decC
#print axioms depth_decC
#print axioms max_decC
#print axioms size_incC
#print axioms depth_incC
#print axioms max_incC
#print axioms nextC_resources
#print axioms outC_length
#print axioms outC_resources
#print axioms per_update_size
#print axioms summary_resources
end ControllerBits
end NimAudit
