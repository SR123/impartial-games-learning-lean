import Misc

/- Phase 8, part C: general weak mastery for Nim, its game semantics, and the checked
   instances.  Written by Claude (10 October 2026).  Lean 4.26.0, core/Std only.

   Paper target: Definition def:mastery (weak mastery relative to an initial position and a
   designated role; histories consistent with the agent's own preceding actions; families
   of initial positions) and Appendix app:weak (pairing strategy).

   C1  Roles, histories (most recent board first), whose turn it is, legal histories,
       policy-consistent histories (`Cons`): on the agent's turns only its own prescribed,
       legal action may occur; on the opponent's turns every legal move may occur.
       Strategies are history-dependent (`Strat := Hist → Option board`).  Plays of a
       strategy pair (`play`, with fuel) and termination by the stone-count decrease.
   C2  `Guarantee r σ P₀` (σ wins against EVERY legal opponent strategy from P₀ in role r),
       `RoleWinnable r P₀` (some strategy has that guarantee; characterised by the nim-sum),
       and `WeakMastery F r σ`.  The history characterisation `secure_iff_guarantee`:
       the guarantee holds iff on every policy-consistent history where it is the agent's
       turn the prescribed action exists and is legal.  So an absent or illegal action is
       a loss, never a vacuous success.
   C3  Bridges from NimGame.Wins (first player), Misc.SecondWins (second player) and
       WholeGame.TwoFrameWins (a history-dependent second-player strategy using the
       previous board).  Instances: the pairing strategy pairSel B (binary selector) and its
       compiled network version, the multi-head network player mhSelect B, and the
       network-driven two-frame restoration player restReply B.
   C4  Locality (`cons_congr`, `guarantee_congr`): strategies that agree on the
       policy-consistent agent-turn histories have the same guarantee.  Strong mastery
       implies weak mastery, and an explicit example is weakly but not strongly masterful. -/

namespace NimAudit
namespace Mastery

open Game Rollout Recurrent Misc WholeGame

/-! ## C1. Roles, histories, turns -/

inductive Role where
  | first
  | second
  deriving DecidableEq

def Role.other : Role → Role
  | .first => .second
  | .second => .first

theorem Role.other_ne (r : Role) : r.other ≠ r := by cases r <;> simp [Role.other]

theorem Role.eq_other_of_ne {r s : Role} (h : s ≠ r) : s = r.other := by
  cases r <;> cases s <;> simp_all [Role.other]

/-- A history: the boards so far, MOST RECENT FIRST; its last entry is the initial board. -/
abbrev Hist := List (List Nat)

/-- A (history-dependent) strategy proposes the next board; `none` means no action. -/
abbrev Strat := Hist → Option (List Nat)

/-- The current board. -/
def cur (h : Hist) : List Nat := h.headD []

@[simp] theorem cur_cons (Q : List Nat) (h : Hist) : cur (Q :: h) = Q := rfl

/-- The player to move: the first player after an even number of moves (odd length). -/
def mover (h : Hist) : Role := if h.length % 2 = 1 then .first else .second

theorem mover_cons (Q : List Nat) (h : Hist) : mover (Q :: h) = (mover h).other := by
  unfold mover Role.other
  simp only [List.length_cons]
  by_cases h1 : h.length % 2 = 1
  · rw [if_pos h1, if_neg (by omega)]
  · rw [if_neg h1, if_pos (by omega)]

@[simp] theorem mover_init (P : List Nat) : mover [P] = .first := rfl

theorem mover_cons_eq {r : Role} {Q : List Nat} {h : Hist} (hm : mover h ≠ r) : mover (Q :: h) = r := by
  rw [mover_cons]; have := Role.eq_other_of_ne hm
  rw [this]; cases r <;> rfl

theorem mover_cons_ne {r : Role} {Q : List Nat} {h : Hist} (hm : mover h = r) : mover (Q :: h) ≠ r := by
  rw [mover_cons, hm]; exact Role.other_ne r

/-- Legal histories from P₀: arbitrary legal actions by both players. -/
inductive Legal (P0 : List Nat) : Hist → Prop
  | init : Legal P0 [P0]
  | step {h : Hist} {Q : List Nat} : Legal P0 h → Move (cur h) Q → Legal P0 (Q :: h)

/-- TERMINATION OF LEGAL PLAY: stones strictly decrease, so a legal history from P₀ has at
    most P₀.sum moves (length ≤ P₀.sum + 1), for both roles and every board, including an
    initially terminal one (length 1). -/
theorem legal_sum {P0 : List Nat} {h : Hist} (hl : Legal P0 h) : (cur h).sum + h.length ≤ P0.sum + 1 := by
  induction hl with
  | init => simp [cur]
  | step _ hm ih => have := move_sum_lt hm; simp only [cur_cons, List.length_cons]; omega

theorem legal_length {P0 : List Nat} {h : Hist} (hl : Legal P0 h) : h.length ≤ P0.sum + 1 := by
  have := legal_sum hl; omega

theorem legal_ne_nil {P0 : List Nat} {h : Hist} (hl : Legal P0 h) : h ≠ [] := by
  cases hl <;> simp

/-- The initial board is the last entry. -/
theorem legal_last {P0 : List Nat} {h : Hist} (hl : Legal P0 h) : h.drop (h.length - 1) = [P0] := by
  induction hl with
  | init => rfl
  | @step h Q hl' _ ih =>
    have hpos : 1 ≤ h.length := by have := legal_ne_nil hl'; cases h <;> simp_all
    simp only [List.length_cons]
    rw [show h.length + 1 - 1 = (h.length - 1) + 1 by omega, List.drop_succ_cons, ih]

/-- Every consecutive pair of a legal history is a legal move. -/
theorem legal_pair {P0 : List Nat} {h : Hist} (hl : Legal P0 h) :
    ∀ j (hj : j + 1 < h.length), Move (cur (h.drop (j + 1))) (h[j]'(by omega)) := by
  induction hl with
  | init => intro j hj; simp at hj
  | @step h Q hl' hm ih =>
    intro j hj
    cases j with
    | zero => simpa using hm
    | succ j =>
      simp only [List.length_cons] at hj
      simp only [List.drop_succ_cons, List.getElem_cons_succ]
      exact ih j (by omega)

/-- Policy-consistent legal histories for the agent in role r using σ: on the agent's turns
    only its own prescribed legal action occurs; on the opponent's turns any legal move. -/
inductive Cons (r : Role) (σ : Strat) (P0 : List Nat) : Hist → Prop
  | init : Cons r σ P0 [P0]
  | opp {h : Hist} {Q : List Nat} : Cons r σ P0 h → mover h ≠ r → Move (cur h) Q → Cons r σ P0 (Q :: h)
  | own {h : Hist} {Q : List Nat} : Cons r σ P0 h → mover h = r → σ h = some Q → Move (cur h) Q →
      Cons r σ P0 (Q :: h)

theorem cons_legal {r : Role} {σ : Strat} {P0 : List Nat} {h : Hist} (hc : Cons r σ P0 h) : Legal P0 h := by
  induction hc with
  | init => exact Legal.init
  | opp _ _ hm ih => exact Legal.step ih hm
  | own _ _ _ hm ih => exact Legal.step ih hm

/-- On a consistent history every agent step in it was the prescribed action. -/
theorem cons_own {r : Role} {σ : Strat} {P0 : List Nat} {h : Hist} (hc : Cons r σ P0 h) :
    ∀ j (hj : j + 1 < h.length), mover (h.drop (j + 1)) = r → σ (h.drop (j + 1)) = some (h[j]'(by omega)) := by
  induction hc with
  | init => intro j hj; simp at hj
  | @opp h Q hc' hne _ ih =>
    intro j hj hmv
    cases j with
    | zero => simp only [List.drop_succ_cons, List.drop_zero] at hmv; exact absurd hmv hne
    | succ j =>
      simp only [List.length_cons] at hj
      simp only [List.drop_succ_cons, List.getElem_cons_succ] at hmv ⊢
      exact ih j (by omega) hmv
  | @own h Q hc' _ hσ _ ih =>
    intro j hj hmv
    cases j with
    | zero => simpa using hσ
    | succ j =>
      simp only [List.length_cons] at hj
      simp only [List.drop_succ_cons, List.getElem_cons_succ] at hmv ⊢
      exact ih j (by omega) hmv

/-- The history guarantee: on every policy-consistent history where it is the agent's turn,
    the prescribed action exists and is a legal move (in particular the agent is never to
    move at a terminal board). -/
def Secure (r : Role) (σ : Strat) (P0 : List Nat) : Prop :=
  ∀ h, Cons r σ P0 h → mover h = r → ∃ Q, σ h = some Q ∧ Move (cur h) Q

/-- NO VACUOUS SUCCESS (1): a secure consistent history can always be continued until the
    board is terminal: on the agent's turn by its own action, on the opponent's turn by any
    legal move. -/
theorem secure_extend {r : Role} {σ : Strat} {P0 : List Nat} (hs : Secure r σ P0) {h : Hist}
    (hc : Cons r σ P0 h) (hnt : ¬ Terminal (cur h)) : ∃ Q, Cons r σ P0 (Q :: h) := by
  by_cases hm : mover h = r
  · obtain ⟨Q, hQ, hmv⟩ := hs h hc hm
    exact ⟨Q, Cons.own hc hm hQ hmv⟩
  · have : ∃ Q, Move (cur h) Q := by
      apply Classical.byContradiction; intro hno
      exact hnt ((terminal_iff_no_move _).2 (fun Q hQ => hno ⟨Q, hQ⟩))
    obtain ⟨Q, hQ⟩ := this
    exact ⟨Q, Cons.opp hc hm hQ⟩

/-- NO VACUOUS SUCCESS (2): under the guarantee every consistent history that reaches a
    terminal board does so with the OPPONENT to move: the opponent cannot move and loses. -/
theorem secure_terminal {r : Role} {σ : Strat} {P0 : List Nat} (hs : Secure r σ P0) {h : Hist}
    (hc : Cons r σ P0 h) (ht : Terminal (cur h)) : mover h ≠ r := by
  intro hm
  obtain ⟨Q, _, hmv⟩ := hs h hc hm
  exact (terminal_iff_no_move _).1 ht Q hmv

/-! ### Plays of strategy pairs -/

/-- Outcome of a play for the agent. -/
inductive Outcome where
  | agentWins
  | agentLoses
  | unfinished
  deriving DecidableEq

/-- A legal opponent strategy: whenever a legal move exists it proposes a legal move. -/
def LegalOpp (τ : Strat) : Prop := ∀ h, (∃ Q, Move (cur h) Q) → ∃ Q, τ h = some Q ∧ Move (cur h) Q

open Classical in
/-- The play of agent σ (role r) against opponent τ, with fuel.  A player who proposes no
    action or an illegal one loses at once; in particular the player to move at a terminal
    board loses (normal play).  Legal opponents never forfeit. -/
noncomputable def play (r : Role) (σ τ : Strat) : Nat → Hist → Outcome
  | 0, _ => .unfinished
  | f + 1, h =>
    if mover h = r then
      match σ h with
      | some Q => if Move (cur h) Q then play r σ τ f (Q :: h) else .agentLoses
      | none => .agentLoses
    else
      match τ h with
      | some Q => if Move (cur h) Q then play r σ τ f (Q :: h) else .agentWins
      | none => .agentWins

section PlayLemmas
variable {r : Role} {σ τ : Strat}

theorem play_own {f : Nat} {h : Hist} {Q : List Nat} (hm : mover h = r) (hσ : σ h = some Q)
    (hmv : Move (cur h) Q) : play r σ τ (f + 1) h = play r σ τ f (Q :: h) := by
  simp only [play, hm, if_true, hσ, hmv]

theorem play_own_fail {f : Nat} {h : Hist} (hm : mover h = r) (hσ : ¬ ∃ Q, σ h = some Q ∧ Move (cur h) Q) :
    play r σ τ (f + 1) h = .agentLoses := by
  simp only [play, hm, if_true]
  cases hs : σ h with
  | none => rfl
  | some Q =>
    have : ¬ Move (cur h) Q := fun hmv => hσ ⟨Q, hs, hmv⟩
    simp only [this, if_false]

theorem play_opp {f : Nat} {h : Hist} {Q : List Nat} (hm : mover h ≠ r) (hτ : τ h = some Q)
    (hmv : Move (cur h) Q) : play r σ τ (f + 1) h = play r σ τ f (Q :: h) := by
  simp only [play, hm, if_false, hτ, hmv, if_true]

theorem play_opp_fail {f : Nat} {h : Hist} (hm : mover h ≠ r) (hτ : ¬ ∃ Q, τ h = some Q ∧ Move (cur h) Q) :
    play r σ τ (f + 1) h = .agentWins := by
  simp only [play, hm, if_false]
  cases hs : τ h with
  | none => rfl
  | some Q =>
    have : ¬ Move (cur h) Q := fun hmv => hτ ⟨Q, hs, hmv⟩
    simp only [this, if_false]

/-- TERMINATION: with fuel above the stone count every play finishes. -/
theorem play_finishes : ∀ (f : Nat) (h : Hist), (cur h).sum < f → play r σ τ f h ≠ .unfinished
  | 0, _, hf => by omega
  | f + 1, h, hf => by
    by_cases hm : mover h = r
    · by_cases hσ : ∃ Q, σ h = some Q ∧ Move (cur h) Q
      · obtain ⟨Q, h1, h2⟩ := hσ
        rw [play_own hm h1 h2]
        have := move_sum_lt h2
        exact play_finishes f (Q :: h) (by simp only [cur_cons]; omega)
      · rw [play_own_fail hm hσ]; simp
    · by_cases hτ : ∃ Q, τ h = some Q ∧ Move (cur h) Q
      · obtain ⟨Q, h1, h2⟩ := hτ
        rw [play_opp hm h1 h2]
        have := move_sum_lt h2
        exact play_finishes f (Q :: h) (by simp only [cur_cons]; omega)
      · rw [play_opp_fail hm hτ]; simp

/-- The outcome does not depend on the fuel once it exceeds the stone count. -/
theorem play_fuel : ∀ (f g : Nat) (h : Hist), (cur h).sum < f → (cur h).sum < g →
    play r σ τ f h = play r σ τ g h
  | 0, _, _, hf, _ => by omega
  | _ + 1, 0, _, _, hg => by omega
  | f + 1, g + 1, h, hf, hg => by
    by_cases hm : mover h = r
    · by_cases hσ : ∃ Q, σ h = some Q ∧ Move (cur h) Q
      · obtain ⟨Q, h1, h2⟩ := hσ
        rw [play_own hm h1 h2, play_own hm h1 h2]
        have := move_sum_lt h2
        exact play_fuel f g (Q :: h) (by simp only [cur_cons]; omega) (by simp only [cur_cons]; omega)
      · rw [play_own_fail hm hσ, play_own_fail hm hσ]
    · by_cases hτ : ∃ Q, τ h = some Q ∧ Move (cur h) Q
      · obtain ⟨Q, h1, h2⟩ := hτ
        rw [play_opp hm h1 h2, play_opp hm h1 h2]
        have := move_sum_lt h2
        exact play_fuel f g (Q :: h) (by simp only [cur_cons]; omega) (by simp only [cur_cons]; omega)
      · rw [play_opp_fail hm hτ, play_opp_fail hm hτ]

end PlayLemmas

/-- The agent wins the play from P₀ (fuel P₀.sum + 1 suffices, play_finishes). -/
def Beats (r : Role) (σ τ : Strat) (P0 : List Nat) : Prop := play r σ τ (P0.sum + 1) [P0] = .agentWins

/-- σ wins from P₀ in role r against EVERY legal opponent strategy. -/
def Guarantee (r : Role) (σ : Strat) (P0 : List Nat) : Prop := ∀ τ, LegalOpp τ → Beats r σ τ P0

/-- An initially terminal board: the first player (to move) loses whatever it does, and the
    second player wins against every opponent. -/
theorem terminal_start {P0 : List Nat} (ht : Terminal P0) (σ τ : Strat) :
    play .first σ τ (P0.sum + 1) [P0] = .agentLoses ∧ play .second σ τ (P0.sum + 1) [P0] = .agentWins := by
  have hno : ∀ Q, ¬ Move P0 Q := (terminal_iff_no_move P0).1 ht
  constructor
  · exact play_own_fail (by rfl) (fun ⟨Q, _, hm⟩ => hno Q hm)
  · exact play_opp_fail (by simp) (fun ⟨Q, _, hm⟩ => hno Q hm)

/-! ## C2. The history characterisation of the guarantee -/

theorem secure_play {r : Role} {σ τ : Strat} {P0 : List Nat} (hs : Secure r σ P0) :
    ∀ (f : Nat) (h : Hist), Cons r σ P0 h → (cur h).sum < f → play r σ τ f h = .agentWins
  | 0, _, _, hf => by omega
  | f + 1, h, hc, hf => by
    by_cases hm : mover h = r
    · obtain ⟨Q, h1, h2⟩ := hs h hc hm
      rw [play_own hm h1 h2]
      have := move_sum_lt h2
      exact secure_play hs f (Q :: h) (Cons.own hc hm h1 h2) (by simp only [cur_cons]; omega)
    · by_cases hτ : ∃ Q, τ h = some Q ∧ Move (cur h) Q
      · obtain ⟨Q, h1, h2⟩ := hτ
        rw [play_opp hm h1 h2]
        have := move_sum_lt h2
        exact secure_play hs f (Q :: h) (Cons.opp hc hm h2) (by simp only [cur_cons]; omega)
      · exact play_opp_fail hm hτ

theorem secure_guarantee {r : Role} {σ : Strat} {P0 : List Nat} (hs : Secure r σ P0) : Guarantee r σ P0 :=
  fun _ _ => secure_play hs (P0.sum + 1) [P0] Cons.init (by simp [cur])

/-- The opponent that follows a given history h on its proper prefixes and otherwise plays
    the default strategy d. -/
def followD (d : Strat) (h : Hist) (g : Hist) : Option (List Nat) :=
  if g.length < h.length ∧ h.drop (h.length - g.length) = g then h[h.length - g.length - 1]? else d g

/-- Following h, with "remove one stone from the first nonempty heap" as default. -/
def follow (h : Hist) : Strat := followD (fun g => subFirstPos (cur g)) h

theorem subFirstPos_move {P Q : List Nat} (h : subFirstPos P = some Q) : Move P Q := by
  obtain ⟨pre, x, post, rfl, hx, rfl⟩ := subFirstPos_some h
  exact ⟨pre, x, post, x - 1, rfl, rfl, by omega⟩

theorem subFirstPos_isSome {P : List Nat} (h : ∃ Q, Move P Q) : ∃ Q, subFirstPos P = some Q := by
  cases hs : subFirstPos P with
  | some Q => exact ⟨Q, rfl⟩
  | none =>
    obtain ⟨Q, hQ⟩ := h
    exact absurd hQ ((terminal_iff_no_move P).1 (subFirstPos_none hs) Q)

theorem subFirst_legal : LegalOpp (fun g => subFirstPos (cur g)) := by
  intro g hex
  obtain ⟨Q, hQ⟩ := subFirstPos_isSome hex
  exact ⟨Q, hQ, subFirstPos_move hQ⟩

theorem followD_legal {P0 : List Nat} {h : Hist} (hl : Legal P0 h) {d : Strat} (hd : LegalOpp d) :
    LegalOpp (followD d h) := by
  intro g hex
  unfold followD
  by_cases hc : g.length < h.length ∧ h.drop (h.length - g.length) = g
  · rw [if_pos hc]
    have hpos : 1 ≤ h.length - g.length := by omega
    have hmv := legal_pair hl (h.length - g.length - 1) (by
      have : 0 < g.length := by
        obtain ⟨Q, hQ⟩ := hex
        cases g with
        | nil => obtain ⟨pre, x, post, y, hp, _, _⟩ := hQ; simp [cur] at hp
        | cons _ _ => simp
      omega)
    have hdrop : h.drop (h.length - g.length - 1 + 1) = g := by
      rw [show h.length - g.length - 1 + 1 = h.length - g.length by omega]; exact hc.2
    rw [hdrop] at hmv
    exact ⟨_, List.getElem?_eq_getElem (by omega), hmv⟩
  · rw [if_neg hc]; exact hd g hex

theorem follow_legal {P0 : List Nat} {h : Hist} (hl : Legal P0 h) : LegalOpp (follow h) :=
  followD_legal hl subFirst_legal

/-- The play against `followD d h` runs along h (whatever the default d). -/
theorem followD_play {r : Role} {σ : Strat} {P0 : List Nat} {h : Hist} (d : Strat) (hc : Cons r σ P0 h) :
    ∀ (j : Nat) (hj : j < h.length) (f : Nat),
      play r σ (followD d h) (f + j) (h.drop j) = play r σ (followD d h) f h
  | 0, _, f => by simp
  | j + 1, hj, f => by
    have hl := cons_legal hc
    have hmv := legal_pair hl j hj
    have hsplit : h.drop j = h[j] :: h.drop (j + 1) := List.drop_eq_getElem_cons (by omega)
    rw [show f + (j + 1) = (f + j) + 1 by omega]
    by_cases hm : mover (h.drop (j + 1)) = r
    · have hσ := cons_own hc j hj hm
      rw [play_own hm hσ hmv, ← hsplit]
      exact followD_play d hc j (by omega) f
    · have hτ : followD d h (h.drop (j + 1)) = some h[j] := by
        unfold followD
        have hlen : (h.drop (j + 1)).length = h.length - (j + 1) := List.length_drop
        rw [if_pos ⟨by omega, by rw [hlen, show h.length - (h.length - (j + 1)) = j + 1 by omega]⟩, hlen,
          show h.length - (h.length - (j + 1)) - 1 = j by omega]
        exact List.getElem?_eq_getElem (by omega)
      rw [play_opp hm hτ hmv, ← hsplit]
      exact followD_play d hc j (by omega) f

theorem follow_play {r : Role} {σ : Strat} {P0 : List Nat} {h : Hist} (hc : Cons r σ P0 h) :
    ∀ (j : Nat) (hj : j < h.length) (f : Nat), play r σ (follow h) (f + j) (h.drop j) = play r σ (follow h) f h :=
  followD_play _ hc

/-- Running a play from P₀ against `followD d h` up to the end of h. -/
theorem followD_reach {r : Role} {σ : Strat} {P0 : List Nat} {h : Hist} (d : Strat) (hc : Cons r σ P0 h) :
    play r σ (followD d h) (P0.sum + 1) [P0] =
      play r σ (followD d h) ((P0.sum + 1 - h.length) + 1) h := by
  have hl := cons_legal hc
  have hsum := legal_sum hl
  have hne := legal_ne_nil hl
  have hlen : 1 ≤ h.length := by cases h <;> simp_all
  have e := followD_play d hc (h.length - 1) (by omega) (P0.sum + 1 - (h.length - 1))
  rw [show P0.sum + 1 - (h.length - 1) + (h.length - 1) = P0.sum + 1 by omega, legal_last hl] at e
  rw [e, show P0.sum + 1 - (h.length - 1) = (P0.sum + 1 - h.length) + 1 by omega]

/-- C2, HISTORY CHARACTERISATION: σ wins from P₀ in role r against every legal opponent iff
    on every policy-consistent history at the agent's turn its prescribed action exists and
    is legal. -/
theorem secure_iff_guarantee (r : Role) (σ : Strat) (P0 : List Nat) : Secure r σ P0 ↔ Guarantee r σ P0 := by
  refine ⟨secure_guarantee, fun hg h hc hm => ?_⟩
  apply Classical.byContradiction; intro hfail
  have hb := hg (follow h) (follow_legal (cons_legal hc))
  unfold Beats follow at hb
  rw [followD_reach _ hc, play_own_fail hm hfail] at hb
  cases hb

/-! ### Winnable roles -/

/-- The role r has a winning strategy from P₀ (existence, separate from any policy). -/
def RoleWinnable (r : Role) (P0 : List Nat) : Prop := ∃ σ : Strat, Guarantee r σ P0

/-- The optimal opponent: move to nim-sum 0 when possible, otherwise any legal move. -/
def optOpp : Strat := fun h => selectMove (nimSum (cur h)) (cur h)

theorem optOpp_legal : LegalOpp optOpp := by
  intro h hex
  cases hs : selectMove (nimSum (cur h)) (cur h) with
  | none =>
    obtain ⟨Q, hQ⟩ := hex
    exact absurd hQ ((terminal_iff_no_move _).1 ((selectMove_none_iff _ _).1 hs) Q)
  | some Q => exact ⟨Q, hs, selectMove_legal hs⟩

/-- Against the optimal opponent the agent loses from every history where it faces nim-sum
    0 on its turn (or the opponent faces a nonzero nim-sum on its turn). -/
theorem optOpp_play {r : Role} {σ : Strat} : ∀ (f : Nat) (h : Hist), (cur h).sum < f →
    (mover h = r → nimSum (cur h) = 0) → (mover h ≠ r → nimSum (cur h) ≠ 0) →
    play r σ optOpp f h = .agentLoses
  | 0, _, hf, _, _ => by omega
  | f + 1, h, hf, h1, h2 => by
    by_cases hm : mover h = r
    · by_cases hσ : ∃ Q, σ h = some Q ∧ Move (cur h) Q
      · obtain ⟨Q, hQ, hmv⟩ := hσ
        rw [play_own hm hQ hmv]
        have := move_sum_lt hmv
        exact optOpp_play f (Q :: h) (by simp only [cur_cons]; omega)
          (fun hm' => absurd hm' (mover_cons_ne hm)) (fun _ => move_from_zero hmv (h1 hm))
      · exact play_own_fail hm hσ
    · obtain ⟨Q, hsel, hmv, hz⟩ := selectMove_zero (h2 hm)
      rw [play_opp hm (show optOpp h = some Q from hsel) hmv]
      have := move_sum_lt hmv
      exact optOpp_play f (Q :: h) (by simp only [cur_cons]; omega) (fun _ => hz)
        (fun hm' => absurd (mover_cons_eq hm) hm')

/-- The same for any opponent that plays like optOpp on all histories of length ≥ k. -/
theorem optLike_play {r : Role} {σ τ : Strat} {k : Nat} (hτ : ∀ g : Hist, k ≤ g.length → τ g = optOpp g) :
    ∀ (f : Nat) (h : Hist), k ≤ h.length → (cur h).sum < f →
    (mover h = r → nimSum (cur h) = 0) → (mover h ≠ r → nimSum (cur h) ≠ 0) → play r σ τ f h = .agentLoses
  | 0, _, _, hf, _, _ => by omega
  | f + 1, h, hk, hf, h1, h2 => by
    by_cases hm : mover h = r
    · by_cases hσ : ∃ Q, σ h = some Q ∧ Move (cur h) Q
      · obtain ⟨Q, hQ, hmv⟩ := hσ
        rw [play_own hm hQ hmv]
        have := move_sum_lt hmv
        exact optLike_play hτ f (Q :: h) (by simp; omega) (by simp only [cur_cons]; omega)
          (fun hm' => absurd hm' (mover_cons_ne hm)) (fun _ => move_from_zero hmv (h1 hm))
      · exact play_own_fail hm hσ
    · obtain ⟨Q, hsel, hmv, hz⟩ := selectMove_zero (h2 hm)
      rw [play_opp hm (show τ h = some Q by rw [hτ h hk]; exact hsel) hmv]
      have := move_sum_lt hmv
      exact optLike_play hτ f (Q :: h) (by simp; omega) (by simp only [cur_cons]; omega) (fun _ => hz)
        (fun hm' => absurd (mover_cons_eq hm) hm')

/-- THE GUARANTEE FORCES WINNING MOVES ON CONSISTENT HISTORIES: if σ wins from P₀ against
    every legal opponent, then at every policy-consistent history where it is to move it
    plays a legal move to a P-position (nim-sum 0).  (Otherwise the opponent that follows
    that history and then plays optimally wins.) -/
theorem guarantee_optimal {r : Role} {σ : Strat} {P0 : List Nat} (hg : Guarantee r σ P0) {h : Hist}
    (hc : Cons r σ P0 h) (hm : mover h = r) : ∃ Q, σ h = some Q ∧ Move (cur h) Q ∧ nimSum Q = 0 := by
  obtain ⟨Q, hQ, hmv⟩ := (secure_iff_guarantee r σ P0).2 hg h hc hm
  refine ⟨Q, hQ, hmv, Classical.byContradiction (fun hz => ?_)⟩
  have hl := cons_legal hc
  have hb := hg (followD optOpp h) (followD_legal hl optOpp_legal)
  unfold Beats at hb
  rw [followD_reach _ hc] at hb
  have hsum := legal_sum hl
  have hs := move_sum_lt hmv
  cases hf : P0.sum + 1 - h.length with
  | zero => omega
  | succ f =>
    rw [hf, play_own hm hQ hmv] at hb
    have hτ : ∀ g : Hist, h.length + 1 ≤ g.length → followD optOpp h g = optOpp g := by
      intro g hg'; unfold followD; rw [if_neg (by omega)]
    rw [optLike_play hτ (f + 1) (Q :: h) (by simp) (by simp only [cur_cons]; omega)
      (fun hm' => absurd hm' (mover_cons_ne hm)) (fun _ => hz)] at hb
    cases hb

/-- The memoryless strategy defined by a board selector. -/
def ofSel (sel : List Nat → Option (List Nat)) : Strat := fun h => sel (cur h)

/-- C3 BRIDGE (first player): a NimGame.Wins certificate gives the history guarantee. -/
theorem wins_secure {sel : List Nat → Option (List Nat)} {P0 : List Nat} (hw : Wins sel P0) :
    Secure .first (ofSel sel) P0 := by
  have inv : ∀ h, Cons .first (ofSel sel) P0 h →
      (mover h = .first → Wins sel (cur h)) ∧ (mover h ≠ .first → ∃ P, Wins sel P ∧ sel P = some (cur h) ∧
        ∀ R, Move (cur h) R → Wins sel R) := by
    intro h hc
    induction hc with
    | init => exact ⟨fun _ => hw, fun h => absurd rfl h⟩
    | @opp h Q hc' hne hmv ih =>
      obtain ⟨P, _, _, hall⟩ := (ih.2 hne)
      exact ⟨fun _ => hall Q hmv, fun h' => absurd (mover_cons_eq hne) h'⟩
    | @own h Q hc' hm hσ hmv ih =>
      have hW := ih.1 hm
      refine ⟨fun h' => absurd h' (mover_cons_ne hm), fun _ => ?_⟩
      cases hW with
      | intro p q hs hm' hall =>
        have hq : q = Q := by unfold ofSel at hσ; rw [hs] at hσ; exact Option.some.inj hσ
        subst hq
        exact ⟨cur h, Wins.intro _ q hs hm' hall, hs, hall⟩
  intro h hc hm
  have hW := (inv h hc).1 hm
  cases hW with
  | intro p q hs hm' _ => exact ⟨q, hs, hm'⟩

/-- C3 BRIDGE (second player): a Misc.SecondWins certificate gives the history guarantee. -/
theorem secondWins_secure {sel : List Nat → Option (List Nat)} {P0 : List Nat} (hw : SecondWins sel P0) :
    Secure .second (ofSel sel) P0 := by
  have inv : ∀ h, Cons .second (ofSel sel) P0 h →
      (mover h ≠ .second → SecondWins sel (cur h)) ∧
      (mover h = .second → ∃ P, SecondWins sel P ∧ Move P (cur h)) := by
    intro h hc
    induction hc with
    | init => exact ⟨fun _ => hw, fun h => by simp at h⟩
    | @opp h Q hc' hne hmv ih =>
      exact ⟨fun h' => absurd (mover_cons_eq hne) h', fun _ => ⟨cur h, ih.1 hne, hmv⟩⟩
    | @own h Q hc' hm hσ hmv ih =>
      obtain ⟨P, hP, hPm⟩ := ih.2 hm
      refine ⟨fun _ => ?_, fun h' => absurd h' (mover_cons_ne hm)⟩
      cases hP with
      | intro _ _ _ hrest => exact hrest (cur h) Q hPm hσ
  intro h hc hm
  obtain ⟨P, hP, hPm⟩ := (inv h hc).2 hm
  cases hP with
  | intro _ hsome hmove _ =>
    cases hs : sel (cur h) with
    | none => have := hsome (cur h) hPm; rw [hs] at this; cases this
    | some Q => exact ⟨Q, hs, hmove (cur h) Q hPm hs⟩

/-- The canonical second-player selector (restore nim-sum 0). -/
def zeroSel (Q : List Nat) : Option (List Nat) := selectMove (nimSum Q) Q

theorem zeroSel_wins : ∀ P : List Nat, nimSum P = 0 → SecondWins zeroSel P := by
  intro P
  induction P using (measure List.sum).wf.induction with
  | h P ih =>
    intro h0
    have key : ∀ Q, Move P Q → ∃ R, zeroSel Q = some R ∧ Move Q R ∧ nimSum R = 0 :=
      fun Q hm => selectMove_zero (move_from_zero hm h0)
    refine SecondWins.intro P (fun Q hm => ?_) (fun Q R hm hR => ?_) (fun Q R hm hR => ?_)
    · obtain ⟨R, h1, _⟩ := key Q hm; rw [h1]; rfl
    · obtain ⟨R', h1, h2, _⟩ := key Q hm; rw [h1] at hR; cases hR; exact h2
    · obtain ⟨R', h1, h2, h3⟩ := key Q hm
      have e : R' = R := Option.some.inj (h1.symm.trans hR)
      subst e
      have := move_sum_lt hm; have := move_sum_lt h2
      exact ih R' (by show R'.sum < P.sum; omega) h3

theorem le_sum_of_mem {x : Nat} : ∀ {P : List Nat}, x ∈ P → x ≤ P.sum
  | [], h => by simp at h
  | y :: P, h => by
    rcases List.mem_cons.mp h with rfl | h
    · simp
    · have := le_sum_of_mem h; simp; omega

theorem width_sum (P : List Nat) : Width P.sum P :=
  fun x hx => Nat.lt_of_le_of_lt (le_sum_of_mem hx) Nat.lt_two_pow_self

/-- WHICH ROLE IS WINNABLE: the first player has a winning strategy iff nim(P₀) ≠ 0, the
    second iff nim(P₀) = 0 (i.e. iff P₀ is an N- resp. P-position). -/
theorem roleWinnable_first (P0 : List Nat) : RoleWinnable .first P0 ↔ nimSum P0 ≠ 0 := by
  constructor
  · rintro ⟨σ, hg⟩ h0
    have := hg optOpp optOpp_legal
    unfold Beats at this
    rw [optOpp_play (r := .first) (σ := σ) (P0.sum + 1) [P0] (by simp [cur]) (fun _ => h0)
      (fun h => absurd rfl h)] at this
    cases this
  · intro h
    exact ⟨ofSel (agent P0.sum), secure_guarantee (wins_secure (agent_wins P0 (width_sum P0) h))⟩

theorem roleWinnable_second (P0 : List Nat) : RoleWinnable .second P0 ↔ nimSum P0 = 0 := by
  constructor
  · rintro ⟨σ, hg⟩
    apply Classical.byContradiction; intro h0
    have := hg optOpp optOpp_legal
    unfold Beats at this
    rw [optOpp_play (r := .second) (σ := σ) (P0.sum + 1) [P0] (by simp [cur]) (fun h => by simp at h)
      (fun _ => h0)] at this
    cases this
  · intro h
    exact ⟨ofSel zeroSel, secure_guarantee (secondWins_secure (zeroSel_wins P0 h))⟩

theorem roleWinnable_game (P0 : List Nat) :
    (RoleWinnable .first P0 ↔ Win P0) ∧ (RoleWinnable .second P0 ↔ Lose P0) :=
  ⟨by rw [roleWinnable_first, win_iff], by rw [roleWinnable_second, lose_iff]⟩

/-- Exactly one role is winnable from each board. -/
theorem roleWinnable_exclusive (P0 : List Nat) : RoleWinnable .first P0 ↔ ¬ RoleWinnable .second P0 := by
  rw [roleWinnable_first, roleWinnable_second]

/-! ## C2. Weak mastery -/

/-- WEAK MASTERY of policy σ for the family F of initial boards and the designated role r:
    from every initial board of the family from which the role has SOME winning strategy,
    σ itself wins against every legal opponent strategy. -/
def WeakMastery (F : List Nat → Prop) (r : Role) (σ : Strat) : Prop :=
  ∀ P0, F P0 → RoleWinnable r P0 → Guarantee r σ P0

/-- Indexed families (e.g. by bit width B), with an index-dependent policy. -/
def WeakMasteryFam {ι : Type} (F : ι → List Nat → Prop) (r : Role) (σ : ι → Strat) : Prop :=
  ∀ i, WeakMastery (F i) r (σ i)

/-- Unfolded form: in nim-sum terms and with the history guarantee. -/
theorem weakMastery_iff (F : List Nat → Prop) (r : Role) (σ : Strat) :
    WeakMastery F r σ ↔
      ∀ P0, F P0 → (if r = .first then nimSum P0 ≠ 0 else nimSum P0 = 0) → Secure r σ P0 := by
  have hw : ∀ P0, RoleWinnable r P0 ↔ (if r = .first then nimSum P0 ≠ 0 else nimSum P0 = 0) := by
    intro P0; cases r
    · simp [roleWinnable_first]
    · simp [roleWinnable_second]
  constructor
  · intro h P0 hF hc; exact (secure_iff_guarantee r σ P0).2 (h P0 hF ((hw P0).2 hc))
  · intro h P0 hF hc; exact (secure_iff_guarantee r σ P0).1 (h P0 hF ((hw P0).1 hc))

/-- THE CONDITIONAL CASE MADE EXPLICIT: at an initial board from which the role is losing
    there is nothing to check, so on a family of losing boards EVERY policy (even one that
    never moves) is weakly masterful.  Weak mastery is informative only where the role is
    winnable. -/
theorem weakMastery_vacuous {F : List Nat → Prop} {r : Role} (hF : ∀ P0, F P0 → ¬ RoleWinnable r P0)
    (σ : Strat) : WeakMastery F r σ :=
  fun P0 h1 h2 => absurd h2 (hF P0 h1)

theorem weakMastery_restrict (F : List Nat → Prop) (r : Role) (σ : Strat) :
    WeakMastery F r σ ↔ WeakMastery (fun P => F P ∧ RoleWinnable r P) r σ :=
  ⟨fun h P0 hF hw => h P0 hF.1 hw, fun h P0 hF hw => h P0 ⟨hF, hw⟩ hw⟩

/-- WEAK MASTERY = WINNING MOVES ON POLICY-CONSISTENT HISTORIES: σ is weakly masterful for F
    and r iff, from every winnable initial board of F, at every history consistent with σ's
    own preceding actions where σ is to move, σ plays a legal move to a P-position.  Contrast
    StrongMastery below, which asks this on ALL legal histories. -/
theorem weakMastery_iff_optimal (F : List Nat → Prop) (r : Role) (σ : Strat) :
    WeakMastery F r σ ↔ ∀ P0, F P0 → RoleWinnable r P0 → ∀ h, Cons r σ P0 h → mover h = r →
      ∃ Q, σ h = some Q ∧ Move (cur h) Q ∧ nimSum Q = 0 := by
  constructor
  · intro hw P0 hF hr h hc hm; exact guarantee_optimal (hw P0 hF hr) hc hm
  · intro h P0 hF hr
    exact secure_guarantee (fun g hc hm => let ⟨Q, h1, h2, _⟩ := h P0 hF hr g hc hm; ⟨Q, h1, h2⟩)

/-! ## C3. Instances -/

/-- PAIRING (second player): from every paired board of width B (all of which are
    P-positions, so the second role IS winnable), the binary mirror selector pairSel B
    wins against every legal opponent strategy. -/
theorem pairing_guarantee {B : Nat} {P0 : List Nat} (hp : Paired P0) (hw : Width B P0) :
    RoleWinnable .second P0 ∧ Guarantee .second (ofSel (pairSel B)) P0 :=
  ⟨(roleWinnable_second P0).2 (paired_lose hp hw).2,
   secure_guarantee (secondWins_secure (pairing_wins P0 hp hw))⟩

theorem pairing_weak : WeakMasteryFam (fun B P => Paired P ∧ Width B P) .second (fun B => ofSel (pairSel B)) :=
  fun _ P0 hF _ => (pairing_guarantee hF.1 hF.2).2

/-- For the first role the paired family is losing, so weak mastery there is vacuous. -/
theorem pairing_first_vacuous (B : Nat) (σ : Strat) : WeakMastery (fun P => Paired P ∧ Width B P) .first σ :=
  weakMastery_vacuous (fun P0 hF hw => (roleWinnable_first P0).1 hw (paired_lose hF.1 hF.2).2) σ

/-- The compiled threshold network of the mirror selector, and its reply rule. -/
def pairNet (B N r : Nat) : List AC0.Layer := ThresholdInst.binNet (pairBin B N r)
def pairNetSel (B : Nat) (Q : List Nat) : Option (List Nat) :=
  SelectCircuit.applyM Q (ThresholdInst.netBinSem (pairNet B Q.length (rIdx Q.length)) Q.length (rIdx Q.length) B
    (CorrBridge.boardBits B Q))

/-- The network reply rule IS the binary selector's rule, on every board. -/
theorem pairNetSel_eq (B : Nat) : pairNetSel B = pairSel B := by
  funext Q
  unfold pairNetSel pairSel pairNet
  rw [ThresholdInst.binNet_correct (pairBin B Q.length (rIdx Q.length))
    (by simp [pairBin, PriorityEncoder.encode]) (by simp [pairBin, PriorityEncoder.encode, pairR])]

theorem pairing_net_weak :
    WeakMasteryFam (fun B P => Paired P ∧ Width B P) .second (fun B => ofSel (pairNetSel B)) := by
  intro B
  show WeakMastery _ _ (ofSel (pairNetSel B))
  rw [pairNetSel_eq]; exact pairing_weak B

/-- The resources certified in phase 6 are for the same binary selector: depth, size and
    reads of pairBin B N r (N even, N ≤ 2^r), and the network compiled from it. -/
theorem pairing_resources (B N : Nat) (hN : N % 2 = 0) :
    PriorityEncoder.BinBound (pairBin B N (rIdx N)) N B (rIdx N) 10
      (4 * ((N + 2) * (N * (2 * pairF B + 1) + 1 + 2)) ^ 3) (B * N) ∧
    AC0.NetValid 1 (pairNet B N (rIdx N)) ∧ FiniteNet.Wired (B * N) (pairNet B N (rIdx N)) ∧
    (pairNet B N (rIdx N)).length ≤ 2 * 10 + 2 :=
  have hb := pairBin_bound B N (rIdx N) (Family.rIdx_width N) hN
  have hn := ThresholdInst.binNet_res hb
  ⟨hb, hn.1, hn.2.1, hn.2.2.1⟩

/-- MULTI-HEAD (first player): the network-driven multi-head player is weakly masterful on
    every B-bit family for the first role. -/
theorem mh_weak : WeakMasteryFam (fun B P => Width B P) .first (fun B => ofSel (mhSelect B)) := by
  intro B P0 hw hwin
  exact secure_guarantee (wins_secure (mhSelect_wins hw ((roleWinnable_first P0).1 hwin)))

/-- The history-dependent two-frame strategy: answer the opponent's move Q → Q' by
    reply Q Q' (Q = the board before the opponent's move). -/
def twoFrameStrat (reply : List Nat → List Nat → Option (List Nat)) : Strat
  | Q' :: Q :: _ => reply Q Q'
  | _ => none

/-- C3 BRIDGE (stateful second player): WholeGame.TwoFrameWins gives the history
    guarantee.  The predecessor read by the strategy is, on consistent histories, the
    board established by the agent's own previous action (or P₀). -/
theorem twoFrame_secure {reply : List Nat → List Nat → Option (List Nat)} {P0 : List Nat}
    (hw : TwoFrameWins reply P0) : Secure .second (twoFrameStrat reply) P0 := by
  have inv : ∀ h, Cons .second (twoFrameStrat reply) P0 h →
      (mover h ≠ .second → TwoFrameWins reply (cur h)) ∧
      (mover h = .second → ∃ Q Q' t, h = Q' :: Q :: t ∧ TwoFrameWins reply Q ∧ Move Q Q') := by
    intro h hc
    induction hc with
    | init => exact ⟨fun _ => hw, fun h => by simp at h⟩
    | @opp h Q' hc' hne hmv ih =>
      refine ⟨fun h' => absurd (mover_cons_eq hne) h', fun _ => ?_⟩
      have hne' := legal_ne_nil (cons_legal hc')
      obtain ⟨Q, t, rfl⟩ : ∃ Q t, h = Q :: t := by cases h with
        | nil => exact absurd rfl hne'
        | cons Q t => exact ⟨Q, t, rfl⟩
      exact ⟨Q, Q', t, rfl, ih.1 hne, hmv⟩
    | @own h R hc' hm hσ hmv ih =>
      obtain ⟨Q, Q', t, rfl, hT, hQm⟩ := ih.2 hm
      refine ⟨fun _ => ?_, fun h' => absurd h' (mover_cons_ne hm)⟩
      cases hT with
      | intro _ _ _ hrest => exact hrest Q' R hQm hσ
  intro h hc hm
  obtain ⟨Q, Q', t, rfl, hT, hQm⟩ := (inv h hc).2 hm
  cases hT with
  | intro _ hsome hmove _ =>
    cases hs : reply Q Q' with
    | none => have := hsome Q' hQm; rw [hs] at this; cases this
    | some R => exact ⟨R, hs, hmove Q' R hQm hs⟩

/-- TWO-FRAME RESTORATION (second player, history-dependent): the player that feeds the
    previous board and the current board to the compiled LOCAL restoration network is
    weakly masterful on every B-bit family for the second role. -/
theorem twoFrame_weak : WeakMasteryFam (fun B P => Width B P) .second (fun B => twoFrameStrat (restReply B)) := by
  intro B P0 hw hwin
  exact secure_guarantee (twoFrame_secure (twoFrame_wins P0 hw ((roleWinnable_second P0).1 hwin)))

/-- STATE OF THE TWO-FRAME PLAYER: on every consistent history at the agent's turn, the
    predecessor it reads is either P₀ (first reply) or the board produced by its own
    previous action.  So the strategy needs one stored board (its last established board,
    as in WholeGame), not an oracle for the opponent's history. -/
theorem twoFrame_memory {reply : List Nat → List Nat → Option (List Nat)} {P0 : List Nat} {h : Hist}
    (hc : Cons .second (twoFrameStrat reply) P0 h) (hm : mover h = .second) :
    ∃ Q' Q t, h = Q' :: Q :: t ∧ ((t = [] ∧ Q = P0) ∨ twoFrameStrat reply t = some Q) := by
  cases hc with
  | init => simp at hm
  | own _ hm' _ _ => exact absurd hm (mover_cons_ne hm')
  | @opp g Q' hc' hne _ =>
    cases hc' with
    | init => exact ⟨Q', P0, [], rfl, Or.inl ⟨rfl, rfl⟩⟩
    | @opp t Q _ hne' _ => exact absurd (mover_cons_eq hne') hne
    | @own t Q _ _ hσ _ => exact ⟨Q', Q, t, rfl, Or.inr hσ⟩

/-! ## C4. Locality, strong versus weak mastery -/

/-- LOCALITY: if σ' agrees with σ on every σ-consistent history at the agent's turn, the two
    strategies have exactly the same consistent histories. -/
theorem cons_congr {r : Role} {σ σ' : Strat} {P0 : List Nat}
    (hag : ∀ h, Cons r σ P0 h → mover h = r → σ' h = σ h) (h : Hist) :
    Cons r σ P0 h ↔ Cons r σ' P0 h := by
  constructor
  · intro hc
    induction hc with
    | init => exact Cons.init
    | opp _ hne hmv ih => exact Cons.opp ih hne hmv
    | @own h Q hc' hm hσ hmv ih => exact Cons.own ih hm (by rw [hag h hc' hm]; exact hσ) hmv
  · intro hc
    induction hc with
    | init => exact Cons.init
    | opp _ hne hmv ih => exact Cons.opp ih hne hmv
    | @own h Q hc' hm hσ hmv ih => exact Cons.own ih hm (by rw [← hag h ih hm]; exact hσ) hmv

/-- LOCALITY OF THE GUARANTEE: changing a policy only at histories that are not reachable
    consistently with its own preceding actions (for instance after a counterfactual agent
    mistake) does not affect its winning guarantee. -/
theorem guarantee_congr {r : Role} {σ σ' : Strat} {P0 : List Nat}
    (hag : ∀ h, Cons r σ P0 h → mover h = r → σ' h = σ h) :
    Guarantee r σ P0 ↔ Guarantee r σ' P0 := by
  rw [← secure_iff_guarantee, ← secure_iff_guarantee]
  constructor
  · intro hs h hc hm
    have hc' := (cons_congr hag h).2 hc
    rw [hag h hc' hm]; exact hs h hc' hm
  · intro hs h hc hm
    rw [← hag h hc hm]; exact hs h ((cons_congr hag h).1 hc) hm

theorem weakMastery_congr {F : List Nat → Prop} {r : Role} {σ σ' : Strat}
    (hag : ∀ P0, F P0 → RoleWinnable r P0 → ∀ h, Cons r σ P0 h → mover h = r → σ' h = σ h) :
    WeakMastery F r σ ↔ WeakMastery F r σ' :=
  ⟨fun hw P0 hF hr => (guarantee_congr (hag P0 hF hr)).1 (hw P0 hF hr),
   fun hw P0 hF hr => (guarantee_congr (hag P0 hF hr)).2 (hw P0 hF hr)⟩

/-- Strong mastery (Definition def:mastery, first clause) relative to F and r: at EVERY
    legal history (arbitrary actions by both players) with the agent to move at an
    N-position, σ plays a move to a P-position. -/
def StrongMastery (F : List Nat → Prop) (r : Role) (σ : Strat) : Prop :=
  ∀ P0, F P0 → ∀ h, Legal P0 h → mover h = r → nimSum (cur h) ≠ 0 →
    ∃ Q, σ h = some Q ∧ Move (cur h) Q ∧ nimSum Q = 0

theorem strong_weak {F : List Nat → Prop} {r : Role} {σ : Strat} (hs : StrongMastery F r σ) :
    WeakMastery F r σ := by
  intro P0 hF hwin
  have inv : ∀ h, Cons r σ P0 h → (mover h = r → nimSum (cur h) ≠ 0) ∧ (mover h ≠ r → nimSum (cur h) = 0) := by
    intro h hc
    induction hc with
    | init =>
      cases r
      · exact ⟨fun _ => (roleWinnable_first P0).1 hwin, fun h => absurd rfl h⟩
      · exact ⟨fun h => by simp at h, fun _ => (roleWinnable_second P0).1 hwin⟩
    | @opp h Q hc' hne hmv ih =>
      exact ⟨fun _ => move_from_zero hmv (ih.2 hne), fun h' => absurd (mover_cons_eq hne) h'⟩
    | @own h Q hc' hm hσ hmv ih =>
      obtain ⟨Q', h1, _, h3⟩ := hs P0 hF h (cons_legal hc') hm (ih.1 hm)
      rw [hσ] at h1; cases h1
      exact ⟨fun h' => absurd h' (mover_cons_ne hm), fun _ => h3⟩
  refine secure_guarantee (fun h hc hm => ?_)
  obtain ⟨Q, h1, h2, _⟩ := hs P0 hF h (cons_legal hc) hm ((inv h hc).1 hm)
  exact ⟨Q, h1, h2⟩

theorem legal_width {B : Nat} {P0 : List Nat} {h : Hist} (hl : Legal P0 h) (hw : Width B P0) :
    Width B (cur h) := by
  induction hl with
  | init => exact hw
  | step _ hm ih => exact width_move ih hm

/-- The multi-head player is in fact STRONGLY masterful on B-bit families, for both roles. -/
theorem mh_strong (B : Nat) (r : Role) : StrongMastery (fun P => Width B P) r (ofSel (mhSelect B)) := by
  intro P0 hw h hl _ hnz
  have hwh : Width B (cur h) := legal_width hl hw
  obtain ⟨i, v, hd, hz⟩ := (Controller.decision_correct (cur h)).2.2 hnz
  obtain ⟨x, _, _, hmv⟩ := (Controller.decision_correct (cur h)).2.1 i v hd
  refine ⟨(cur h).set i v, ?_, hmv, hz⟩
  unfold ofSel; rw [mhSelect_eq hwh]; simp [Controller.ctrlSel, hd]

/-- SEPARATION EXAMPLE: from (3) the first player takes all three stones; the policy is
    undefined everywhere else. -/
def sep3 : Strat := fun h => if cur h = [3] then some [0] else none

theorem sep3_weak : WeakMastery (fun P => P = [3]) .first sep3 := by
  intro P0 hP _
  subst hP
  refine secure_guarantee (fun h hc hm => ?_)
  have key : ∀ h, Cons .first sep3 [3] h → (mover h = .first → h = [[3]]) ∧ (mover h ≠ .first → Terminal (cur h)) := by
    intro h hc
    induction hc with
    | init => exact ⟨fun _ => rfl, fun h => absurd rfl h⟩
    | @opp h Q hc' hne hmv ih =>
      exact absurd hmv ((terminal_iff_no_move _).1 (ih.2 hne) Q)
    | @own h Q hc' hm' hσ hmv ih =>
      have e := ih.1 hm'
      subst e
      have hQ : Q = [0] := by simp [sep3, cur] at hσ; exact hσ.symm
      subst hQ
      exact ⟨fun h' => absurd h' (mover_cons_ne hm'), fun _ => by intro x hx; simpa using hx⟩
  have e := (key h hc).1 hm
  subst e
  exact ⟨[0], by simp [sep3, cur], ⟨[], 3, [], 0, rfl, rfl, by omega⟩⟩

/-- … but it is not strongly masterful: after the counterfactual agent mistake 3 → 2 and the
    reply 2 → 1, the agent is to move at the N-position (1) and its policy has no move. -/
theorem sep3_not_strong : ¬ StrongMastery (fun P => P = [3]) .first sep3 := by
  intro hs
  have hl : Legal [3] [[1], [2], [3]] :=
    Legal.step (Legal.step Legal.init ⟨[], 3, [], 2, rfl, rfl, by omega⟩) ⟨[], 2, [], 1, rfl, rfl, by omega⟩
  obtain ⟨Q, hQ, _⟩ := hs [3] rfl _ hl rfl (by decide)
  simp [sep3, cur] at hQ

/-! ## Axiom checks -/
#print axioms Role.other_ne
#print axioms Role.eq_other_of_ne
#print axioms cur_cons
#print axioms mover_cons
#print axioms mover_init
#print axioms mover_cons_eq
#print axioms mover_cons_ne
#print axioms legal_sum
#print axioms legal_length
#print axioms legal_ne_nil
#print axioms legal_last
#print axioms legal_pair
#print axioms cons_legal
#print axioms cons_own
#print axioms secure_extend
#print axioms secure_terminal
#print axioms play_own
#print axioms play_own_fail
#print axioms play_opp
#print axioms play_opp_fail
#print axioms play_finishes
#print axioms play_fuel
#print axioms terminal_start
#print axioms secure_play
#print axioms secure_guarantee
#print axioms subFirstPos_move
#print axioms subFirstPos_isSome
#print axioms subFirst_legal
#print axioms followD_legal
#print axioms follow_legal
#print axioms followD_play
#print axioms follow_play
#print axioms followD_reach
#print axioms secure_iff_guarantee
#print axioms optOpp_legal
#print axioms optOpp_play
#print axioms optLike_play
#print axioms guarantee_optimal
#print axioms wins_secure
#print axioms secondWins_secure
#print axioms zeroSel_wins
#print axioms le_sum_of_mem
#print axioms width_sum
#print axioms roleWinnable_first
#print axioms roleWinnable_second
#print axioms roleWinnable_game
#print axioms roleWinnable_exclusive
#print axioms weakMastery_iff
#print axioms weakMastery_vacuous
#print axioms weakMastery_restrict
#print axioms weakMastery_iff_optimal
#print axioms pairing_guarantee
#print axioms pairing_weak
#print axioms pairing_first_vacuous
#print axioms pairNetSel_eq
#print axioms pairing_net_weak
#print axioms pairing_resources
#print axioms mh_weak
#print axioms twoFrame_secure
#print axioms twoFrame_weak
#print axioms twoFrame_memory
#print axioms cons_congr
#print axioms guarantee_congr
#print axioms weakMastery_congr
#print axioms strong_weak
#print axioms legal_width
#print axioms mh_strong
#print axioms sep3_weak
#print axioms sep3_not_strong

end Mastery
end NimAudit
