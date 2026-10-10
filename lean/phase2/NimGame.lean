import NimRollout

/- Phase 2, targets 1 and 2.  Written by Claude for the independent review
   (9 October 2026).  Lean 4.26.0, core/Std only.  Imports the unchanged
   NimCore.lean and NimRollout.lean.

   Target 1  Normal-play semantics of Nim, the classical characterisation
             (losing iff nim-sum zero), reconstruction of the nim-sum from the B
             structured rollout outcomes, a deterministic move selector driven by
             that reconstruction, and the adversarial guarantee: the selector wins
             from every nonzero position against every legal opponent.  Also the
             finite bound B*N*(2^B-1) on simulated rollout moves.
   Target 2  The parity reduction on boards (2, b_1, ..., b_m).

   Nothing here formalises circuits, AC0, or probability. -/

namespace NimAudit
namespace Game

open Rollout

/-! ## Target 1A: legal moves and normal-play semantics -/

/-- An ordinary legal Nim move: exactly one heap strictly decreases. -/
def Move (p q : List Nat) : Prop :=
  ∃ pre x post y, p = pre ++ x :: post ∧ q = pre ++ y :: post ∧ y < x

/-- Terminal board: every heap is empty. -/
def Terminal (p : List Nat) : Prop := ∀ x ∈ p, x = 0

/-- B-bit board: every heap is below 2^B. -/
def Width (B : Nat) (p : List Nat) : Prop := ∀ x ∈ p, x < 2 ^ B

/- Normal play: `Win p` (an N-position) and `Lose p` (a P-position), for the
   player to move.  A player who cannot move loses. -/
mutual
inductive Win : List Nat → Prop
  | intro (p q : List Nat) : Move p q → Lose q → Win p
inductive Lose : List Nat → Prop
  | intro (p : List Nat) : (∀ q, Move p q → Win q) → Lose p
end

theorem move_sum_lt {p q : List Nat} (hm : Move p q) : q.sum < p.sum := by
  obtain ⟨pre, x, post, y, rfl, rfl, hlt⟩ := hm
  simp only [List.sum_append_nat, List.sum_cons]
  omega

theorem terminal_iff_no_move (p : List Nat) : Terminal p ↔ ∀ q, ¬ Move p q := by
  constructor
  · intro ht q ⟨pre, x, post, y, hp, _, hlt⟩
    have : x = 0 := ht x (by rw [hp]; simp)
    omega
  · intro hno x hx
    obtain ⟨pre, post, rfl⟩ := List.append_of_mem hx
    by_cases h0 : x = 0
    · exact h0
    · exact absurd ⟨pre, x, post, 0, rfl, rfl, by omega⟩ (hno (pre ++ 0 :: post))

theorem terminal_lose {p : List Nat} (ht : Terminal p) : Lose p :=
  Lose.intro p (fun q hm => absurd hm ((terminal_iff_no_move p).1 ht q))

theorem xor_eq_zero_imp {x y : Nat} (h : x ^^^ y = 0) : x = y := by
  have := xor_cancel_left x y
  rw [h, Nat.xor_zero] at this
  exact this

theorem nimSum_move {pre post : List Nat} {x y : Nat} :
    nimSum (pre ++ y :: post) = nimSum (pre ++ x :: post) ^^^ (x ^^^ y) := by
  rw [one_heap_update pre post x y, Nat.xor_assoc]

/-- Every legal move from a zero-nim-sum board reaches a nonzero nim-sum. -/
theorem move_from_zero {p q : List Nat} (hm : Move p q) (h0 : nimSum p = 0) :
    nimSum q ≠ 0 := by
  obtain ⟨pre, x, post, y, rfl, rfl, hlt⟩ := hm
  rw [nimSum_move, h0, Nat.zero_xor]
  intro h
  have := xor_eq_zero_imp h
  omega

/-- From a nonzero nim-sum there is a legal move to nim-sum zero (from NimRollout). -/
theorem exists_move_to_zero {p : List Nat} (h : nimSum p ≠ 0) :
    ∃ q, Move p q ∧ nimSum q = 0 := by
  obtain ⟨pre, x, post, rfl, hlt, hz⟩ := exists_decreasing_heap p h
  exact ⟨_, ⟨pre, x, post, _, rfl, rfl, hlt⟩, hz⟩

theorem lose_of_zero_win_of_ne (p : List Nat) :
    (nimSum p = 0 → Lose p) ∧ (nimSum p ≠ 0 → Win p) := by
  constructor
  · intro h
    exact Lose.intro p (fun q hm =>
      have := move_sum_lt hm
      (lose_of_zero_win_of_ne q).2 (move_from_zero hm h))
  · intro h
    obtain ⟨q, hm, hq⟩ := exists_move_to_zero h
    have := move_sum_lt hm
    exact Win.intro p q hm ((lose_of_zero_win_of_ne q).1 hq)
termination_by p.sum

theorem not_win_and_lose (p : List Nat) (hw : Win p) (hl : Lose p) : False := by
  cases hw with
  | intro _ q hm hlq =>
    cases hl with
    | intro _ hall =>
      have := move_sum_lt hm
      exact not_win_and_lose q (hall q hm) hlq
termination_by p.sum

/-- CLASSICAL CHARACTERISATION (paper Theorem nim-win). -/
theorem lose_iff (p : List Nat) : Lose p ↔ nimSum p = 0 := by
  constructor
  · intro hl
    by_cases h : nimSum p = 0
    · exact h
    · exact (not_win_and_lose p ((lose_of_zero_win_of_ne p).2 h) hl).elim
  · exact (lose_of_zero_win_of_ne p).1

theorem win_iff (p : List Nat) : Win p ↔ nimSum p ≠ 0 := by
  constructor
  · intro hw h
    exact not_win_and_lose p hw ((lose_of_zero_win_of_ne p).1 h)
  · exact (lose_of_zero_win_of_ne p).2

/-! ### The adversarial guarantee -/

/-- `Wins sel p`: the player to move at `p`, always playing the successor chosen by
    `sel`, wins against EVERY legal opponent.  The selected move is legal, and after
    every legal opponent reply the player is again in a `Wins` position.  Because
    the predicate is inductive, every such play is finite and ends with the
    opponent facing a terminal board (normal play: the opponent loses). -/
inductive Wins (sel : List Nat → Option (List Nat)) : List Nat → Prop
  | intro (p q : List Nat) : sel p = some q → Move p q →
      (∀ r, Move q r → Wins sel r) → Wins sel p

/-- `Wins` is sound for the game semantics. -/
theorem wins_sound {sel : List Nat → Option (List Nat)} {p : List Nat}
    (h : Wins sel p) : Win p := by
  induction h with
  | intro p q _ hm _ ih => exact Win.intro p q hm (Lose.intro q ih)

/-! ## Target 1B: rollout measurements and reconstruction of the nim-sum -/

/-- Rollout outcome RO_{pi_j}(P) as a game: both players follow pi_j; the result is
    `true` iff the player to move at P (the first player) wins under normal play.
    At a terminal start it is `false`. -/
def rolloutWinner (j : Nat) (p : List Nat) : Bool :=
  match h : policyStep j p with
  | none => false
  | some q => !rolloutWinner j q
termination_by rolloutCount j p
decreasing_by
  have := policyMove_count (policyStep_some h)
  omega

theorem testBit0_succ (n : Nat) : (n + 1).testBit 0 = !(n.testBit 0) := by
  rw [lowBit_add]
  cases n.testBit 0 <;> rfl

/-- The first player wins the rollout iff the number of rollout moves is odd. -/
theorem rolloutWinner_eq (j : Nat) (p : List Nat) :
    rolloutWinner j p = (rolloutMoves j p).testBit 0 := by
  induction p using rolloutWinner.induct j with
  | case1 p h =>
    rw [rolloutWinner, rolloutMoves, h]
    show false = (0 : Nat).testBit 0
    simp
  | case2 p q h ih =>
    rw [rolloutWinner, rolloutMoves, h]
    show (!rolloutWinner j q) = (rolloutMoves j q + 1).testBit 0
    rw [ih, testBit0_succ]

/-- RO_{pi_0}(P) = sigma_0 and RO_{pi_j}(P) = sigma_j XOR sigma_0 (j ≥ 1), proved for
    the executed rollout. -/
theorem rolloutWinner_channel (j : Nat) (p : List Nat) :
    rolloutWinner j p = channel j (nimSum p) := by
  rw [rolloutWinner_eq]
  exact rolloutMoves_parity j p

/-- The number with bits f 0, ..., f (B-1). -/
def ofBits : Nat → (Nat → Bool) → Nat
  | 0, _ => 0
  | B + 1, f => 2 ^ B * (if f B then 1 else 0) + ofBits B f

theorem ofBits_lt (B : Nat) (f : Nat → Bool) : ofBits B f < 2 ^ B := by
  induction B with
  | zero => simp [ofBits]
  | succ B ih =>
    simp only [ofBits, Nat.pow_succ]
    split <;> omega

theorem testBit_ofBits (B : Nat) (f : Nat → Bool) (i : Nat) :
    (ofBits B f).testBit i = (decide (i < B) && f i) := by
  induction B with
  | zero => simp [ofBits]
  | succ B ih =>
    simp only [ofBits]
    rw [Nat.testBit_two_pow_mul_add _ (ofBits_lt B f)]
    by_cases hi : i < B
    · simp [hi, ih, show i < B + 1 by omega]
    · by_cases hiB : i = B
      · subst hiB; cases f i <;> simp
      · have h1 : ¬ i < B + 1 := by omega
        have h2 : (1 : Nat).testBit (i - B) = false :=
          Nat.testBit_lt_two_pow (Nat.one_lt_two_pow (by omega))
        simp only [hi, if_false, h1, decide_false, Bool.false_and]
        cases hf : f B <;> simp [h2]

/-- Bit recovery from the outcomes o j = RO_{pi_j}: sigma_0 = o 0, sigma_j = o j XOR o 0. -/
def recoverBit (o : Nat → Bool) (j : Nat) : Bool :=
  if j = 0 then o 0 else xor (o j) (o 0)

/-- The nim-sum reconstructed from the B rollout outcomes o 0, ..., o (B-1). -/
def reconstruct (B : Nat) (o : Nat → Bool) : Nat := ofBits B (recoverBit o)

/-- The B actual rollout measurements of board p. -/
def outcomes (p : List Nat) : Nat → Bool := fun j => rolloutWinner j p

theorem nimSum_lt {B : Nat} {p : List Nat} (hw : Width B p) : nimSum p < 2 ^ B := by
  induction p with
  | nil => simp only [nimSum]; exact Nat.two_pow_pos B
  | cons x t ih =>
    exact Nat.xor_lt_two_pow (hw x (by simp))
      (ih (fun y hy => hw y (List.mem_cons_of_mem _ hy)))

/-- RECONSTRUCTION: on a B-bit board (any N, including the empty and terminal
    boards), the B rollout outcomes determine the full nim-sum. -/
theorem reconstruct_eq {B : Nat} {p : List Nat} (hw : Width B p) :
    reconstruct B (outcomes p) = nimSum p := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [reconstruct, testBit_ofBits]
  by_cases hi : i < B
  · simp only [hi, decide_true, Bool.true_and, recoverBit, outcomes, rolloutWinner_channel]
    by_cases h0 : i = 0
    · subst h0; simp [channel]
    · simp only [h0, if_false, channel, if_true]
      cases (nimSum p).testBit i <;> cases (nimSum p).testBit 0 <;> rfl
  · simp only [hi, decide_false, Bool.false_and]
    symm
    apply Nat.testBit_lt_two_pow
    exact Nat.lt_of_lt_of_le (nimSum_lt hw) (Nat.pow_le_pow_right (by decide) (by omega))

/-! ## Target 1C: the selected move and the winning strategy -/

/-- Replace the first heap x with x ^^^ s < x by x ^^^ s. -/
def cancelFirst (s : Nat) : List Nat → Option (List Nat)
  | [] => none
  | x :: t => if x ^^^ s < x then some ((x ^^^ s) :: t) else (cancelFirst s t).map (x :: ·)

/-- Move selector from a claimed nim-sum s: if s ≠ 0 cancel s at the first qualifying
    heap; otherwise (or if no heap qualifies) subtract 1 from the first nonzero heap;
    halt (`none`) only on a terminal board. -/
def selectMove (s : Nat) (p : List Nat) : Option (List Nat) :=
  match (if s = 0 then none else cancelFirst s p) with
  | some q => some q
  | none => subFirstPos p

/-- The agent: reconstruct the nim-sum from the B root rollouts, then select. -/
def agent (B : Nat) (p : List Nat) : Option (List Nat) :=
  selectMove (reconstruct B (outcomes p)) p

theorem cancelFirst_some {s : Nat} {p q : List Nat} (h : cancelFirst s p = some q) :
    ∃ pre x post, p = pre ++ x :: post ∧ x ^^^ s < x ∧ q = pre ++ (x ^^^ s) :: post := by
  induction p generalizing q with
  | nil => simp [cancelFirst] at h
  | cons x t ih =>
    by_cases hx : x ^^^ s < x
    · simp only [cancelFirst, hx, if_true, Option.some.injEq] at h
      exact ⟨[], x, t, rfl, hx, h.symm⟩
    · simp only [cancelFirst, hx, if_false] at h
      cases ht : cancelFirst s t with
      | none => simp [ht] at h
      | some a =>
        simp only [ht, Option.map_some, Option.some.injEq] at h
        obtain ⟨pre, y, post, h1, h2, h3⟩ := ih ht
        exact ⟨x :: pre, y, post, by simp [h1], h2, by rw [← h, h3]; rfl⟩

theorem cancelFirst_none {s : Nat} {p : List Nat} (h : cancelFirst s p = none) :
    ∀ x ∈ p, ¬ x ^^^ s < x := by
  induction p with
  | nil => simp
  | cons x t ih =>
    by_cases hx : x ^^^ s < x
    · simp [cancelFirst, hx] at h
    · simp only [cancelFirst, hx, if_false] at h
      cases ht : cancelFirst s t with
      | some a => simp [ht] at h
      | none =>
        intro y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · exact hx
        · exact ih ht y hy

theorem cancelFirst_terminal {s : Nat} {p : List Nat} (ht : Terminal p) :
    cancelFirst s p = none := by
  induction p with
  | nil => rfl
  | cons x t ih =>
    have hx : x = 0 := ht x (by simp)
    subst hx
    simp [cancelFirst, ih (fun y hy => ht y (List.mem_cons_of_mem _ hy))]

theorem subFirstPos_terminal {p : List Nat} (ht : Terminal p) : subFirstPos p = none := by
  induction p with
  | nil => rfl
  | cons x t ih =>
    have hx : x = 0 := ht x (by simp)
    subst hx
    simp [subFirstPos, ih (fun y hy => ht y (List.mem_cons_of_mem _ hy))]

/-- Every selected move is a legal Nim move, whatever claimed nim-sum is used. -/
theorem selectMove_legal {s : Nat} {p q : List Nat} (h : selectMove s p = some q) :
    Move p q := by
  unfold selectMove at h
  split at h
  · next q' hq' =>
    cases h
    by_cases hs : s = 0
    · simp [hs] at hq'
    · simp only [hs, if_false] at hq'
      obtain ⟨pre, x, post, rfl, hlt, rfl⟩ := cancelFirst_some hq'
      exact ⟨pre, x, post, _, rfl, rfl, hlt⟩
  · obtain ⟨pre, x, post, rfl, hx, rfl⟩ := subFirstPos_some h
    exact ⟨pre, x, post, x - 1, rfl, rfl, by omega⟩

/-- The selector halts exactly on terminal boards. -/
theorem selectMove_none_iff (s : Nat) (p : List Nat) :
    selectMove s p = none ↔ Terminal p := by
  constructor
  · intro h
    unfold selectMove at h
    split at h
    · cases h
    · exact subFirstPos_none h
  · intro ht
    unfold selectMove
    rw [cancelFirst_terminal ht, subFirstPos_terminal ht]
    split <;> simp_all

/-- With the true nonzero nim-sum, the selected move is legal and reaches nim-sum zero. -/
theorem selectMove_zero {p : List Nat} (h : nimSum p ≠ 0) :
    ∃ q, selectMove (nimSum p) p = some q ∧ Move p q ∧ nimSum q = 0 := by
  cases hc : cancelFirst (nimSum p) p with
  | none =>
    obtain ⟨pre, x, post, hp, hlt, _⟩ := exists_decreasing_heap p h
    exact absurd hlt (cancelFirst_none hc x (by rw [hp]; simp))
  | some q =>
    refine ⟨q, ?_, ?_, ?_⟩
    · simp [selectMove, h, hc]
    · exact selectMove_legal (s := nimSum p) (by simp [selectMove, h, hc])
    · obtain ⟨pre, x, post, hp, _, rfl⟩ := cancelFirst_some hc
      rw [hp]
      exact move_to_zero_algebra pre post x

theorem width_move {B : Nat} {p q : List Nat} (hw : Width B p) (hm : Move p q) :
    Width B q := by
  obtain ⟨pre, x, post, y, rfl, rfl, hlt⟩ := hm
  intro z hz
  simp only [List.mem_append, List.mem_cons] at hz
  rcases hz with hz | rfl | hz
  · exact hw z (by simp [hz])
  · exact Nat.lt_trans hlt (hw x (by simp))
  · exact hw z (by simp [hz])

/-- The agent's move is the rollout-reconstructed selection; on B-bit boards it
    coincides with selection from the true nim-sum. -/
theorem agent_eq {B : Nat} {p : List Nat} (hw : Width B p) :
    agent B p = selectMove (nimSum p) p := by
  rw [agent, reconstruct_eq hw]

theorem agent_legal {B : Nat} {p q : List Nat} (h : agent B p = some q) : Move p q :=
  selectMove_legal h

theorem agent_none_iff (B : Nat) (p : List Nat) : agent B p = none ↔ Terminal p :=
  selectMove_none_iff _ p

/-- END-TO-END STRATEGY GUARANTEE (Target 1C): on B-bit boards, the agent that
    queries the B structured rollouts, reconstructs the nim-sum and plays the
    selected move wins from every nonzero-nim-sum position against every legal
    opponent. -/
theorem agent_wins {B : Nat} (p : List Nat) (hw : Width B p) (h : nimSum p ≠ 0) :
    Wins (agent B) p := by
  obtain ⟨q, hsel, hm, hq⟩ := selectMove_zero h
  refine Wins.intro p q (by rw [agent_eq hw]; exact hsel) hm ?_
  intro r hr
  have h1 := move_sum_lt hm
  have h2 := move_sum_lt hr
  exact agent_wins r (width_move (width_move hw hm) hr) (move_from_zero hr hq)
termination_by p.sum

/-- Strong mastery on B-bit boards: from every N-position the agent wins. -/
theorem agent_wins_of_win {B : Nat} {p : List Nat} (hw : Width B p) (h : Win p) :
    Wins (agent B) p :=
  agent_wins p hw ((win_iff p).1 h)

/-- At a P-position no winning move exists; the agent still plays a legal move,
    or halts exactly when the board is terminal. -/
theorem agent_at_zero {B : Nat} {p : List Nat} (h : nimSum p = 0) :
    Lose p ∧ (agent B p = none ↔ Terminal p) ∧ (∀ q, agent B p = some q → Move p q) :=
  ⟨(lose_iff p).2 h, agent_none_iff B p, fun _ hq => agent_legal hq⟩

/-- Restoration / invariant maintenance: once the agent has reached a zero-nim-sum
    B-bit board, it wins after every legal opponent reply. -/
theorem agent_maintains {B : Nat} {q : List Nat} (hw : Width B q) (hq : nimSum q = 0) :
    ∀ r, Move q r → Wins (agent B) r :=
  fun r hr => agent_wins r (width_move hw hr) (move_from_zero hr hq)

/-- Two-frame restoration selector (paper Prop. restore / Thm search-gap (iii)):
    from the predecessor Q and current board Q', cancel delta = nim(Q) XOR nim(Q'). -/
def restore (Q Q' : List Nat) : Option (List Nat) :=
  cancelFirst (nimSum Q ^^^ nimSum Q') Q'

theorem restore_correct {Q Q' : List Nat} (h0 : nimSum Q = 0) (hm : Move Q Q') :
    ∃ R, restore Q Q' = some R ∧ Move Q' R ∧ nimSum R = 0 := by
  have hne := move_from_zero hm h0
  have hd : nimSum Q ^^^ nimSum Q' = nimSum Q' := by rw [h0, Nat.zero_xor]
  obtain ⟨R, hsel, hmR, hR⟩ := selectMove_zero hne
  refine ⟨R, ?_, hmR, hR⟩
  unfold restore
  rw [hd]
  simp only [selectMove, hne, if_false] at hsel
  split at hsel
  · next q' hq' => cases hsel; exact hq'
  · next _ hnone =>
    obtain ⟨pre, x, post, hp, hlt, _⟩ := exists_decreasing_heap Q' hne
    exact absurd hlt (cancelFirst_none hnone x (by rw [hp]; simp))

/-! ## Target 1D: finite bound on simulated rollout moves -/

theorem heapCount_le (j h : Nat) : heapCount j h ≤ h := by
  unfold heapCount
  have hd := Nat.div_add_mod h (2 ^ j)
  have hm : h / 2 ^ j ≤ 2 ^ j * (h / 2 ^ j) := Nat.le_mul_of_pos_left _ (Nat.two_pow_pos j)
  generalize 2 ^ j * (h / 2 ^ j) = t at hd hm
  omega

theorem rolloutMoves_le {B j : Nat} {p : List Nat} (hw : Width B p) :
    rolloutMoves j p ≤ p.length * (2 ^ B - 1) := by
  rw [rolloutMoves_eq]
  induction p with
  | nil => simp [rolloutCount]
  | cons x t ih =>
    have hx : x < 2 ^ B := hw x (by simp)
    have ht := ih (fun y hy => hw y (List.mem_cons_of_mem _ hy))
    have hc := heapCount_le j x
    have e : rolloutCount j (x :: t) = heapCount j x + rolloutCount j t := by
      simp [rolloutCount]
    rw [e, List.length_cons, Nat.succ_mul]
    omega

/-- Total simulated moves of the B root rollouts. -/
def totalRolloutMoves (B : Nat) (p : List Nat) : Nat :=
  ((List.range B).map (fun j => rolloutMoves j p)).sum

theorem totalRolloutMoves_le {B : Nat} {p : List Nat} (hw : Width B p) :
    totalRolloutMoves B p ≤ B * (p.length * (2 ^ B - 1)) := by
  unfold totalRolloutMoves
  have key : ∀ k, ((List.range k).map (fun j => rolloutMoves j p)).sum ≤
      k * (p.length * (2 ^ B - 1)) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [List.range_succ, List.map_append, List.sum_append_nat, Nat.succ_mul]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
      have := rolloutMoves_le (j := k) hw
      omega
  exact key B

/-! ## Target 2: the parity reduction -/

/-- XOR of a list of Booleans (false on the empty list). -/
def parity : List Bool → Bool
  | [] => false
  | b :: bs => xor b (parity bs)

/-- The board (2, b_1, ..., b_m), Boolean heaps encoded as 0/1. -/
def encode (bs : List Bool) : List Nat := 2 :: bs.map Bool.toNat

theorem nimSum_bits (bs : List Bool) :
    nimSum (bs.map Bool.toNat) = (parity bs).toNat := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    simp only [List.map_cons, nimSum, ih, parity]
    cases b <;> cases parity bs <;> rfl

theorem nimSum_encode (bs : List Bool) : nimSum (encode bs) = 2 ^^^ (parity bs).toNat := by
  simp [encode, nimSum, nimSum_bits]

theorem nimSum_encode_ne (bs : List Bool) : nimSum (encode bs) ≠ 0 := by
  rw [nimSum_encode]
  cases parity bs <;> decide

/-- The reduced board: leading heap replaced by the parity. -/
def reduced (bs : List Bool) : List Nat := (parity bs).toNat :: bs.map Bool.toNat

theorem reduced_move (bs : List Bool) :
    Move (encode bs) (reduced bs) ∧ nimSum (reduced bs) = 0 := by
  refine ⟨⟨[], 2, bs.map Bool.toNat, (parity bs).toNat, rfl, rfl, ?_⟩, ?_⟩
  · cases parity bs <;> decide
  · simp only [reduced, nimSum, nimSum_bits]
    exact Nat.xor_self _

/-- UNIQUENESS: the only legal move from (2, b_1, ..., b_m) to nim-sum zero sets the
    leading heap to b_1 XOR ... XOR b_m.  Holds for every m, including m = 0. -/
theorem unique_zero_move (bs : List Bool) (q : List Nat)
    (hm : Move (encode bs) q) (hq : nimSum q = 0) : q = reduced bs := by
  obtain ⟨pre, x, post, y, hp, rfl, hlt⟩ := hm
  cases pre with
  | nil =>
    simp only [encode, List.nil_append, List.cons.injEq] at hp
    obtain ⟨rfl, rfl⟩ := hp
    simp only [List.nil_append, nimSum, nimSum_bits] at hq
    have := xor_eq_zero_imp hq
    simp [reduced, this]
  | cons h pre' =>
    simp only [encode, List.cons_append, List.cons.injEq] at hp
    obtain ⟨rfl, hM⟩ := hp
    have hx1 : x ≤ 1 := by
      have hmem : x ∈ bs.map Bool.toNat := by rw [hM]; simp
      obtain ⟨b, _, rfl⟩ := List.mem_map.mp hmem
      exact Bool.toNat_le b
    have hx : x = 1 := by omega
    have hy : y = 0 := by omega
    subst hx; subst hy
    exfalso
    have e1 : nimSum (pre' ++ 0 :: post) = nimSum (pre' ++ 1 :: post) ^^^ (1 ^^^ 0) :=
      nimSum_move
    rw [← hM, nimSum_bits] at e1
    simp only [List.cons_append, nimSum, e1] at hq
    revert hq
    cases parity bs <;> decide

/-- Every winning-move selector outputs the reduced board, hence the parity, on
    (2, b_1, ..., b_m).  The hypothesis uses the normal-play semantics. -/
theorem winning_selector_parity (sel : List Nat → Option (List Nat))
    (hsel : ∀ p, Win p → ∃ q, sel p = some q ∧ Move p q ∧ Lose q) (bs : List Bool) :
    sel (encode bs) = some (reduced bs) := by
  have hw : Win (encode bs) := (win_iff _).2 (nimSum_encode_ne bs)
  obtain ⟨q, hs, hm, hl⟩ := hsel _ hw
  rw [hs, unique_zero_move bs q hm ((lose_iff q).1 hl)]

/-- The rollout agent (B = 2) computes the parity on these boards. -/
theorem agent_parity (bs : List Bool) : agent 2 (encode bs) = some (reduced bs) := by
  have hw : Width 2 (encode bs) := by
    intro x hx
    simp only [encode, List.mem_cons, List.mem_map] at hx
    rcases hx with rfl | ⟨b, _, rfl⟩
    · decide
    · have := Bool.toNat_le b; omega
  obtain ⟨q, hs, hm, hq⟩ := selectMove_zero (nimSum_encode_ne bs)
  rw [agent_eq hw, hs, unique_zero_move bs q hm hq]

/-- Read the parity bit off a selector's output (the new leading heap). -/
def decodeHead : Option (List Nat) → Bool
  | some (x :: _) => x == 1
  | _ => false

theorem decode_reduced (bs : List Bool) : decodeHead (some (reduced bs)) = parity bs := by
  simp only [decodeHead, reduced]
  cases parity bs <;> rfl

/-- CONDITIONAL COMPLEXITY CONSEQUENCE (logic only).  For ANY predicate `C` on
    Boolean functions and ANY predicate `S` on selectors, assuming
      (closure)  S sel implies C (bs ↦ decodeHead (sel (encode bs))), and
      (hardness) ¬ C parity,
    no selector satisfying S is a winning-move selector.  Instantiating C as
    "computable by polynomial-size constant-depth circuits" requires the
    closure of that class under the encoding/decoding, and the parity lower
    bound; NEITHER is formalised here.  They are explicit hypotheses. -/
theorem no_winning_selector_of_hardness
    (C : (List Bool → Bool) → Prop) (S : (List Nat → Option (List Nat)) → Prop)
    (closure : ∀ sel, S sel → C (fun bs => decodeHead (sel (encode bs))))
    (hard : ¬ C parity) (sel : List Nat → Option (List Nat)) (hS : S sel) :
    ¬ (∀ p, Win p → ∃ q, sel p = some q ∧ Move p q ∧ Lose q) := by
  intro hsel
  apply hard
  have e : (fun bs => decodeHead (sel (encode bs))) = parity := by
    funext bs
    rw [winning_selector_parity sel hsel bs, decode_reduced]
  rw [← e]
  exact closure sel hS


#print axioms move_sum_lt
#print axioms terminal_iff_no_move
#print axioms terminal_lose
#print axioms xor_eq_zero_imp
#print axioms nimSum_move
#print axioms move_from_zero
#print axioms exists_move_to_zero
#print axioms lose_of_zero_win_of_ne
#print axioms not_win_and_lose
#print axioms lose_iff
#print axioms win_iff
#print axioms wins_sound
#print axioms testBit0_succ
#print axioms rolloutWinner_eq
#print axioms rolloutWinner_channel
#print axioms ofBits_lt
#print axioms testBit_ofBits
#print axioms nimSum_lt
#print axioms reconstruct_eq
#print axioms cancelFirst_some
#print axioms cancelFirst_none
#print axioms cancelFirst_terminal
#print axioms subFirstPos_terminal
#print axioms selectMove_legal
#print axioms selectMove_none_iff
#print axioms selectMove_zero
#print axioms width_move
#print axioms agent_eq
#print axioms agent_legal
#print axioms agent_none_iff
#print axioms agent_wins
#print axioms agent_wins_of_win
#print axioms agent_at_zero
#print axioms agent_maintains
#print axioms restore_correct
#print axioms heapCount_le
#print axioms rolloutMoves_le
#print axioms totalRolloutMoves_le
#print axioms nimSum_bits
#print axioms nimSum_encode
#print axioms nimSum_encode_ne
#print axioms reduced_move
#print axioms unique_zero_move
#print axioms winning_selector_parity
#print axioms agent_parity
#print axioms decode_reduced
#print axioms no_winning_selector_of_hardness

end Game
end NimAudit
