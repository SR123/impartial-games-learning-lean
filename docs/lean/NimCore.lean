import Std

/- Elementary algebra for the revised Nim paper. Authored locally by Codex.
   This file does not formalise AC0, the correlation theorem, or neural training. -/
namespace NimAudit

def nimSum : List Nat → Nat
  | [] => 0
  | h :: t => h ^^^ nimSum t

def scan (initial : Nat) (rows : List Nat) : Nat :=
  rows.foldl (fun acc row => acc ^^^ row) initial

theorem xor_left_comm (a b c : Nat) : a ^^^ (b ^^^ c) = b ^^^ (a ^^^ c) := by
  ac_rfl

@[simp] theorem xor_cancel_left (a b : Nat) : a ^^^ (a ^^^ b) = b := by
  rw [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]

theorem nimSum_append (xs ys : List Nat) :
    nimSum (xs ++ ys) = nimSum xs ^^^ nimSum ys := by
  induction xs with
  | nil => simp [nimSum]
  | cons h t ih => simp [nimSum, ih, Nat.xor_assoc]

theorem scan_invariant (rows : List Nat) (initial : Nat) :
    scan initial rows = initial ^^^ nimSum rows := by
  induction rows generalizing initial with
  | nil => simp [scan, nimSum]
  | cons h t ih =>
    change scan (initial ^^^ h) t = initial ^^^ (h ^^^ nimSum t)
    rw [ih, Nat.xor_assoc]

theorem scan_from_zero (rows : List Nat) : scan 0 rows = nimSum rows := by
  simp [scan_invariant]

theorem one_heap_difference (pre post : List Nat) (a b : Nat) :
    nimSum (pre ++ a :: post) ^^^ nimSum (pre ++ b :: post) = a ^^^ b := by
  simp [nimSum_append, nimSum, Nat.xor_comm, xor_left_comm]

theorem one_heap_update (pre post : List Nat) (a b : Nat) :
    nimSum (pre ++ b :: post) = nimSum (pre ++ a :: post) ^^^ a ^^^ b := by
  simp [nimSum_append, nimSum, Nat.xor_comm, xor_left_comm]

theorem matching_deltas_restore_original (q q' r : Nat)
    (matched : q ^^^ q' = q' ^^^ r) : r = q := by
  have eq := congrArg (fun z => q' ^^^ z) matched
  simpa [Nat.xor_assoc, Nat.xor_comm, xor_left_comm] using eq.symm

theorem conditional_restoration (q q' r : Nat)
    (zero : q = 0) (matched : q ^^^ q' = q' ^^^ r) : r = 0 := by
  exact (matching_deltas_restore_original q q' r matched).trans zero

theorem move_to_zero_algebra (pre post : List Nat) (heap : Nat) :
    nimSum (pre ++ (heap ^^^ nimSum (pre ++ heap :: post)) :: post) = 0 := by
  rw [one_heap_update pre post heap]
  simp [Nat.xor_comm]

theorem summary_comparison (pre post : List Nat) (a b : Nat) :
    scan 0 (pre ++ a :: post) ^^^ scan 0 (pre ++ b :: post) = a ^^^ b := by
  simpa [scan_from_zero] using one_heap_difference pre post a b

/- A finite fibre check, not a theorem about the limiting distribution of all boards. -/
def guessFromLowBit (sigma : Nat) : Nat := if sigma % 2 = 1 then 1 else 2

theorem two_of_three_fibre_values :
    ([1, 2, 3].filter (fun sigma => guessFromLowBit sigma == sigma)).length = 2 := by
  decide

theorem failure_on_third_value : guessFromLowBit 3 ≠ 3 := by decide

theorem no_zero_without_zero_promise :
    (1 ^^^ 3 = 3 ^^^ 1) ∧ (1 : Nat) ≠ 0 := by decide


/- Algebraic move-count model. Actual execution of the policy is outside this file. -/
def channel (j sigma : Nat) : Bool :=
  if j = 0 then sigma.testBit 0 else xor (sigma.testBit j) (sigma.testBit 0)

def heapCount (j h : Nat) : Nat := h / 2^j + h % 2^j

def rolloutCount (j : Nat) (rows : List Nat) : Nat := (rows.map (heapCount j)).sum

theorem lowBit_add (a b : Nat) :
    (a+b).testBit 0 = xor (a.testBit 0) (b.testBit 0) := by
  rcases Nat.mod_two_eq_zero_or_one a with ha | ha <;>
    rcases Nat.mod_two_eq_zero_or_one b with hb | hb <;>
    simp [Nat.testBit_zero, Nat.add_mod, ha, hb]

theorem channel_xor (j a b : Nat) :
    channel j (a ^^^ b) = xor (channel j a) (channel j b) := by
  by_cases hj : j = 0
  · subst j
    simp only [channel]
    exact Nat.testBit_xor a b 0
  · simp only [channel, hj, if_false, Nat.testBit_xor]
    cases a.testBit j <;> cases a.testBit 0 <;>
      cases b.testBit j <;> cases b.testBit 0 <;> rfl

theorem heap_count_channel (j h : Nat) :
    (heapCount j h).testBit 0 = channel j h := by
  by_cases hj : j = 0
  · subst j
    simp only [heapCount, Nat.pow_zero, Nat.div_one, Nat.mod_one, Nat.add_zero,
      channel]
    rfl
  · have hpos : 0 < j := Nat.pos_of_ne_zero hj
    unfold heapCount
    rw [lowBit_add]
    simp only [Nat.testBit_div_two_pow, Nat.zero_add, Nat.testBit_mod_two_pow]
    simp [channel, hj, hpos]

theorem rollout_count_channel (j : Nat) (rows : List Nat) :
    (rolloutCount j rows).testBit 0 = channel j (nimSum rows) := by
  induction rows with
  | nil => simp [rolloutCount, nimSum, channel]
  | cons h t ih =>
    change (heapCount j h + rolloutCount j t).testBit 0 = channel j (h ^^^ nimSum t)
    rw [lowBit_add, heap_count_channel, ih, channel_xor]

#print axioms xor_left_comm
#print axioms xor_cancel_left
#print axioms nimSum_append
#print axioms scan_invariant
#print axioms scan_from_zero
#print axioms one_heap_difference
#print axioms one_heap_update
#print axioms matching_deltas_restore_original
#print axioms conditional_restoration
#print axioms move_to_zero_algebra
#print axioms summary_comparison
#print axioms two_of_three_fibre_values
#print axioms failure_on_third_value
#print axioms no_zero_without_zero_promise
#print axioms lowBit_add
#print axioms channel_xor
#print axioms heap_count_channel
#print axioms rollout_count_channel
end NimAudit
