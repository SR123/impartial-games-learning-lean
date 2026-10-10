import NimAttain
import Circuit

/- Phase 3, target B: the complete recurrent separator/state protocol.
   Written by Claude (10 October 2026).  Lean 4.26.0, core/Std only.

   Stream: each position P is serialised as its rows (one token per heap, in
   order, empty heaps included) followed by SEP.  Persistent state: accumulator,
   previous completed summary, validity flag.
     row x : acc := acc XOR x
     SEP   : output (acc, if valid then some (prev XOR acc) else none);
             prev := acc; valid := true; acc := 0   (only the accumulator is reset)
   Proved:
     * fold invariant for arbitrary finite sequences of positions, including the
       first position, empty positions (= consecutive separators) and retained
       state between positions;
     * width preservation for B-bit rows; validity/reset behaviour;
     * stream differences equal Delta(P_{t-1}, P_t) and drive restoration;
     * move extraction by REPLAY (second scan; legal winning move when sigma ≠ 0,
       legal fallback / halt otherwise) with index and value bounds, and by BOARD
       STORAGE;
     * a bit-level encoding with 2B+1 state bits and an explicit per-update
       Boolean circuit (target C formulas) of constant depth and O(B) size, plus a
       fixed-scale threshold realisation of the XOR bit update.
   Not claimed: learning, self-play, or that training finds this update. -/

namespace NimAudit
namespace Recurrent

open Game Rollout Prob Attain AC0 AC0.Circ

inductive Token where
  | row (x : Nat)
  | sep

structure State where
  acc : Nat
  prev : Nat
  valid : Bool

structure Out where
  summary : Nat
  diff : Option Nat

def init : State := ⟨0, 0, false⟩

/-- One recurrent update; SEP produces an output. -/
def step (s : State) : Token → State × Option Out
  | .row x => (⟨s.acc ^^^ x, s.prev, s.valid⟩, none)
  | .sep => (⟨0, s.acc, true⟩, some ⟨s.acc, if s.valid then some (s.prev ^^^ s.acc) else none⟩)

/-- Run the recurrence over a token list, collecting outputs. -/
def run : State → List Token → State × List Out
  | s, [] => (s, [])
  | s, t :: ts => ((run (step s t).1 ts).1, (step s t).2.toList ++ (run (step s t).1 ts).2)

/-- Serialise positions: rows then SEP, position after position. -/
def serialize (Ps : List (List Nat)) : List Token :=
  Ps.flatMap (fun P => P.map Token.row ++ [Token.sep])

theorem run_append (s : State) (ts us : List Token) :
    run s (ts ++ us) = ((run (run s ts).1 us).1, (run s ts).2 ++ (run (run s ts).1 us).2) := by
  induction ts generalizing s with
  | nil => simp [run]
  | cons t ts ih => simp only [List.cons_append, run, ih, List.append_assoc]

/-- Rows XOR into the accumulator; nothing else changes and nothing is output. -/
theorem run_rows (s : State) (P : List Nat) :
    run s (P.map Token.row) = (⟨s.acc ^^^ nimSum P, s.prev, s.valid⟩, []) := by
  induction P generalizing s with
  | nil => simp [run, nimSum]
  | cons x P ih =>
    simp only [List.map_cons, run, step, ih, Option.toList, List.nil_append, nimSum,
      Nat.xor_assoc]

/-- One complete position. -/
theorem run_position (s : State) (P : List Nat) :
    run s (P.map Token.row ++ [Token.sep]) =
      (⟨0, s.acc ^^^ nimSum P, true⟩,
        [⟨s.acc ^^^ nimSum P, if s.valid then some (s.prev ^^^ (s.acc ^^^ nimSum P)) else none⟩]) := by
  rw [run_append, run_rows]
  simp [run, step]

/-- Expected outputs for a sequence of positions from a state with empty accumulator. -/
def expectedOuts : Bool → Nat → List (List Nat) → List Out
  | _, _, [] => []
  | v, q, P :: Ps =>
    ⟨nimSum P, if v then some (q ^^^ nimSum P) else none⟩ :: expectedOuts true (nimSum P) Ps

/-- Expected final state. -/
def expectedState : State → List (List Nat) → State
  | s, [] => s
  | _, P :: Ps => expectedState ⟨0, nimSum P, true⟩ Ps

/-- FOLD INVARIANT.  From any state with empty accumulator, for ANY finite sequence
    of positions (empty positions allowed): the t-th output is
    (sigma(P_t), Delta) where Delta = prev XOR sigma(P_1) if the starting state is
    valid (none otherwise) for t = 1 and sigma(P_{t-1}) XOR sigma(P_t) for t ≥ 2;
    the final state retains the last summary with valid = true and acc = 0. -/
theorem fold_invariant (s : State) (hs : s.acc = 0) (Ps : List (List Nat)) :
    run s (serialize Ps) = (expectedState s Ps, expectedOuts s.valid s.prev Ps) := by
  induction Ps generalizing s with
  | nil => simp [serialize, run, expectedState, expectedOuts]
  | cons P Ps ih =>
    have e : serialize (P :: Ps) = (P.map Token.row ++ [Token.sep]) ++ serialize Ps := by
      simp [serialize]
    rw [e, run_append, run_position, hs, Nat.zero_xor]
    rw [ih ⟨0, nimSum P, true⟩ rfl]
    simp [expectedState, expectedOuts]

/-- From the initial state: first output has no difference; later outputs carry
    the consecutive differences. -/
theorem stream_from_init (Ps : List (List Nat)) :
    (run init (serialize Ps)).2 = expectedOuts false 0 Ps := by
  rw [fold_invariant init rfl]; rfl

/-- Empty positions are exactly consecutive separators. -/
theorem serialize_empty (Ps : List (List Nat)) :
    serialize ([] :: Ps) = Token.sep :: serialize Ps := by
  simp [serialize]

/-- A separator immediately after a separator reports summary 0 (the empty
    position) and difference prev XOR 0 = prev. -/
theorem consecutive_sep (s : State) :
    run s [Token.sep, Token.sep] =
      (⟨0, 0, true⟩, [⟨s.acc, if s.valid then some (s.prev ^^^ s.acc) else none⟩,
        ⟨0, some (s.acc ^^^ 0)⟩]) := by
  simp [run, step]

/-- RESET BEHAVIOUR: after SEP the accumulator is 0, the summary is retained and the
    validity bit is set; rows never change prev or valid. -/
theorem sep_resets (s : State) :
    (step s Token.sep).1 = ⟨0, s.acc, true⟩ := rfl

theorem row_keeps (s : State) (x : Nat) :
    (step s (Token.row x)).1.prev = s.prev ∧ (step s (Token.row x)).1.valid = s.valid := ⟨rfl, rfl⟩

/-- WIDTH PRESERVATION: B-bit rows keep acc and prev below 2^B. -/
def StateWidth (B : Nat) (s : State) : Prop := s.acc < 2 ^ B ∧ s.prev < 2 ^ B

def TokenWidth (B : Nat) : Token → Prop
  | .row x => x < 2 ^ B
  | .sep => True

theorem step_width {B : Nat} {s : State} {t : Token} (hs : StateWidth B s) (ht : TokenWidth B t) :
    StateWidth B (step s t).1 := by
  cases t with
  | row x => exact ⟨Nat.xor_lt_two_pow hs.1 ht, hs.2⟩
  | sep => exact ⟨Nat.two_pow_pos B, hs.1⟩

theorem run_width {B : Nat} : ∀ {s : State} {ts : List Token}, StateWidth B s →
    (∀ t ∈ ts, TokenWidth B t) → StateWidth B (run s ts).1
  | s, [], hs, _ => hs
  | s, t :: ts, hs, ht => by
    simp only [run]
    exact run_width (step_width hs (ht t (by simp))) (fun u hu => ht u (List.mem_cons_of_mem _ hu))

/-! ## Differences and restoration from the stream -/

/-- Stream differences are nimber differences of consecutive positions. -/
theorem stream_diff_one_heap (pre post : List Nat) (a b : Nat) :
    nimSum (pre ++ a :: post) ^^^ nimSum (pre ++ b :: post) = a ^^^ b :=
  one_heap_difference pre post a b

/-- RESTORATION FROM THE STREAM: if the previous position Q had nim-sum zero and the
    opponent moved legally to Q', the difference reported at Q's successor drives a
    legal move to nim-sum zero (cancel the reported difference at the first
    qualifying heap). -/
theorem stream_restoration {Q Q' : List Nat} (h0 : nimSum Q = 0) (hm : Move Q Q') :
    ∃ R, cancelFirst (nimSum Q ^^^ nimSum Q') Q' = some R ∧ Move Q' R ∧ nimSum R = 0 :=
  restore_correct h0 hm

theorem stream_reports_delta (Q Q' : List Nat) (Ps : List (List Nat)) :
    expectedOuts false 0 (Q :: Q' :: Ps) =
      ⟨nimSum Q, none⟩ :: ⟨nimSum Q', some (nimSum Q ^^^ nimSum Q')⟩ ::
        expectedOuts true (nimSum Q') Ps := by
  simp [expectedOuts]

/-! ## Move extraction by replay -/

structure Replay where
  idx : Nat
  sel : Option (Nat × Nat)
  fnz : Option (Nat × Nat)

/-- Replay update for row x, with the summary sigma held fixed. -/
def replayStep (σ : Nat) (r : Replay) (x : Nat) : Replay :=
  ⟨r.idx + 1,
   (match r.sel with
    | some m => some m
    | none => if σ ≠ 0 ∧ x ^^^ σ < x then some (r.idx, x ^^^ σ) else none),
   (match r.fnz with
    | some m => some m
    | none => if 0 < x then some (r.idx, x - 1) else none)⟩

def replay (σ : Nat) (r : Replay) (P : List Nat) : Replay := P.foldl (replayStep σ) r

def shift (i0 : Nat) : Option (Nat × Nat) → Option (Nat × Nat) :=
  Option.map (fun p => (i0 + p.1, p.2))

/-- Left-biased choice. -/
def firstSome {α : Type} : Option α → Option α → Option α
  | some x, _ => some x
  | none, y => y

/-- The cancelling selection for summary sigma (none when sigma = 0). -/
def selFor (σ : Nat) (P : List Nat) : Option (Nat × Nat) :=
  if σ = 0 then none else cancelIdx σ P

theorem shift_zero (o : Option (Nat × Nat)) : shift 0 o = o := by
  cases o <;> simp [shift]

theorem firstSome_none_right {α : Type} (o : Option α) : firstSome o none = o := by
  cases o <;> rfl

theorem shift_map_succ (i0 : Nat) (o : Option (Nat × Nat)) :
    shift i0 (o.map (fun p => (p.1 + 1, p.2))) = shift (i0 + 1) o := by
  cases o with
  | none => rfl
  | some p => simp [shift]; omega

/-- REPLAY CHARACTERISATION: replaying P from index i0 with partial selections s, f
    yields s (if already set) or the first cancelling heap, and f or the first
    nonzero heap, with indices offset by i0. -/
theorem replay_spec (σ : Nat) : ∀ (P : List Nat) (i0 : Nat) (s f : Option (Nat × Nat)),
    replay σ ⟨i0, s, f⟩ P =
      ⟨i0 + P.length, firstSome s (shift i0 (selFor σ P)), firstSome f (shift i0 (decIdx P))⟩
  | [], i0, s, f => by
    simp [replay, selFor, cancelIdx, decIdx, shift, firstSome_none_right]
  | x :: P, i0, s, f => by
    have ih := replay_spec σ P (i0 + 1)
    simp only [replay, List.foldl_cons] at ih ⊢
    rw [replayStep, ih]
    simp only [Replay.mk.injEq, List.length_cons]
    refine ⟨by omega, ?_, ?_⟩
    · cases s with
      | some m => rfl
      | none =>
        simp only [firstSome]
        by_cases hσ : σ = 0
        · simp [hσ, selFor, shift]
        · by_cases hx : x ^^^ σ < x
          · simp [hσ, hx, selFor, cancelIdx, shift]
          · simp only [hσ, hx, and_false, if_false, firstSome, selFor, cancelIdx, ne_eq,
              not_false_eq_true, true_and]
            rw [shift_map_succ]
    · cases f with
      | some m => rfl
      | none =>
        simp only [firstSome]
        by_cases hx : 0 < x
        · simp [hx, decIdx, shift]
        · simp only [hx, if_false, firstSome, decIdx]
          first | done | rw [shift_map_succ]

/-- The move chosen after replay. -/
def replayMove (σ : Nat) (P : List Nat) : Option (Nat × Nat) :=
  let r := replay σ ⟨0, none, none⟩ P
  firstSome r.sel r.fnz

theorem replayMove_eq (σ : Nat) (P : List Nat) :
    replayMove σ P = firstSome (selFor σ P) (decIdx P) := by
  unfold replayMove
  rw [replay_spec]
  simp [firstSome, shift_zero]

theorem terminal_nimSum_zero {P : List Nat} (h : Terminal P) : nimSum P = 0 := by
  induction P with
  | nil => rfl
  | cons y ys ih =>
    simp only [nimSum, h y (by simp), Nat.zero_xor]
    exact ih (fun z hz => h z (List.mem_cons_of_mem _ hz))

/-- REPLAY EXTRACTION IS CORRECT.  With sigma = nim(P) from the first scan:
    the replay move is none iff P is terminal; every move is legal; and if
    sigma ≠ 0 the move reaches nim-sum zero. -/
theorem replay_correct (P : List Nat) :
    (replayMove (nimSum P) P = none ↔ Terminal P) ∧
    (∀ i v, replayMove (nimSum P) P = some (i, v) → ∃ x, P[i]? = some x ∧ v < x) ∧
    (nimSum P ≠ 0 → ∃ i v, replayMove (nimSum P) P = some (i, v) ∧ nimSum (P.set i v) = 0) := by
  rw [replayMove_eq]
  refine ⟨?_, ?_, ?_⟩
  · constructor
    · intro h
      unfold firstSome at h
      split at h
      · cases h
      · exact decIdx_none h
    · intro ht
      rw [terminal_nimSum_zero ht]
      simp [selFor, firstSome, decIdx_terminal ht]
  · intro i v h
    unfold firstSome at h
    split at h
    · next m hm =>
      cases h
      unfold selFor at hm
      split at hm
      · cases hm
      · obtain ⟨x, hx, rfl, hlt⟩ := cancelIdx_some hm
        exact ⟨x, hx, hlt⟩
    · obtain ⟨x, hx, rfl, hlt⟩ := decIdx_some h
      exact ⟨x, hx, by omega⟩
  · intro h0
    obtain ⟨pre, x, post, hp, hlt, _⟩ := exists_decreasing_heap P h0
    cases hc : cancelIdx (nimSum P) P with
    | none => exact absurd hlt (cancelIdx_none hc x (by rw [hp]; simp))
    | some m =>
      obtain ⟨i, v⟩ := m
      obtain ⟨y, hy, rfl, _⟩ := cancelIdx_some hc
      refine ⟨i, y ^^^ nimSum P, ?_, ?_⟩
      · simp [selFor, h0, hc, firstSome]
      · rw [nimSum_set _ hy, Nat.xor_assoc, xor_cancel_left]
        exact Nat.xor_self _

/-- TWO-SCAN PROTOCOL: the first scan (N rows + SEP, from the initial state) reports
    sigma = nim(P); the replay scan (N more rows) then yields the move of
    `replay_correct`.  Total 2N + 1 updates. -/
theorem two_scan_protocol (P : List Nat) :
    (run init (P.map Token.row ++ [Token.sep])).2 = [⟨nimSum P, none⟩] ∧
    (P.map Token.row ++ [Token.sep]).length + P.length = 2 * P.length + 1 := by
  refine ⟨?_, by simp; omega⟩
  rw [run_position]
  simp [init]

/-- Replay resources: the index counter ends at N, selected indices are < N, and on
    a B-bit board selected values are < 2^B; indices < N fit in log2 N + 1 bits. -/
theorem replay_resources {B : Nat} (P : List Nat) (hw : Width B P) :
    (replay (nimSum P) ⟨0, none, none⟩ P).idx = P.length ∧
    (∀ i v, replayMove (nimSum P) P = some (i, v) →
      i < P.length ∧ v < 2 ^ B ∧ i < 2 ^ (P.length.log2 + 1)) := by
  refine ⟨by rw [replay_spec]; simp, ?_⟩
  intro i v h
  obtain ⟨x, hx, hlt⟩ := (replay_correct P).2.1 i v h
  have hi : i < P.length := by
    rcases Nat.lt_or_ge i P.length with h' | h'
    · exact h'
    · rw [List.getElem?_eq_none h'] at hx; cases hx
  have hxm : x ∈ P := List.mem_of_getElem? hx
  exact ⟨hi, Nat.lt_trans hlt (hw x hxm), Nat.lt_trans hi Nat.lt_log2_self⟩

/-! ## Move extraction by board storage -/

structure Store where
  acc : Nat
  board : List Nat

def storeStep (st : Store) (x : Nat) : Store := ⟨st.acc ^^^ x, st.board ++ [x]⟩

theorem store_fold (P : List Nat) (a : Nat) (b : List Nat) :
    P.foldl storeStep ⟨a, b⟩ = ⟨a ^^^ nimSum P, b ++ P⟩ := by
  induction P generalizing a b with
  | nil => simp [nimSum]
  | cons x P ih =>
    simp only [List.foldl_cons, storeStep, ih, nimSum, Nat.xor_assoc, List.append_assoc,
      List.singleton_append]

theorem store_fold0 (P : List Nat) : P.foldl storeStep ⟨0, []⟩ = ⟨nimSum P, P⟩ := by
  rw [store_fold]; simp

/-- BOARD STORAGE: one scan stores (nim(P), P); the separator applies the phase-2
    selector, which is legal, winning when sigma ≠ 0 and halts only when terminal.
    Memory: N rows of B bits plus a B-bit accumulator. -/
theorem store_correct (P : List Nat) :
    (P.foldl storeStep ⟨0, []⟩).acc = nimSum P ∧ (P.foldl storeStep ⟨0, []⟩).board = P ∧
    (∀ q, selectMove (P.foldl storeStep ⟨0, []⟩).acc (P.foldl storeStep ⟨0, []⟩).board = some q →
      Move P q) ∧
    (selectMove (P.foldl storeStep ⟨0, []⟩).acc (P.foldl storeStep ⟨0, []⟩).board = none ↔
      Terminal P) ∧
    (nimSum P ≠ 0 → ∃ q, selectMove (P.foldl storeStep ⟨0, []⟩).acc
      (P.foldl storeStep ⟨0, []⟩).board = some q ∧ Move P q ∧ nimSum q = 0) := by
  rw [store_fold0]
  exact ⟨rfl, rfl, fun q h => selectMove_legal h, selectMove_none_iff _ P, selectMove_zero⟩

/-! ## Bit-level state and the per-update circuit -/

/-- Input layout of one update: acc bits 0..B-1, prev bits B..2B-1, valid 2B,
    tag 2B+1 (true = row), row bits 2B+2..3B+1. -/
def encode (B : Nat) (s : State) (t : Token) : Nat → Bool := fun j =>
  if j < B then s.acc.testBit j
  else if j < 2 * B then s.prev.testBit (j - B)
  else if j = 2 * B then s.valid
  else if j = 2 * B + 1 then (match t with | .row _ => true | .sep => false)
  else if j < 3 * B + 2 then (match t with | .row x => x.testBit (j - (2 * B + 2)) | .sep => false)
  else false

def xorC (a b : Circ) : Circ := or [and [a, not b], and [not a, b]]
def accC (B k : Nat) : Circ := and [input (2 * B + 1), xorC (input k) (input (2 * B + 2 + k))]
def prevC (B k : Nat) : Circ :=
  or [and [input (2 * B + 1), input (B + k)], and [not (input (2 * B + 1)), input k]]
def validC (B : Nat) : Circ := or [input (2 * B), not (input (2 * B + 1))]
def diffC (B k : Nat) : Circ := xorC (input (B + k)) (input k)
def diffValidC (B : Nat) : Circ := and [input (2 * B), not (input (2 * B + 1))]

theorem eval_xorC (x : Nat → Bool) (a b : Circ) : eval x (xorC a b) = xor (eval x a) (eval x b) := by
  unfold xorC
  simp only [eval_or, eval_and, eval_not, List.all_cons, List.all_nil, List.any_cons, List.any_nil]
  generalize eval x a = p
  generalize eval x b = q
  cases p <;> cases q <;> rfl

theorem enc_acc {B k : Nat} (hk : k < B) (s : State) (t : Token) :
    encode B s t k = s.acc.testBit k := by simp [encode, hk]

theorem enc_prev {B k : Nat} (hk : k < B) (s : State) (t : Token) :
    encode B s t (B + k) = s.prev.testBit k := by
  simp [encode, show ¬ B + k < B by omega, show B + k < 2 * B by omega]

theorem enc_valid (B : Nat) (s : State) (t : Token) : encode B s t (2 * B) = s.valid := by
  simp [encode, show ¬ 2 * B < B by omega]

theorem enc_tag (B : Nat) (s : State) (t : Token) :
    encode B s t (2 * B + 1) = (match t with | .row _ => true | .sep => false) := by
  simp [encode, show ¬ 2 * B + 1 < B by omega, show ¬ 2 * B + 1 < 2 * B by omega]

theorem enc_x {B k : Nat} (hk : k < B) (s : State) (x : Nat) :
    encode B s (Token.row x) (2 * B + 2 + k) = x.testBit k := by
  simp [encode, show ¬ 2 * B + 2 + k < B by omega, show ¬ 2 * B + 2 + k < 2 * B by omega,
    show 2 * B + 2 + k ≠ 2 * B by omega, show 2 * B + 2 + k ≠ 2 * B + 1 by omega,
    show 2 * B + 2 + k < 3 * B + 2 by omega]

/-- PER-UPDATE CIRCUIT CORRECTNESS (k < B): the circuits compute the new state bits
    and, at a separator, the output bits. -/
theorem circuit_update {B k : Nat} (hk : k < B) (s : State) (t : Token) :
    eval (encode B s t) (accC B k) = (step s t).1.acc.testBit k ∧
    eval (encode B s t) (prevC B k) = (step s t).1.prev.testBit k ∧
    eval (encode B s t) (validC B) = (step s t).1.valid ∧
    (t = Token.sep → eval (encode B s t) (input k) = s.acc.testBit k ∧
      eval (encode B s t) (diffC B k) = (s.prev ^^^ s.acc).testBit k ∧
      eval (encode B s t) (diffValidC B) = s.valid) := by
  cases t with
  | row x =>
    simp only [accC, prevC, validC, eval_and, eval_or, eval_not, eval_input, eval_xorC,
      List.all_cons, List.all_nil, List.any_cons, List.any_nil, enc_acc hk, enc_prev hk,
      enc_valid, enc_tag, enc_x hk, step, Nat.testBit_xor]
    refine ⟨by simp, by simp, by simp, fun h => by cases h⟩
  | sep =>
    simp only [accC, prevC, validC, diffC, diffValidC, eval_and, eval_or, eval_not, eval_input,
      eval_xorC, List.all_cons, List.all_nil, List.any_cons, List.any_nil, enc_acc hk,
      enc_prev hk, enc_valid, enc_tag, step, Nat.testBit_xor, Nat.zero_testBit]
    refine ⟨by simp, by simp, by simp, fun _ => ⟨by simp, by simp, by simp⟩⟩

/-- The 2B+1 state bits determine the state (B-bit width). -/
def stateOfBits (B : Nat) (bits : Nat → Bool) : State :=
  ⟨ofBits B (fun k => bits k), ofBits B (fun k => bits (B + k)), bits (2 * B)⟩

theorem ofBits_testBit_eq {B v : Nat} (hv : v < 2 ^ B) (f : Nat → Bool)
    (hf : ∀ k < B, f k = v.testBit k) : ofBits B f = v := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [testBit_ofBits]
  by_cases hi : i < B
  · simp [hi, hf i hi]
  · simp only [hi, decide_false, Bool.false_and]
    exact (Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hv
      (Nat.pow_le_pow_right (by decide) (by omega)))).symm

/-- STATE-BIT THEOREM: 2B+1 bits suffice, and the per-update circuit maps the bit
    encoding of a B-bit state to the bit encoding of its successor. -/
theorem circuit_step_correct {B : Nat} {s : State} {t : Token} (hs : StateWidth B s)
    (ht : TokenWidth B t) :
    stateOfBits B (fun j =>
        if j < B then eval (encode B s t) (accC B j)
        else if j < 2 * B then eval (encode B s t) (prevC B (j - B))
        else eval (encode B s t) (validC B)) = (step s t).1 := by
  have hw := step_width hs ht
  unfold stateOfBits
  have h1 : ofBits B (fun k => if k < B then eval (encode B s t) (accC B k)
      else if k < 2 * B then eval (encode B s t) (prevC B (k - B))
      else eval (encode B s t) (validC B)) = (step s t).1.acc := by
    apply ofBits_testBit_eq hw.1
    intro k hk
    simp only [hk, if_true]
    exact (circuit_update hk s t).1
  have h2 : ofBits B (fun k => if B + k < B then eval (encode B s t) (accC B (B + k))
      else if B + k < 2 * B then eval (encode B s t) (prevC B (B + k - B))
      else eval (encode B s t) (validC B)) = (step s t).1.prev := by
    apply ofBits_testBit_eq hw.2
    intro k hk
    simp only [show ¬ B + k < B by omega, show B + k < 2 * B by omega, if_true, if_false,
      show B + k - B = k by omega]
    exact (circuit_update hk s t).2.1
  have h3 : (if 2 * B < B then eval (encode B s t) (accC B (2 * B))
      else if 2 * B < 2 * B then eval (encode B s t) (prevC B (2 * B - B))
      else eval (encode B s t) (validC B)) = (step s t).1.valid := by
    simp only [show ¬ 2 * B < B by omega, Nat.lt_irrefl, if_false]
    cases t <;> simp [validC, enc_valid, enc_tag, step]
  simp only []
  rw [h1, h2, h3]

/-- Per-update circuit resources: depth ≤ 4, total size ≤ 28 B + 8 for all
    state and output bits (constant depth, O(B) size). -/
theorem circuit_resources (B k : Nat) :
    depth (accC B k) ≤ 4 ∧ depth (prevC B k) ≤ 4 ∧ depth (validC B) ≤ 4 ∧
    depth (diffC B k) ≤ 4 ∧ depth (diffValidC B) ≤ 4 ∧
    size (accC B k) + size (prevC B k) + size (diffC B k) ≤ 28 ∧
    size (validC B) + size (diffValidC B) ≤ 8 := by
  simp [accC, prevC, validC, diffC, diffValidC, xorC, listMax]

/-- Fixed-scale threshold realisation of one XOR bit update (W = 2): a two-layer
    network of literal-threshold gates computes a XOR b. -/
def xorNet : List Layer :=
  [[⟨[1, 1], [false, true], 2⟩, ⟨[1, 1], [true, false], 2⟩], [⟨[1, 1], [false, false], 1⟩]]

theorem xorNet_valid : NetValid 2 xorNet := by
  intro l hl g hg
  simp [xorNet] at hl
  rcases hl with rfl | rfl <;> simp at hg <;> rcases hg with rfl | rfl <;>
    simp [Gate.Valid] <;> omega

theorem xorNet_correct (a b : Bool) :
    evalNet xorNet (fun j => if j = 0 then a else if j = 1 then b else false) 0 = xor a b := by
  cases a <;> cases b <;> decide

#print axioms run_append
#print axioms run_rows
#print axioms run_position
#print axioms fold_invariant
#print axioms stream_from_init
#print axioms serialize_empty
#print axioms consecutive_sep
#print axioms sep_resets
#print axioms row_keeps
#print axioms step_width
#print axioms run_width
#print axioms stream_diff_one_heap
#print axioms stream_restoration
#print axioms stream_reports_delta
#print axioms shift_zero
#print axioms firstSome_none_right
#print axioms shift_map_succ
#print axioms replay_spec
#print axioms replayMove_eq
#print axioms terminal_nimSum_zero
#print axioms replay_correct
#print axioms two_scan_protocol
#print axioms replay_resources
#print axioms store_fold
#print axioms store_fold0
#print axioms store_correct
#print axioms eval_xorC
#print axioms enc_acc
#print axioms enc_prev
#print axioms enc_valid
#print axioms enc_tag
#print axioms enc_x
#print axioms circuit_update
#print axioms ofBits_testBit_eq
#print axioms circuit_step_correct
#print axioms circuit_resources
#print axioms xorNet_valid
#print axioms xorNet_correct

end Recurrent
end NimAudit
