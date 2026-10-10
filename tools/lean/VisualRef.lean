/-
  Reference values for the interactive illustrations (tools/visuals).

  This file does not prove anything and changes nothing in the audited development. It
  evaluates the development's own definitions on small inputs with `#eval` and prints one JSON
  object per line. tools/validate_site.py compares the browser engine (tools/visuals/nimvis-core.js)
  with these values, so that each illustration is tied to the Lean definitions it depicts:

    rest   LocalRestore / PriorityEncoder: the binary two-frame selector `Family.restS (B, N)`
           evaluated as Boolean formulas on `LocalRestore.tf B N Q Q'` (all output wires), its
           decoded move `PriorityEncoder.binSem`, and `LocalRestore.localDelta`;
    net    ThresholdNet.compileF on small formulas: every layer and gate, the gate program, and
           `evalNet` on every input;
    shoot  Shootout.ostep: every tick of the outer controller (all-head and early-exit schedules)
           from the reset tick, the outcome bits, and the binary readout `PriorityEncoder.mhBin`;
    ctrl   Controller.cstep: every state and output of the replay controller on token streams;
    store  BoardStore.bsStep: every state and output of the board-storage controller;
    summ   Recurrent.step: the summary mechanism (s, q, v) of Proposition 5.x.

  Run (from the edition folder, after building the 38 modules with tools/lean/build_bundle.sh):
    LEAN_PATH=<build>/olean lean tools/lean/VisualRef.lean > data/visual_reference_lean.jsonl
-/
import Family
import Shootout
import BoardStore

open NimAudit NimAudit.AC0 NimAudit.Game

namespace VisualRef

def jb (b : Bool) : String := if b then "true" else "false"
def jl (l : List Nat) : String := "[" ++ ",".intercalate (l.map toString) ++ "]"
def jbl (l : List Bool) : String := "[" ++ ",".intercalate (l.map jb) ++ "]"
def jm (o : Option (Nat × Nat)) : String :=
  match o with
  | none => "null"
  | some (i, v) => "[" ++ toString i ++ "," ++ toString v ++ "]"
def jon (o : Option Nat) : String := match o with | none => "null" | some n => toString n

/-- All boards with N heaps of values below 2^B. -/
def boards (B : Nat) : Nat → List (List Nat)
  | 0 => [[]]
  | N + 1 => (List.range (2 ^ B)).flatMap (fun x => (boards B N).map (x :: ·))

def nim (P : List Nat) : Nat := P.foldl (· ^^^ ·) 0

/-- Legal successors (one heap decreased). -/
def moves (P : List Nat) : List (List Nat) :=
  (List.range P.length).flatMap (fun i => (List.range (P.getD i 0)).map (fun v => P.set i v))

/-! ### Two-frame selector -/

def restLine (B N : Nat) (Q Q' : List Nat) : String :=
  let S := Family.restS (B, N)
  let z := LocalRestore.tf B N Q Q'
  let wires := (ThresholdInst.bForms S).map (Circ.eval z)
  "{\"kind\":\"rest\",\"B\":" ++ toString B ++ ",\"N\":" ++ toString N ++ ",\"r\":" ++
    toString (WholeGame.rIdx N) ++ ",\"Q\":" ++ jl Q ++ ",\"Qp\":" ++ jl Q' ++ ",\"wires\":" ++ jbl wires ++
    ",\"sem\":" ++ jm (PriorityEncoder.binSem S N z) ++ ",\"delta\":" ++
    toString (LocalRestore.localDelta B N Q Q') ++ "}"

/-- Every pair of boards (exhaustive), for tiny sizes. -/
def restAll (B N : Nat) : List String :=
  (boards B N).flatMap (fun Q => (boards B N).map (fun Q' => restLine B N Q Q'))

/-- Every legal transition from a zero-nim-sum board (the promised domain). -/
def restPromise (B N : Nat) : List String :=
  ((boards B N).filter (fun Q => nim Q == 0)).flatMap (fun Q => (moves Q).map (fun Q' => restLine B N Q Q'))

/-! ### Threshold compiler -/

def gateStr (g : AC0.Gate) : String :=
  "{\"w\":" ++ jl g.coeffs ++ ",\"neg\":" ++ jbl g.negs ++ ",\"thr\":" ++ toString g.thr ++ "}"

def dgateStr : Shared.DGate → String
  | .inp i => "{\"op\":\"inp\",\"i\":" ++ toString i ++ "}"
  | .cst b => "{\"op\":\"cst\",\"b\":" ++ jb b ++ "}"
  | .neg a => "{\"op\":\"neg\",\"a\":" ++ toString a ++ "}"
  | .conj as => "{\"op\":\"and\",\"as\":" ++ jl as ++ "}"
  | .disj as => "{\"op\":\"or\",\"as\":" ++ jl as ++ "}"

def inputsOf (n : Nat) : List (Nat → Bool) :=
  (List.range (2 ^ n)).map (fun m => fun i => if i < n then m.testBit (n - 1 - i) else false)

def netLine (name : String) (n : Nat) (cs : List Circ) : String :=
  let net := ThresholdNet.compileF cs
  let prog := ThresholdNet.progOf cs
  let layers := net.map (fun l => "[" ++ ",".intercalate (l.map gateStr) ++ "]")
  let table := (inputsOf n).map (fun x =>
    "{\"in\":" ++ jbl ((List.range n).map x) ++ ",\"formula\":" ++ jbl (cs.map (Circ.eval x)) ++
    ",\"net\":" ++ jbl ((List.range cs.length).map (evalNet net x)) ++ "}")
  "{\"kind\":\"net\",\"name\":\"" ++ name ++ "\",\"n\":" ++ toString n ++ ",\"depths\":" ++
    jl (cs.map Circ.depth) ++ ",\"sizes\":" ++ jl (cs.map Circ.size) ++ ",\"prog\":[" ++
    ",".intercalate (prog.map dgateStr) ++ "],\"outs\":" ++ jl (ThresholdNet.outsOf cs) ++
    ",\"levels\":" ++ jl ((List.range prog.length).map (ThresholdNet.lv prog)) ++
    ",\"layers\":[" ++ ",".intercalate layers ++ "],\"table\":[" ++ ",".intercalate table ++ "]}"

/-! ### Shootout controller -/

def osStr (B : Nat) (s : Shootout.OS) : String :=
  "{\"board\":" ++ jl s.rs.board ++ ",\"par\":" ++ jb s.rs.par ++ ",\"halted\":" ++ jb s.rs.halted ++
    ",\"run\":" ++ jb s.run ++ ",\"dec\":" ++ jb s.dec ++ ",\"j\":" ++ toString s.j ++ ",\"outs\":" ++
    jbl ((List.range B).map s.outs) ++ "}"

/-- States after the reset tick and after every further tick until the controller stops. -/
def osTrace (early : Bool) (B : Nat) (P : List Nat) : Nat → Shootout.OS → List Shootout.OS
  | 0, s => [s]
  | f + 1, s => if s.run then s :: osTrace early B P f (Shootout.ostep early B P false s) else [s]

def shootLine (early : Bool) (B : Nat) (P : List Nat) : String :=
  let N := P.length
  let s0 := Shootout.ostep early B P true (Shootout.initOS B [])
  let tr := osTrace early B P (B * (N * 2 ^ B + 3) + 4) s0
  let last := tr.getLast?.getD s0
  let r := WholeGame.rIdx N
  let readout := PriorityEncoder.binSem (PriorityEncoder.mhBin B N r) N (SelectCircuit.obsIn B N P last.outs)
  "{\"kind\":\"shoot\",\"early\":" ++ jb early ++ ",\"B\":" ++ toString B ++ ",\"P\":" ++ jl P ++
    ",\"states\":[" ++ ",".intercalate (tr.map (osStr B)) ++ "],\"outcomes\":" ++
    jbl ((List.range B).map (fun j => rolloutWinner j P)) ++ ",\"moves\":" ++
    jl ((List.range B).map (fun j => Rollout.rolloutMoves j P)) ++ ",\"readout\":" ++ jm readout ++
    ",\"decision\":" ++ jm (Controller.decisionMove P) ++ "}"

/-! ### Replay controller, board storage and summary -/

def tokStr : Controller.Tok → String
  | .row x => "{\"t\":\"row\",\"x\":" ++ toString x ++ "}"
  | .sep => "{\"t\":\"sep\"}"
  | .reset => "{\"t\":\"reset\"}"

def csStr (s : Controller.CState) : String :=
  "{\"replay\":" ++ jb s.replayMode ++ ",\"acc\":" ++ toString s.acc ++ ",\"prev\":" ++ toString s.prev ++
    ",\"valid\":" ++ jb s.valid ++ ",\"sig\":" ++ toString s.sig ++ ",\"idx\":" ++ toString s.idx ++
    ",\"sel\":" ++ jm s.sel ++ ",\"fnz\":" ++ jm s.fnz ++ "}"

def coutStr : Controller.COut → String
  | .summary s d => "{\"summary\":" ++ toString s ++ ",\"diff\":" ++ jon d ++ "}"
  | .move m => "{\"move\":" ++ jm m ++ "}"

def ctrlSteps : Controller.CState → List Controller.Tok → List String
  | _, [] => []
  | s, t :: ts =>
    let (s', o) := Controller.cstep s t
    ("{\"tok\":" ++ tokStr t ++ ",\"state\":" ++ csStr s' ++ ",\"out\":" ++
      (match o with | none => "null" | some c => coutStr c) ++ "}") :: ctrlSteps s' ts

def ctrlLine (name : String) (toks : List Controller.Tok) : String :=
  "{\"kind\":\"ctrl\",\"name\":\"" ++ name ++ "\",\"init\":" ++ csStr Controller.cinit ++ ",\"steps\":[" ++
    ",".intercalate (ctrlSteps Controller.cinit toks) ++ "]}"

def bsStr (s : BoardStore.BS) : String :=
  "{\"board\":" ++ jl s.board ++ ",\"acc\":" ++ toString s.acc ++ ",\"idx\":" ++ toString s.idx ++ "}"

def storeSteps (N : Nat) : BoardStore.BS → List Controller.Tok → List String
  | _, [] => []
  | s, t :: ts =>
    let (s', o) := BoardStore.bsStep N s t
    ("{\"tok\":" ++ tokStr t ++ ",\"state\":" ++ bsStr s' ++ ",\"out\":" ++
      (match o with | none => "null" | some b => "{\"summary\":" ++ toString b.sum ++ ",\"move\":" ++ jm b.move ++ "}") ++
      "}") :: storeSteps N s' ts

def storeLine (name : String) (N : Nat) (toks : List Controller.Tok) : String :=
  "{\"kind\":\"store\",\"name\":\"" ++ name ++ "\",\"N\":" ++ toString N ++ ",\"init\":" ++ bsStr (BoardStore.bsInit N) ++
    ",\"steps\":[" ++ ",".intercalate (storeSteps N (BoardStore.bsInit N) toks) ++ "]}"

def rtokStr : Recurrent.Token → String
  | .row x => "{\"t\":\"row\",\"x\":" ++ toString x ++ "}"
  | .sep => "{\"t\":\"sep\"}"

def summSteps : Recurrent.State → List Recurrent.Token → List String
  | _, [] => []
  | s, t :: ts =>
    let (s', o) := Recurrent.step s t
    ("{\"tok\":" ++ rtokStr t ++ ",\"state\":{\"acc\":" ++ toString s'.acc ++ ",\"prev\":" ++ toString s'.prev ++
      ",\"valid\":" ++ jb s'.valid ++ "},\"out\":" ++
      (match o with | none => "null" | some u => "{\"summary\":" ++ toString u.summary ++ ",\"diff\":" ++ jon u.diff ++ "}") ++
      "}") :: summSteps s' ts

def summLine (name : String) (Ps : List (List Nat)) : String :=
  "{\"kind\":\"summ\",\"name\":\"" ++ name ++ "\",\"positions\":[" ++ ",".intercalate (Ps.map jl) ++ "],\"steps\":[" ++
    ",".intercalate (summSteps Recurrent.init (Recurrent.serialize Ps)) ++ "]}"

/-- Resources of the actual two-frame selector formulas for one size: per-output depth and size,
    and the layer and gate counts of the network `ThresholdNet.compileF` builds from them
    (2·D + 2 layers and (2·D + 1)·S + K gates, ThresholdNet.compileF_spec). -/
def restSizeLine (B N : Nat) : String :=
  let cs := ThresholdInst.bForms (Family.restS (B, N))
  let D := AC0.Circ.listMax (cs.map AC0.Circ.depth)
  let S := (cs.map AC0.Circ.size).sum
  "{\"kind\":\"restsize\",\"B\":" ++ toString B ++ ",\"N\":" ++ toString N ++ ",\"depths\":" ++ jl (cs.map AC0.Circ.depth) ++
    ",\"sizes\":" ++ jl (cs.map AC0.Circ.size) ++ ",\"D\":" ++ toString D ++ ",\"S\":" ++ toString S ++ ",\"K\":" ++
    toString cs.length ++ ",\"layers\":" ++ toString (ThresholdNet.nLayers cs + 1) ++ ",\"gates\":" ++
    toString ((2 * D + 1) * S + cs.length) ++ "}"

def emit (ls : List String) : IO Unit := ls.forM IO.println

end VisualRef

open VisualRef

/- Two-frame selector: the paper's example, several candidates, outside the promise, and
   exhaustive small cases. -/
#eval emit [restLine 3 3 [3,5,6] [3,4,6], restLine 3 4 [4,5,6,7] [4,5,6,3], restLine 3 3 [1,2,3] [1,2,0],
  restLine 2 1 [2] [1], restLine 3 2 [1,0] [0,0], restLine 3 3 [3,5,6] [3,5,6], restLine 3 3 [1,2,3] [2,2,3]]
#eval emit (restAll 1 1 ++ restAll 1 2 ++ restAll 2 1 ++ restAll 1 3 ++ restAll 2 2)
#eval emit (restAll 2 3)
#eval emit (restPromise 3 3)
#eval emit (restPromise 3 4)

/- Threshold compiler on small formulas. -/
#eval emit [netLine "and" 2 [.and [.input 0, .input 1]], netLine "or" 2 [.or [.input 0, .input 1]],
  netLine "not" 1 [.not (.input 0)], netLine "xor" 2 [CorrBridge.xor2 (.input 0) (.input 1)]]

/- Shootout controller: examples and exhaustive small boards, both schedules. -/
#eval emit [shootLine false 3 [3,4,6], shootLine true 3 [3,4,6], shootLine false 3 [3,5,6], shootLine true 3 [3,5,6],
  shootLine false 3 [5,6,7], shootLine true 3 [5,6,7], shootLine false 2 [2], shootLine false 2 [0,0], shootLine true 2 [0,0]]
#eval emit ((boards 1 3).flatMap (fun P => [shootLine false 1 P, shootLine true 1 P]))
#eval emit ((boards 2 2 ++ boards 2 3).flatMap (fun P => [shootLine false 2 P, shootLine true 2 P]))
#eval emit ((boards 3 2).flatMap (fun P => [shootLine false 3 P, shootLine true 3 P]))

/- Replay controller: one decision, a game with two decisions, reset between games, and the
   separator/reset edge cases. -/
#eval emit [
  ctrlLine "decision-346" (.reset :: Controller.dtoks [3,4,6]),
  ctrlLine "game-two-decisions" (.reset :: Controller.dtoks [3,4,6] ++ Controller.dtoks [2,4,1]),
  ctrlLine "two-games" (.reset :: Controller.dtoks [3,4,6] ++ (.reset :: Controller.dtoks [1,1,0])),
  ctrlLine "zero-board" (.reset :: Controller.dtoks [3,5,6]),
  ctrlLine "terminal-board" (.reset :: Controller.dtoks [0,0,0]),
  ctrlLine "reset-mid-replay" (.reset :: ([Controller.Tok.row 3, .row 4, .row 6, .sep, .row 3, .reset] ++ Controller.dtoks [1,2,0])),
  ctrlLine "separator-keeps-summary" (.reset :: Controller.dtoks [3,4,6] ++ [Controller.Tok.sep, .sep])]
#eval emit ((boards 2 1 ++ boards 2 2 ++ boards 2 3 ++ boards 3 2).map (fun P => ctrlLine "exh" (.reset :: Controller.dtoks P)))

/- Board storage. -/
#eval emit [
  storeLine "decision-346" 3 (.reset :: BoardStore.btoks [3,4,6]),
  storeLine "game-two-decisions" 3 (.reset :: BoardStore.btoks [3,4,6] ++ BoardStore.btoks [2,4,1]),
  storeLine "reset" 3 (.reset :: BoardStore.btoks [3,4,6] ++ [Controller.Tok.reset] ++ BoardStore.btoks [1,1,0])]
#eval emit ((boards 2 1 ++ boards 2 2 ++ boards 2 3 ++ boards 3 2).map (fun P => storeLine "exh" P.length (.reset :: BoardStore.btoks P)))

/- Summary mechanism: decision-time boards only, versus including the player's own post-move board. -/
#eval emit [summLine "decision-boards" [[3,4,6], [2,4,1]], summLine "with-post-move-board" [[3,4,6], [2,4,6], [2,4,1]],
  summLine "extra-separator" [[3,4,6], []], summLine "single" [[3,4,6]]]
#eval emit ((boards 2 2).flatMap (fun P => (boards 2 2).map (fun P' => summLine "exh" [P, P'])))

/- Size of the actual selector formulas and of the compiled networks, for the depth accounting. -/
#eval emit [restSizeLine 2 2, restSizeLine 3 3, restSizeLine 3 4, restSizeLine 4 4]
