/-
  Site-build tool (not part of the formal development).  Imports all 38 project modules
  and writes, for every user-written project declaration, its kind, pretty-printed type
  (Lean 4.26.0 default pretty-printer options, width 100), docstring, source range and
  direct project-level dependencies (constants occurring in its type and in its value or
  proof term; compiler-generated auxiliary constants are expanded to the user-level
  constants they use).

  Usage:  LEAN_PATH=<mathlib paths>:<fresh olean dir> lean tools/lean/ExportDecls.lean
  Output: data/lean_export.json (path given in the command at the end of this file).
-/
import NimCore
import NimRollout
import NimGame
import NimProbability
import NimAttain
import Circuit
import NimRecurrent
import BitBridge
import NimCorrBridge
import AttainCircuit
import FiniteNet
import BinaryReadout
import ParityCircuit
import Controller
import ControllerBits
import SharedCircuit
import SelectCircuit
import LocalRestore
import Foundation
import Coverage
import PriorityEncoder
import ThresholdNet
import ThresholdInst
import WholeGame
import Family
import Barrier
import RolloutExec
import Bypass
import Classical
import BoardStore
import Windows
import Misc
import NoiseModel
import Shootout
import WeakMastery
import Fourier
import RealNoise
import RealFourier
import Lean

open Lean Meta Elab Command

namespace ExportDecls

def projectModules : Array Name := #[`NimCore, `NimRollout, `NimGame, `NimProbability, `NimAttain,
  `Circuit, `NimRecurrent, `BitBridge, `NimCorrBridge, `AttainCircuit, `FiniteNet, `BinaryReadout,
  `ParityCircuit, `Controller, `ControllerBits, `SharedCircuit, `SelectCircuit, `LocalRestore,
  `Foundation, `Coverage, `PriorityEncoder, `ThresholdNet, `ThresholdInst, `WholeGame, `Family,
  `Barrier, `RolloutExec, `Bypass, `Classical, `BoardStore, `Windows, `Misc, `NoiseModel, `Shootout,
  `WeakMastery, `Fourier, `RealNoise, `RealFourier]

def kindOf : ConstantInfo → String
  | .thmInfo _ => "theorem"
  | .defnInfo _ => "def"
  | .axiomInfo _ => "axiom"
  | .opaqueInfo _ => "opaque"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"
  | .quotInfo _ => "quot"

def userName (n : Name) : Name := (privateToUserName? n).getD n

/-- User-level project constants reachable from `start`, expanding compiler-generated
    auxiliary project constants (matchers, nested proofs, …) to what they use. -/
def expandDeps (env : Environment) (isProj : Name → Bool) (userSet : NameSet)
    (start : Array Name) (self : Name) : Array String := Id.run do
  let mut seen : NameSet := NameSet.empty.insert self
  let mut acc : NameSet := {}
  let mut todo : Array Name := start
  while todo.size > 0 do
    let n := todo.back!
    todo := todo.pop
    if seen.contains n then continue
    seen := seen.insert n
    if userSet.contains n then
      acc := acc.insert n
    else if isProj n then
      if let some ci := env.find? n then
        todo := todo ++ ci.type.getUsedConstants
        if let some v := ci.value? then
          todo := todo ++ v.getUsedConstants
  return (acc.toList.map (fun n => (userName n).toString)).toArray.qsort (· < ·)

elab "#export_decls " path:str : command => do
  let env ← getEnv
  let modNames := env.header.moduleNames
  let modOf (n : Name) : Option Name :=
    match env.getModuleIdxFor? n with
    | some idx => let m := modNames[idx.toNat]!; if projectModules.contains m then some m else none
    | none => none
  let isProj (n : Name) : Bool := (modOf n).isSome
  let projConsts : Array Name := env.constants.map₁.fold (init := #[]) fun acc n _ =>
    if isProj n then acc.push n else acc
  let mut userSet : NameSet := {}
  for n in projConsts do
    if (← findDeclarationRanges? n).isSome then userSet := userSet.insert n
  let mut out : Array Json := #[]
  for n in projConsts do
    unless userSet.contains n do continue
    let some ci := env.find? n | continue
    let some rng ← findDeclarationRanges? n | continue
    let tyStr ← liftTermElabM do
      let f ← ppExpr ci.type
      pure (f.pretty 100)
    let doc ← findDocString? env n
    let valStart : Array Name := match ci.value? with
      | some v => v.getUsedConstants
      | none => match ci with
        | .inductInfo ii => ii.ctors.foldl (fun acc c => acc ++ ((env.find? c).map (fun cc => cc.type.getUsedConstants)).getD #[]) #[]
        | _ => #[]
    let j := Json.mkObj [
      ("name", toJson (userName n).toString),
      ("private", toJson (isPrivateName n)),
      ("module", toJson ((modOf n).getD Name.anonymous).toString),
      ("kind", toJson (kindOf ci)),
      ("type", toJson tyStr),
      ("doc", toJson doc),
      ("line", toJson rng.range.pos.line),
      ("column", toJson rng.range.pos.column),
      ("endLine", toJson rng.range.endPos.line),
      ("endColumn", toJson rng.range.endPos.column),
      ("selLine", toJson rng.selectionRange.pos.line),
      ("typeDeps", toJson (expandDeps env isProj userSet ci.type.getUsedConstants n)),
      ("valueDeps", toJson (expandDeps env isProj userSet valStart n))]
    out := out.push j
  IO.FS.writeFile path.getString (Json.compress (Json.arr out))
  logInfo m!"exported {out.size} declarations from {projConsts.size} project constants"

end ExportDecls

#export_decls "data/lean_export.json"
