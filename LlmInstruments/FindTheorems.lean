
import LlmInstruments.RunFile
import LlmInstruments.Common

import Lean
import Lean.Parser.Command

open Lean
open Lean.Lsp
open Lean.Elab
open Lean.Parser

#check Lean.Lsp.Range

namespace LlmInstruments

structure TheoremInfo where
  name : String     -- Name of the theorem
  range : Range     -- Range of the entire declaration
  sigRange : Range  -- Range of the theorem signature
  valRange : Range  -- Range of the theorem value (proof)
deriving ToJson, FromJson

structure TheoremInfoAndStx extends TheoremInfo where
  stx : Syntax
  valStx : Syntax


def validateTopLevelInfoTrees (trees : Lean.PersistentArray InfoTree) : Except String Unit := do
  for t in trees do
    match t with
    | .context _ _ => continue
    | .node _ _ => throw s!"Expected only context nodes in the top level info trees but found a .node"
    | .hole _ => throw s!"Expected only context nodes in the top level info trees but found a .hole"
  return ()


#check Lean.Server.registerLspRequestHandler
#check Command.elabDeclaration
#check Lean.Parser.Command.declaration



#check Lean.Server.registerLspRequestHandler
#check Lean.Name
#check Lean.Parser.Command.declaration
#check Lean.Parser.Command.declId

def checkForTheoremInfo
  (i : Info)
  (c : Lean.PersistentArray InfoTree)
  (contextInfo : Option ContextInfo)
  (inputCtx : Lean.Parser.InputContext) : IO (Option TheoremInfoAndStx) := do
  match i with
  | .ofCommandInfo e =>
    let ⟨_, stx⟩ := e
    match stx with
    | `($_:declModifiers theorem $id:declId $dSig:declSig $dVal:declVal) =>
      let theoremRange? : Option TheoremInfoAndStx := do
        let range ← stxLspRange stx inputCtx.fileMap
        let sigRange ← stxLspRange dSig.raw inputCtx.fileMap
        let valRange ← stxLspRange dVal.raw inputCtx.fileMap
        let cInfo ← contextInfo
        let idStx ← id.raw[0]?
        let n := cInfo.currNamespace.append idStx.getId
        let ti : TheoremInfo := {
          name := toString n,
          sigRange := sigRange,
          valRange := valRange,
          range := range
        }
        return { ti with stx := stx, valStx := dVal.raw }
      return theoremRange?
    | _ => return none
  | _ => return none


def theoremInfoFromITree (t : InfoTree) (inputCtx : InputContext)
  : IO (Option TheoremInfoAndStx) := do
  let foldFun acc t contextInfo : IO (Option TheoremInfoAndStx) := do
    match acc with
    | some _ => return acc
    | none =>
      match t with
      | .node i c => checkForTheoremInfo i c contextInfo inputCtx
      | _ => return none
  foldInfoTree foldFun none t none


#check InfoTree
#check InfoTree.format
-- def theoremInfosFromState (state : Frontend.State) : IO (List TheoremInfo) :=
def theoremInfosFromState
  (state : Frontend.State)
  (ctx : InputContext) : ExceptT String IO (Array TheoremInfoAndStx) := do
  let infoTrees := state.commandState.infoState.trees
  validateTopLevelInfoTrees infoTrees
  let mut theorems : Array TheoremInfoAndStx := #[]
  for t in infoTrees do
    let ti? ← theoremInfoFromITree t ctx
    if let some ti := ti? then
      theorems := theorems.push ti
  return theorems


unsafe def findTheorems (file : String) : ExceptT String IO (Environment × Array TheoremInfoAndStx) := do
  let (state, ctx) ← runFile file
  let theorems ← theoremInfosFromState state ctx
  return (state.commandState.env, theorems)
