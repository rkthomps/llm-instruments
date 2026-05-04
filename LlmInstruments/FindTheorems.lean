
import LlmInstruments.RunFile

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
deriving ToJson

structure TheoremInfoAndStx extends TheoremInfo where
  stx : Syntax


def validateTopLevelInfoTrees (trees : Lean.PersistentArray InfoTree) : Except String Unit := do
  for t in trees do
    match t with
    | .context _ _ => continue
    | .node _ _ => Except.error s!"Expected only context nodes in the top level info trees but found a .node"
    | .hole _ => Except.error s!"Expected only context nodes in the top level info trees but found a .hole"
  Except.ok ()


#check Lean.Server.registerLspRequestHandler
#check Command.elabDeclaration
#check Lean.Parser.Command.declaration


def stxLspRange (stx: Syntax) (text: FileMap): Option Range :=
  stx.getRange?.map (λ r => r.toLspRange text)


/--
  I'd prefer to do this, but if we want lemmas in the dataset, wed
  have to include mathlib as a dep. Don't want to do that.
    | `($_:declModifiers theorem $id:declId $sig:declSig $val:declVal) =>
-/
def parseTheoremOrLemma (n: Name) (stx: Syntax) (fileMap: FileMap) : IO (Option TheoremInfo) := do
  match stx with
  | `($_:declModifiers theorem $id:declId $sig:declSig $val:declVal) =>
    let declRange? := stxLspRange stx fileMap
    let sigRange? := stxLspRange sig fileMap
    let valRange? := stxLspRange val fileMap
    match declRange?, sigRange?, valRange? with
      | some dr, some sr, some vr =>
        return some ⟨n.toString, dr, sr, vr⟩
      | _, _, _ => return none
  | _ =>
    if stx.getKind == `lemma then
      -- dbg_trace stx
      let lemmaStx := stx[1]
      let lemmaSig := lemmaStx[1]
      let lemmaVal := lemmaStx[2]

      let declRange? := stxLspRange stx fileMap
      let sigRange? := stxLspRange lemmaSig fileMap
      let valRange? := stxLspRange lemmaVal fileMap
      match declRange?, sigRange?, valRange? with
        | some dr, some sr, some vr =>
          return some ⟨n.toString, dr, sr, vr⟩
        | _, _, _ => return none

    return none



/--
Returns a list of all parent decl names in the InfoTree
-/
partial def findParentDecls (iTree : InfoTree) : List Name :=
  match iTree with
  | .node i c => c.foldl (fun acc el => acc ++ findParentDecls el) []
  | .context (.parentDeclCtx n) t => n :: findParentDecls t
  | .context _ t => findParentDecls t
  | .hole _ => []




#check Lean.Server.registerLspRequestHandler
#check Lean.Name
#check Lean.Parser.Command.declaration
#check Lean.Parser.Command.declId

def checkForTheoremInfo (i : Info) (c : Lean.PersistentArray InfoTree) (contextInfo : Option ContextInfo) (inputCtx : Lean.Parser.InputContext): IO (Option TheoremInfoAndStx) := do
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
        return { ti with stx := stx }
      return theoremRange?
    | _ => return none
  | _ => return none



#check Info
#check PartialContextInfo
partial def traverseITree
  (t : InfoTree)
  (contextInfo : Option ContextInfo)
  (inputCtx: InputContext): IO (Option TheoremInfoAndStx):= do
  match t with
  | .node i c =>
    let ti? ← checkForTheoremInfo i c contextInfo inputCtx
    if let some ti := ti? then
      return ti
    -- Continue traversal
    for ch in c do
      let ti? ← traverseITree ch contextInfo inputCtx
      if let some ti := ti? then
        return ti
    return none


  | .context partialInfo t =>
    let newContext := partialInfo.mergeIntoOuter? contextInfo
    traverseITree t newContext inputCtx

  | .hole _ =>
    return none



#check InfoTree
#check InfoTree.format
-- def theoremInfosFromState (state : Frontend.State) : IO (List TheoremInfo) :=
def theoremInfosFromState (state : Frontend.State) (ctx : InputContext): IO (Array TheoremInfoAndStx) := do
  let infoTrees := state.commandState.infoState.trees
  dbg_trace s!"Got {infoTrees.size} info trees"
  if let Except.error s := validateTopLevelInfoTrees infoTrees then
    panic! s!"{s}\nAssumption about top level info trees invalid."
  else
    let mut theorems : Array TheoremInfoAndStx := #[]
    for t in infoTrees do
      let ti? ← traverseITree t none ctx
      if let some ti := ti? then
        theorems := theorems.push ti
    return theorems


unsafe def findTheorems (file : String) : IO (Except String (Environment × Array TheoremInfoAndStx)) := do
  let fileResult? ← runFile file
  match fileResult? with
  | Except.error e => return Except.error e
  | Except.ok (state, ctx) =>
    let theorems ← theoremInfosFromState state ctx
    return Except.ok (state.commandState.env, theorems)
