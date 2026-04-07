
import Lean
import LlmInstruments.FindTheorems


namespace LlmInstruments

open Lean
open Lean.Lsp
open Lean.Server
open Lean.Server.RequestM
open Lean.Elab
open Lean.Elab.Command



structure FindTheoremsParams where
  textDocument : TextDocumentIdentifier
  deriving FromJson, ToJson

instance : FileSource FindTheoremsParams where
  fileSource p := p.textDocument.uri

structure FindTheoremsResult where
  theorems : Array TheoremInfo
  deriving FromJson, ToJson


#check Snapshots.Snapshot


#check Command.Context
#check RequestT

def theoremInfosFromTrees (infoTrees : Lean.PersistentArray InfoTree) (inputCtx : Parser.InputContext) : IO (Array TheoremInfo) := do
  -- dbg_trace s!"Got {infoTrees.size} info trees"
  if let Except.error s := validateTopLevelInfoTrees infoTrees then
    panic! s!"{s}\nAssumption about top level info trees invalid."
  else
    let mut theorems : Array TheoremInfo := #[]
    for t in infoTrees do
      let tFmt ← InfoTree.format t
      -- dbg_trace f!"{tFmt}"
      let ti? ← traverseITree t none inputCtx
      if let some ti := ti? then
        theorems := theorems.push ti.toTheoremInfo
    return theorems

#check Context

def handleFindTheoremsCommand : CommandElabM FindTheoremsResult := do
  let ctx ← read
  let st ← get
  let map := ctx.fileMap
  let trees := st.infoState.trees
  let inputCtx : Parser.InputContext := { input := "", fileName := ctx.fileName, fileMap := ctx.fileMap }
  let result ← theoremInfosFromTrees trees inputCtx
  let theoremResult : FindTheoremsResult := { theorems := result }
  return theoremResult

def handleFindTheoremsReqT : RequestT CommandElabM FindTheoremsResult := do
  liftM handleFindTheoremsCommand


def runSnapShots (snaps : List Snapshots.Snapshot) : RequestM FindTheoremsResult := do
    match snaps with
    | [] => return ⟨#[]⟩
    | s :: ss =>
      let sInfo ← runCommandElabM s handleFindTheoremsReqT
      let rest ← runSnapShots ss
      return { theorems := (sInfo.theorems ++ rest.theorems) }


open Lean.Server in
open Lean.Server.RequestM in
partial def handleFindTheorems (_ : FindTheoremsParams)
    : RequestM (RequestTask FindTheoremsResult) := do
  let doc ← readDoc
  -- bad: we have to wait on elaboration of the entire file before we can report document symbols
  let t := doc.cmdSnaps.waitAll
  mapTask t fun (snaps, _) => do
    runSnapShots snaps
