
import Lean
import LlmInstruments.FindTheorems

open Lean
open Lsp
open Server
open RequestM
open Elab
open Command


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

def handleFindTheoremsCommand : CommandElabM FindTheoremsResult := do
  let ctx ← read
  let st ← get
  let map := ctx.fileMap
  let trees := st.infoState.trees
  let result ← theoremInfosFromTrees trees map
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
