
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


def myMapTask (t : Task α) (f : α → RequestM β) : RequestM (RequestTask β) := do
  let rc ← readThe RequestContext
  EIO.mapTask (f · rc) t


open Lean.Server in
open Lean.Server.RequestM in
partial def handleFindTheorems (_ : FindTheoremsParams)
    : RequestM (RequestTask FindTheoremsResult) := do
  let doc ← readDoc
  -- bad: we have to wait on elaboration of the entire file before we can report document symbols
  let t := doc.cmdSnaps.waitAll
  myMapTask t fun (snaps, _) => do
    match h : snaps with
    | [] =>
      dbg_trace s!"No snaps."
      return ⟨#[]⟩
    | s :: ss =>
      let lastSnap := snaps.getLast (by simp_all)
      runCommandElabM lastSnap handleFindTheoremsReqT
