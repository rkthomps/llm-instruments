


import Lean

open Lean
open Lean.Server
open Lean.Server.RequestM
open Lean.Parser
open Lean.Elab
open Lean.Elab.Command


variable {α β : Type}


def runHandler (handler : PersistentArray InfoTree → InputContext → IO β)
  : CommandElabM β := do
  let ctx ← read
  let st ← get
  let trees ← pure st.infoState.trees
  let inputCtx : Parser.InputContext := {
    input := "",
    fileName := ctx.fileName,
    fileMap := ctx.fileMap
  }
  let result ← handler trees inputCtx
  return result


def handleInfoTreesTask
  (init : β)
  (combine : β → β → β)
  (handler : PersistentArray InfoTree → InputContext → IO β)
  : α → RequestM (RequestTask β) := fun _ => do
  let doc ← readDoc
  let t := doc.cmdSnaps.waitAll
  mapTask t fun (snaps, _) => do
    snaps.foldlM (fun acc snap => do
      let info ← runCommandElabM snap (liftM (runHandler handler))
      return (combine acc info)
    ) init
