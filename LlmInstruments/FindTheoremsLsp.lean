
import Lean
import LlmInstruments.FindTheorems
import LlmInstruments.LspCommon


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


def theoremInfosFromTrees (infoTrees : Lean.PersistentArray InfoTree) (inputCtx : Parser.InputContext)
  : IO (Array TheoremInfo) := do
  -- dbg_trace s!"Got {infoTrees.size} info trees"
  if let Except.error s := validateTopLevelInfoTrees infoTrees then
    panic! s!"{s}\nAssumption about top level info trees invalid."
  else
    let mut theorems : Array TheoremInfo := #[]
    for t in infoTrees do
      let ti? ← theoremInfoFromITree t inputCtx
      if let some ti := ti? then
        theorems := theorems.push ti.toTheoremInfo
    return theorems


def theoremInfosHandler (trees : Lean.PersistentArray InfoTree) (inputCtx : Parser.InputContext)
  : IO FindTheoremsResult := do
  let result ← theoremInfosFromTrees trees inputCtx
  return { theorems := result }

def theoremInfosCombine (r1 r2 : FindTheoremsResult) : FindTheoremsResult :=
  { theorems := r1.theorems ++ r2.theorems }

def theoremInfosInit : FindTheoremsResult := { theorems := #[] }

def handleFindTheorems := handleInfoTreesTask (α := FindTheoremsParams) theoremInfosInit theoremInfosCombine theoremInfosHandler
