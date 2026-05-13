
import Lean

def Array.enumerate {α} (arr : Array α) : Array (Nat × α) :=
  let rangeArr := Array.range arr.size
  rangeArr.zip arr


namespace LlmInstruments

open Lean in
open Lean.Lsp in
def stxLspRange (stx: Syntax) (text: FileMap): Option Range :=
  stx.getRange?.map (λ r => r.toLspRange text)


open Lean in
def getRangeStr (r : Range) (text : FileMap) : String :=
  sorry


open Lean.Elab in
partial def foldInfoTree [Monad m]
  (f : α → InfoTree → Option ContextInfo → m α)
  (acc : α)
  (t : InfoTree)
  (contextInfo : Option ContextInfo): m α := do
  let acc ← f acc t contextInfo
  match t with
  | .node _ c =>
    c.foldlM (fun acc ch => foldInfoTree f acc ch contextInfo) acc
  | .context partialInfo t =>
    let newContext := partialInfo.mergeIntoOuter? contextInfo
    foldInfoTree f acc t newContext
  | .hole _ =>
    return acc


end LlmInstruments
