
import Lean
import LlmInstruments.FindDecls
import LlmInstruments.LspCommon

open Lean
open Lean.Lsp
open Lean.Elab
open Lean.Elab.Command
open Lean.Server
open Lean.Server.RequestM

namespace LlmInstruments

structure FindDeclsParams where
  textDocument : TextDocumentIdentifier
  deriving FromJson, ToJson

instance : FileSource FindDeclsParams where
  fileSource p := p.textDocument.uri

structure FindDeclsResult where
  decls : Array Decl
  deriving FromJson, ToJson


def declsFromTrees
  (infoTrees : Lean.PersistentArray InfoTree)
  (inputCtx : Parser.InputContext) : IO (Array Decl) := do
  let mut decls : Array Decl := #[]
  for t in infoTrees do
    let decl? ← declFromITree t inputCtx
    if let some decl := decl? then
      decls := decls.push decl
  return decls

def declsHandler (trees : Lean.PersistentArray InfoTree) (inputCtx : Parser.InputContext)
  : IO FindDeclsResult := do
  let result ← declsFromTrees trees inputCtx
  return { decls := result }

def declsCombine (r1 r2 : FindDeclsResult) : FindDeclsResult :=
  { decls := r1.decls ++ r2.decls }

def declsInit : FindDeclsResult := { decls := #[] }

def handleFindDecls := handleInfoTreesTask (α := FindDeclsParams) declsInit declsCombine declsHandler


end LlmInstruments
