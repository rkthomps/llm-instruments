
import LlmInstruments.Common
import LlmInstruments.RunFile

import Lean

open Lean
open Lean.Lsp
open Lean.Elab
open Lean.Parser
open Lean.Parser.Term

namespace LlmInstruments

inductive DeclInfo where
  | «abbrev» (name : Name)
  | «def» (name : Name)
  | «theorem» (name : Name)
  | «opaque» (name : Name)
  | «instance» (name : Option Name)
  | «axiom» (name : Name)
  | «example»
  | «inductive» (name : Name)
  | «class inductive» (name : Name)
  | «structure» (name : Name)
  | «class» (name : Name)
deriving ToJson

structure Decl where
  range : Range
  content : String
  info : DeclInfo
deriving ToJson


#check Lean.Parser.Command.declaration

def getName
  (tstx : TSyntax `Lean.Parser.Command.declId)
  (contextInfo : Option ContextInfo) : Option Name := do
  let idStx ← tstx.raw[0]?
  let cInfo ← contextInfo
  return cInfo.currNamespace.append idStx.getId

def checkForDeclInfo
  (i : Info)
  (contextInfo : Option ContextInfo)
  (inputCtx : InputContext) : IO (Option Decl) := do
  match i with
  | .ofCommandInfo e =>
    let decl : Option Decl := do
      let ⟨_, stx⟩ := e
      -- stx is a `Lean.Parser.Command.declaration`:
      --   stx[0] = declModifiers,  stx[1] = the body (abbrev / def / ... / structure)
      -- For every kind we care about, body[0] is the leading keyword atom and
      -- body[1] is the declId (when present). The shape is what Lean's own
      -- elaborators (Elab/{Definition,Inductive,Structure}.lean) rely on.
      let body := stx[1]
      let cInfo ← contextInfo
      let ⟨startPos, endPos⟩ ← stx.getRange?
      let lspRange ← stxLspRange stx inputCtx.fileMap
      let content := inputCtx.fileMap.source.extract startPos endPos
      let named (declIdStx : Syntax) (ctor : Name → DeclInfo) : Option DeclInfo := do
        let id ← declIdStx[0]?
        let name := cInfo.currNamespace.append id.getId
        return ctor name

      let declInfo : DeclInfo ← match body.getKind with
        | ``Command.«abbrev»       => named body[1] DeclInfo.«abbrev»
        | ``Command.definition     => named body[1] DeclInfo.«def»
        | ``Command.«theorem»      => named body[1] DeclInfo.«theorem»
        | ``Command.«opaque»       => named body[1] DeclInfo.«opaque»
        | ``Command.«axiom»        => named body[1] DeclInfo.«axiom»
        | ``Command.«inductive»    => named body[1] DeclInfo.«inductive»
        | ``Command.classInductive => named body[1] DeclInfo.«class inductive»
        | ``Command.«example»      => DeclInfo.«example»
        | ``Command.«instance»     => do
          -- attrKind, "instance", optNamedPrio, optional declId, declSig, declVal
          let declIdStx ← body[3].getOptional?
          let idStx ← declIdStx[0]?
          let name := cInfo.currNamespace.append idStx.getId
          DeclInfo.«instance» name
        | ``Command.«structure»    =>
          let ctor :=
            if body[0].getKind == ``Command.classTk then DeclInfo.«class» else DeclInfo.«structure»
          named body[1] ctor
        | _ => none

      return ⟨lspRange, content, declInfo⟩
    return decl
  | _ => return none


def declsFromState
  (state : Frontend.State)
  (ctx : Parser.InputContext) : ExceptT String IO (Array Decl) := do
  let infoTrees := state.commandState.infoState.trees
  let mut decls : Array Decl := #[]

  for t in infoTrees do
    let ti? ← liftM (foldInfoTree foldFun none t none)
    if let some decl := ti? then
      decls := decls.push decl
  return decls

  where
    foldFun acc t contextInfo : IO (Option Decl) := do
      match acc with
      | some _ => return acc
      | none =>
        match t with
        | .node i _ => checkForDeclInfo i contextInfo ctx
        | _ => return none


unsafe def findDecls
  (file : String) : ExceptT String IO (Environment × Array Decl) := do
  let (state, ctx) ← runFile file
  let decls ← declsFromState state ctx
  return (state.commandState.env, decls)



end LlmInstruments
