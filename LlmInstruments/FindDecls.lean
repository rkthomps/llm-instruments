
import LlmInstruments.Common
import LlmInstruments.RunFile

import Lean

open Lean
open Lean.Lsp
open Lean.Elab
open Lean.Parser
open Lean.Parser.Term

namespace LlmInstruments

inductive Decl where
  | «abbrev» (name : Name) (range : Range)
  | «def» (name : Name) (range : Range)
  | «theorem» (name : Name) (range : Range)
  | «opaque» (name : Name) (range : Range)
  | «instance» (name : Option Name) (range : Range)
  | «axiom» (name : Name) (range : Range)
  | «example» (range : Range)
  | «inductive» (name : Name) (range : Range)
  | «class inductive» (name : Name) (range : Range)
  | «structure» (name : Name) (range : Range)
  | «class» (name : Name) (range : Range)
deriving ToJson


#check Lean.Parser.Command.declaration

def getName (tstx : TSyntax `Lean.Parser.Command.declId) (contextInfo : Option ContextInfo) : Option Name := do
  let idStx ← tstx.raw[0]?
  let cInfo ← contextInfo
  return cInfo.currNamespace.append idStx.getId

def checkForDeclInfo
  (i : Info)
  (contextInfo : Option ContextInfo)
  (inputCtx : InputContext) : IO (Option Decl) := do
  match i with
  | .ofCommandInfo e =>
    let ⟨_, stx⟩ := e
    -- stx is a `Lean.Parser.Command.declaration`:
    --   stx[0] = declModifiers,  stx[1] = the body (abbrev / def / ... / structure)
    -- For every kind we care about, body[0] is the leading keyword atom and
    -- body[1] is the declId (when present). The shape is what Lean's own
    -- elaborators (Elab/{Definition,Inductive,Structure}.lean) rely on.
    let body := stx[1]
    let range? := stxLspRange stx inputCtx.fileMap
    let named (idStx : Syntax) (ctor : Name → Range → Decl) : Option Decl := do
      let name ← getName ⟨idStx⟩ contextInfo
      let range ← range?
      return ctor name range
    let decl : Option Decl := match body.getKind with
      | ``Command.«abbrev»       => named body[1] Decl.«abbrev»
      | ``Command.definition     => named body[1] Decl.«def»
      | ``Command.«theorem»      => named body[1] Decl.«theorem»
      | ``Command.«opaque»       => named body[1] Decl.«opaque»
      | ``Command.«axiom»        => named body[1] Decl.«axiom»
      | ``Command.«inductive»    => named body[1] Decl.«inductive»
      | ``Command.classInductive => named body[1] Decl.«class inductive»
      | ``Command.«example»      => range?.map Decl.«example»
      | ``Command.«instance»     =>
        -- attrKind, "instance", optNamedPrio, optional declId, declSig, declVal
        range?.map fun r =>
          let name := body[3].getOptional?.bind fun id => getName ⟨id⟩ contextInfo
          Decl.«instance» name r
      | ``Command.«structure»    =>
        let ctor :=
          if body[0].getKind == ``Command.classTk then Decl.«class» else Decl.«structure»
        named body[1] ctor
      | _ => none
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
