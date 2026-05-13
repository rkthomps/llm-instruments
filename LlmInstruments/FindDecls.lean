
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
    match stx with
    | `($_:declModifiers abbrev $id:declId $dSig:optDeclSig $dVal:declVal) =>
      let decl : Option Decl := do
        let name ← getName id contextInfo
        let range ← stxLspRange stx inputCtx.fileMap
        return Decl.«abbrev» name range
      return decl
    | `($_:declModifiers def $id:declId $dSig:optDeclSig $dVal:declVal) =>
      let decl : Option Decl := do
        let name ← getName id contextInfo
        let range ← stxLspRange stx inputCtx.fileMap
        return Decl.«def» name range
      return decl
    | `($_:declModifiers theorem $id:declId $dSig:declSig $dVal:declVal) =>
      let decl : Option Decl := do
        let name ← getName id contextInfo
        let range ← stxLspRange stx inputCtx.fileMap
        return Decl.«theorem» name range
      return decl
    | `($_:declModifiers opaque $id:declId $dSig:declSig $[$dVal:declValSimple]?) =>
      let decl : Option Decl := do
        let name ← getName id contextInfo
        let range ← stxLspRange stx inputCtx.fileMap
        return Decl.«opaque» name range
      return decl
    | `($_:declModifiers $_:attrKind instance $[$_:namedPrio]? $[$id:declId]? $dSig:declSig $dVal:declVal) =>
      let decl : Option Decl := do
        let range ← stxLspRange stx inputCtx.fileMap
        let name := id >>= (getName · contextInfo)
        return Decl.«instance» name range
      return decl
    | `($_:declModifiers axiom $id:declId $dSig:declSig) =>
      let decl : Option Decl := do
        let name ← getName id contextInfo
        let range ← stxLspRange stx inputCtx.fileMap
        return Decl.«axiom» name range
      return decl
    | `($_:declModifiers example $dSig:optDeclSig $dVal:declVal) =>
      let decl : Option Decl := do
        let range ← stxLspRange stx inputCtx.fileMap
        return Decl.«example» range
      return decl
    | _ =>
      -- inductive / classInductive / structure have too many optional
      -- sub-pieces for reliable quotation matching; Lean's own elaborator
      -- (Elab/Inductive.lean, Elab/Structure.lean) indexes positionally
      -- on these too. The declId is at body[1] for all three.
      let body := stx[1]
      let mkDecl (ctor : Name → Range → Decl) : IO (Option Decl) := do
        let decl : Option Decl := do
          let name ← getName ⟨body[1]⟩ contextInfo
          let range ← stxLspRange stx inputCtx.fileMap
          return ctor name range
        return decl
      match body.getKind with
      | ``Lean.Parser.Command.«inductive»   => mkDecl Decl.«inductive»
      | ``Lean.Parser.Command.classInductive => mkDecl Decl.«class inductive»
      | ``Lean.Parser.Command.«structure» =>
        -- body[0] is structureTk or classTk; that picks the constructor.
        if body[0].getKind == ``Lean.Parser.Command.classTk then
          mkDecl Decl.«class»
        else
          mkDecl Decl.«structure»
      | _ => return none
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
