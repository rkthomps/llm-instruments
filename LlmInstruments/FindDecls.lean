
import LlmInstruments.Common
import LlmInstruments.RunFile

import Lean

open Lean
open Lean.Lsp
open Lean.Elab

namespace LlmInstruments

structure DeclInfo where
  name : String
  range : Range
deriving ToJson


def checkForDeclInfo
  (i : Info)
  (contextInfo : Option ContextInfo)
  (inputCtx : InputContext) : IO (Option DeclInfo) := do
  match i with
  | .ofCommandInfo e => sorry
  | _ => return none


def declsFromState
  (state : Frontend.State)
  (ctx : Parser.InputContext) : ExceptT String IO (Array DeclInfo) := do
  let infoTrees := state.commandState.infoState.trees
  let mut decls : Array DeclInfo := #[]

  for t in infoTrees do
    let ti? ← liftM (foldInfoTree foldFun none t none)
    if let some declInfo := ti? then
      decls := decls.push declInfo
  return decls

  where
    foldFun acc t contextInfo : IO (Option DeclInfo) := do
      match acc with
      | some _ => return acc
      | none =>
        match t with
        | .node i _ => checkForDeclInfo i contextInfo ctx
        | _ => return none


unsafe def findDecls
  (file : String) : ExceptT String IO (Environment × Array DeclInfo) := do
  let (state, ctx) ← runFile file
  sorry



end LlmInstruments
