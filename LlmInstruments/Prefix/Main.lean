

import Lean
import LlmInstruments.RunFile

#check Lean.Syntax
#check Lean.Elab.Tactic.TacticM

open Lean
open Lean.Elab.Tactic


structure SyntaxError where
  pos : String.Pos
  stack: Parser.SyntaxStack
  error: Parser.Error


inductive Reason where
  | syntaxError (err : SyntaxError)
  | tacticError (ex : Exception)


structure IllegalPrefix where
  pos : String.Pos
  reason : Reason


/-
Real message function below:
ModuleParserState
-/


#check Elab.Command.State
#check Elab.Command.Context
#check Parser.ParserState
#check Parser.Tactic.delta

#check CoreM


def getPrefixParseError (err : SyntaxError) : Option IllegalPrefix :=
  match err.error.expected with
  /-
If `err.error.expected` is empty, we don't yet know if the string could be
  continued in a valid way
  e.g.
  theorem foo : True := by
    sim

  could be made valid by completing the string:
  theorem foo : True := by
    simp
  -/
  | [] =>
    let unexpectedTokStx := err.error.unexpectedTk
    match unexpectedTokStx with
    | .missing => some ⟨⟨err.pos.byteIdx + 1⟩, Reason.syntaxError err⟩
    -- | .missing => none
    | _ =>
      none


  /-
  If `err.error.expected` is nonempty, we know that the attempted string will never
  parse no matter how long it is extended
  -/
  | _ :: _ => some ⟨⟨err.pos.byteIdx + 1⟩, Reason.syntaxError err⟩




#check Monad
#check StateT
#check Server.registerLspRequestHandler


#check Parser.Command.declaration

def runParser (s : String) : Elab.Command.CommandElabM (Except (List IllegalPrefix) Syntax) := do
  -- TODO: Could change "llm-generated-proof to be the actual file name"
  let ictx := Parser.mkInputContext s "llm-generated-proof"
  let p := Parser.Command.declaration.fn
  let env ← getEnv
  let st := p.run ictx { env, options := {} } (Parser.getTokenTable env) (Parser.mkParserState s)
  match st.allErrors.toList with
  | [] => return Except.ok st.stxStack.back
  | _ :: _ =>
    let errorStructs : List SyntaxError := st.allErrors.toList.map (λ (p, stxStack, error) => ⟨p, stxStack, error⟩)
    let illegalPrefixs  := errorStructs.map (λ s => getPrefixParseError s)
    let struct0 := errorStructs[0]?.map ( λ err =>
      err.error.unexpectedTk
    )
    dbg_trace s!"unexpected range: {repr struct0}"
    return Except.error (illegalPrefixs.filterMap id)


#check Lean.throwError



#check bind







#check Elab.InfoTree.goalsAt?
#check Elab.Command.CommandElabM
#check Elab.Command.elabCommand
#check Elab.Command.elabDeclaration

#check Elab.InfoTree
#check Elab.CommandContextInfo

-- Needed to elab a command:
-- abbrev CommandElabCoreM (ε) := ReaderT Context $ StateRefT State $ EIO ε
--


-- Will be useful
#check Elab.ContextInfo.runMetaM
#check Elab.ContextInfo.runCoreM
#check Elab.runFrontend
#check Environment

#check withoutRecover

def elabDecl (attemptedProof : String) (ci : Elab.ContextInfo) : IO (Except (List IllegalPrefix) Unit):= do
  Elab.ContextInfo.runCoreM ci do
    liftCommandElabM do
      let parsedDecl ← runParser attemptedProof
      match parsedDecl with
      | Except.error errs => return Except.error errs
      | Except.ok declStx =>
        let state ← get
        let hasFoo := (state.env.find? `foo).isSome
        dbg_trace s!"Has foo {hasFoo}"
        try
          Elab.Command.elabDeclaration declStx
          let state ← get
          let hasFoo := (state.env.find? `foo).isSome
          dbg_trace s!"Has foo {hasFoo}"
          let messageStrs ← state.messages.reportedPlusUnreported.toList.mapM (λ m => m.toString)
          dbg_trace s!"{messageStrs};;; Has errors: {state.messages.hasErrors}"
          modify fun s => { s with messages := {} }
          return Except.ok ()
        catch e =>
          dbg_trace s!"Got exception: {← e.toMessageData.toString}"
          return Except.ok ()

        -- catch e =>
        --   dbg_trace s!"Got exception: {← e.toMessageData.toString}"



#check Elab.InfoTree
#check Elab.ContextInfo
#check Elab.PartialContextInfo


#check Elab.Info
#check Elab.CommandContextInfo

partial def firstContextFromTree (tree : Elab.InfoTree) (ci? : Option Elab.ContextInfo) : Option Elab.ContextInfo :=
  match tree with
  | .context pi t => do
    let ci := pi.mergeIntoOuter? ci?
    ci
  | .node _ cs => do
    for c in cs do
      if let some ci := firstContextFromTree c ci? then
        return ci
    none
  | .hole _ => none



partial def contextInfoFromTree
  (theoremName : Lean.Name)
  (ci? : Option Elab.ContextInfo)
  (tree : Elab.InfoTree) : Option Elab.ContextInfo :=
  match tree with
  | .context pi t => do
    if let Elab.PartialContextInfo.parentDeclCtx n := pi then
      dbg_trace s!"Got name {n}"
      if n == theoremName then
        match ci? with
        | some ci => return ci
        | none => panic! "context cant be none"
    let newCi? := pi.mergeIntoOuter? ci?
    if let some ci := newCi? then
      let foundTheorem := ci.env.find? theoremName
      if let some t := foundTheorem then
        dbg_trace s!"Found theorem {theoremName}"
      else
        dbg_trace s!"Didn't find theorem."

    contextInfoFromTree theoremName newCi? t
  | .node _ cs => do
    for c in cs do
      if let some ci := contextInfoFromTree theoremName ci? c then
        return ci
    none
  | .hole _ => none




def getCommand (stx : Syntax) : CoreM Unit := do
  sorry


/-
Strategy:

To get a prefix for theorem t,
1) Construct the proper context with which to run CommandElabM
2) Run CommandElabM
3) Use errors to construct an illegal prefix
-/

open Elab
open Parser


#check Parser.Command.declaration

partial def getCommandIncrementalState (name : Name) (initialState : IncrementalState) :
  /-
  In future, matching on name is probably not the right thing.
  Probably need to find the correct syntax based on the fully qualified name and thread it through
  -/
  Except String Language.Lean.CommandParsedSnapshot :=
  go name initialState.initialSnap
  where
    go name snap :=
      let isTheorem : Syntax → Bool
      | `(theorem $id:ident : $ty := $val) =>
        id.raw.getId == name
      | _ => False
      if let some _ := snap.stx.find? (fun innerStx => isTheorem innerStx) then
        Except.ok snap
      else
        if let some next := snap.nextCmdSnap? then
          go name next.get
        else
          Except.error s!"Could not find incremental command snapshot for {name}"



#check Frontend.State

-- unsafe def getIllegalPrefix
--   (file : String)
--   (theoremName : Name)
--   (attemptedProof : String) : IO (Except String (Option IllegalPrefix)) := do
--   let fileResult? ← runFile file
--   match fileResult? with
--   | Except.error e => return Except.error e
--   | Except.ok (state, ctx) =>
--     dbg_trace s!"Inspecting trees."
--     let trees := state.commandState.infoState.trees
--     for t in trees do
--       dbg_trace f!"NEW INFO TREE!!!!!"
--       if let some ci := contextInfoFromTree theoremName none t then
--         elabDecl attemptedProof ci
--         return Except.error "Not implemented"
--     return Except.error "Not implemented"


#check IncrementalState
#check Language.SnapshotLeaf
#check Snapshot
#check Language.SnapshotTree

def getErr (o : Option α) (err : String) : Except String α :=
  match o with
  | some a => Except.ok a
  | none => Except.error err


partial def findITree (sTree : Language.SnapshotTree) : Option InfoTree := do
  if let some iTree := sTree.element.infoTree? then
    return iTree
  else
    for c in sTree.children do
      if let some iTree := findITree c.get then
        return iTree
    none


open Lean.Language in
unsafe def getIllegalPrefix
  (file : String)
  (theoremName : Name)
  (attemptedProof : String) : IO (Except (List IllegalPrefix) Unit) := do
  let fileResult? ← runFile file
  let commandContext : Except String ContextInfo := do
    let (initialState, ctx) ← fileResult?
    let incrementalState ← getCommandIncrementalState theoremName initialState
    let eTree := Language.ToSnapshotTree.toSnapshotTree incrementalState.elabSnap
    let iTree ← getErr (findITree eTree) "No info tree"
    --.infoTree? "No info tree"
    getErr (firstContextFromTree iTree none) "Could not find context"

  match commandContext with
  | Except.error err => throw $ IO.userError s!"Error: {err}"
  | Except.ok cc =>
    dbg_trace "Attempting proof!!!"
    let result ← elabDecl attemptedProof cc
    match result with
    | Except.error err => return Except.error err
    | Except.ok _ => return Except.ok ()


#check withInfoContext

-- def attempted := "\
-- theorem foo : True := by
--   theorem "

def attempted := "\
theorem foo : True := by
  sim iso"

#check String.Pos


def getPrefixString (attemptedProof : String) (pos : String.Pos) : Substring :=
  {
    str := attemptedProof
    startPos := {}
    stopPos := pos
  }


unsafe def main (args : List String) : IO Unit := do
  let res ← getIllegalPrefix "TestFile.lean" `foo attempted
  match res with
  | Except.error err =>
    println! s!"Illegal Prefixs: {err.map (λ e => e.pos)}"
    println! s!"Illegal Prefixs: {err.map (λ e => getPrefixString attempted e.pos)}"
  | Except.ok _ =>
    return ()
