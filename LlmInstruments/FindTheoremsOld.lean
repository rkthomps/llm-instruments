
import LlmInstruments.RunFile

import Lean
import Lean.Parser.Command

open Lean.Lsp
open Lean.Elab

#check Lean.Lsp.Range

open Lean in
structure TheoremInfo where
  name : String     -- Name of the theorem
  range : Range     -- Range of the entire declaration
  sigRange : Range  -- Range of the theorem signature
  valRange : Range  -- Range of the theorem value (proof)
deriving ToJson


def validateTopLevelInfoTrees (trees : Lean.PersistentArray InfoTree) : Except String Unit := do
  for t in trees do
    match t with
    | .context _ _ => continue
    | .node _ _ => Except.error s!"Expected only context nodes in the top level info trees but found a .node"
    | .hole _ => Except.error s!"Expected only context nodes in the top level info trees but found a .hole"
  Except.ok ()


#check Lean.Server.registerLspRequestHandler
#check Command.elabDeclaration
#check Lean.Parser.Command.declaration


open Lean in
open Lean.Lsp in
def stxLspRange (stx: Syntax) (text: FileMap): Option Range :=
  stx.getRange?.map (λ r => r.toLspRange text)


open Lean in
open Lean.Parser.Command in
/--
  I'd prefer to do this, but if we want lemmas in the dataset, wed
  have to include mathlib as a dep. Don't want to do that.
    | `($_:declModifiers theorem $id:declId $sig:declSig $val:declVal) =>
-/
def parseTheoremOrLemma (n: Name) (stx: Syntax) (fileMap: FileMap) : IO (Option TheoremInfo) := do
  match stx with
  | `($_:declModifiers theorem $id:declId $sig:declSig $val:declVal) =>
    let declRange? := stxLspRange stx fileMap
    let sigRange? := stxLspRange sig fileMap
    let valRange? := stxLspRange val fileMap
    match declRange?, sigRange?, valRange? with
      | some dr, some sr, some vr =>
        return some ⟨n.toString, dr, sr, vr⟩
      | _, _, _ => return none
  | _ =>
    if stx.getKind == `lemma then
      dbg_trace stx
      let lemmaStx := stx[1]
      let lemmaSig := lemmaStx[1]
      let lemmaVal := lemmaStx[2]

      let declRange? := stxLspRange stx fileMap
      let sigRange? := stxLspRange lemmaSig fileMap
      let valRange? := stxLspRange lemmaVal fileMap
      match declRange?, sigRange?, valRange? with
        | some dr, some sr, some vr =>
          return some ⟨n.toString, dr, sr, vr⟩
        | _, _, _ => return none

    return none

partial def traverseITreeUnit (t : InfoTree) (contextInfo : Option ContextInfo) : IO Unit := do
  match t with
  | .node i c =>
    for ch in c do
      traverseITreeUnit ch contextInfo

  | .context partialInfo t =>
    let newContext := partialInfo.mergeIntoOuter? contextInfo
    traverseITreeUnit t newContext

  | .hole _ =>
    dbg_trace f!"Found hole"

-- set_option maxHeartbeats 1000000

#check Info
#check PartialContextInfo
open Lean in
partial def traverseITree (t : InfoTree) (contextInfo : Option ContextInfo) (inTheorem : Bool): IO Unit := do
  match t with
  | .node i c =>
    -- Return Theorem Info if the time is right
    -- if let some ci := contextInfo then
    --   if let some n := ci.parentDecl? then
    --     if inTheorem then
    --       let fmtInfo ← Info.format ci i
    --       if let .ofCustomInfo custInf := i then
    --         let ⟨stx, _⟩ := custInf
    --         -- dbg_trace s!"found custom info {n} {stx}"
    --       else
    --         -- dbg_trace s!"FOUND THM {n} {fmtInfo}"
    --       return ()

    -- Update in theorem
    -- let inTheorem := inTheorem || match i with
    -- | .ofCommandInfo e =>
    --   let ⟨_, stx⟩ := e
    --   match stx with
    --   | `($_:declModifiers theorem $id:declId $_:declSig $_:declVal) =>
    --     dbg_trace s!"[[CHILDREN OF {id}]]"
    --     for ch in c do
    --       let tfmt ← ch.fmt
    --       dbg_trace f"[[CHILD]]"
    --       dbg_trace tfmt
    --     true
    --   | _ => false
    -- | _ => false

    match i with
    | .ofCommandInfo e =>
      let ⟨_, stx⟩ := e
      match stx with
      | `($_:declModifiers theorem $id:declId $_:declSig $_:declVal) =>
        if h: c.size >= 2 then
          let c1 := c[0]
          let c2 := c[1]
          match c1 with
          | .context (.commandCtx i1) (.context (.parentDeclCtx n1) t1) =>
            dbg_trace s!"found the money for thm {n1}"
            -- Get whnf timeout if I check the second child.
          | _ => let _ := "hi"

          -- match c[0] with
          -- | .context (.commandCtx i1) (.context (.parentDeclCtx n1) t1) =>
          --   dbg_trace s!"Found the money for thm {n1}"
            -- match c.get! 1 with
            -- | .context (.commandCtx i2) (.context (.parentDeclCtx n2) t2) =>
            --     dbg_trace s!"Found the money for thm {n1} {n2}"
            --     return



          -- match c.get! 0, c.get! 1 with
          -- | .context (.commandCtx i1) ot1, .context (.commandCtx i2) ot2 =>
            -- match ot1 with
            -- | (.context (.parentDeclCtx n1) _) => sorry
            -- match ot1, ot2 with
            -- | (.context (.parentDeclCtx n1) _), (.context (.parentDeclCtx n2) _) =>
            --   dbg_trace s!"Found the money for thm {n1} {n2}"
              -- return
          -- | _, _ =>
            dbg_trace s!"Skipping thm {id}"

        -- dbg_trace s!"[[CHILDREN OF {id}]]"
        -- for ch in c do
        --   let tfmt ← ch.format
        --   dbg_trace s!"[[CHILD]]"
        --   dbg_trace tfmt
      | _ => let _ := "hi"
    | _ => let _ := "hi"

    -- Continue traversal
    for ch in c do
      traverseITree ch contextInfo inTheorem

  | .context partialInfo t =>
    let newContext := partialInfo.mergeIntoOuter? contextInfo
    traverseITree t newContext inTheorem
    -- if let .parentDeclCtx n := partialInfo then
    --   let tfmt ← t.format newContext
      -- if n == `Cat.Cherry.cat then
        -- dbg_trace "AT NAME:"
        -- dbg_trace tfmt

  | .hole _ =>
    dbg_trace f!"Found hole"



open Lean in
open Lean.Parser.Command in
def getDecl (parentName: Option Name) (t : InfoTree) (fileMap: FileMap): IO (Option TheoremInfo) := do
  match t with
  | .node (.ofCommandInfo e) c =>
    let ⟨_, stx⟩ := e
    if let some n := parentName then
      parseTheoremOrLemma n stx fileMap
    else
      -- let noDeclFmt ← InfoTree.format t
      -- dbg_trace noDeclFmt
      return none
  | .context (.parentDeclCtx n) t =>
    -- dbg_trace s!"Getting ranges for {n}"
    getDecl n t fileMap
  | .context _ t =>
    -- dbg_trace s!"Getting ranges for ??"
    getDecl parentName t fileMap
  | _ => return none


#check InfoTree
#check InfoTree.format
-- def theoremInfosFromState (state : Frontend.State) : IO (List TheoremInfo) :=
open Lean.Parser in
def theoremInfosFromState (state : Frontend.State) (ctx : InputContext): IO Unit :=
  let infoTrees := state.commandState.infoState.trees
  dbg_trace s!"Got {infoTrees.size} info trees"
  if let Except.error s := validateTopLevelInfoTrees infoTrees then
    panic! s!"{s}\nAssumption about top level info trees invalid."
  else
    for t in infoTrees do
      traverseITree t none false
      let decl? ← getDecl none t ctx.fileMap
      if let some tr := decl? then
        dbg_trace s!"Found thm {Lean.toJson tr}"

      -- match t with
      -- | .node

      -- let infoFmt ← InfoTree.format t
      -- dbg_trace s!"Tree:  {infoFmt}"
      -- match t with
      -- | .context (.parentDeclCtx n) t =>
      --   let infoFmt ← InfoTree.format t
      --   dbg_trace s!"Tree for {n}: {infoFmt}"
      -- | .context (.commandCtx _) _ => continue
      -- | _ => panic! "uh oh"



unsafe def findTheorems (file : String) : IO (Except String (List TheoremInfo)) := do
  dbg_trace "running file"
  let fileResult? ← runFile file
  dbg_trace "ran file"
  match fileResult? with
  | Except.error e => return Except.error e
  | Except.ok (state, ctx) =>
    theoremInfosFromState state ctx
    return Except.ok []
