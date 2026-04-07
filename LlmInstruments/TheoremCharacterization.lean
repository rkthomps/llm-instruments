
/-
The goal is here is to take a theorem, and characterize it by its
syntactic structure.
This characterization can be used downstream for analysis of various techniques.
-/

import Lean
import LlmInstruments.FindTheorems

namespace LlmInstruments

open Lean

structure TacticFrequency where
  tactic : String
  frequency : Nat


structure TheoremCharacterization where
  thm : TheoremInfo
  tacticFrequencies : List TacticFrequency
  hasSorry : Bool
  -- And then other charactarizing information

#check List.foldl


partial def foldSyntax (f : α → Syntax → α) (init : α) : Syntax → α := fun stx =>
  match stx with
  | .node _ _ a => a.foldl (foldSyntax f) (f init stx)
  | _ => f init stx


partial def countMatches (p : Syntax → Bool) : Syntax → Nat :=
  foldSyntax (fun cur stx => if p stx then cur + 1 else cur) 0

structure TacticInfo where
  name : String
  kind : String
deriving ToJson, Repr, BEq

instance : ToString TacticInfo where
  toString t := toString (toJson t)


structure TacticInfoWithStx extends TacticInfo where
  stx : Syntax


partial def isTactic (stx : Syntax) : Option TacticInfo :=
  match stx with
  | .node _ k a => do
    if (`Lean.Parser.Tactic).isPrefixOf k then
      let first ← a[0]?
      match first with
      | .atom _ v =>
        if v == "by" || v == "with" then
          none
        let firstChar ← v.get? 0
        if firstChar.isAlpha then
          return { name := v, kind := k.toString }
        else
          none
      | _ => none
    else
      none
  | _ => none


-- def getAnalysisTree (stx : Syntax) : AnalysisTree :=

def getTactics (stx : Syntax) : List TacticInfo :=
  foldSyntax (fun cur stx =>
    match isTactic stx with
    | some info => cur ++ [info]
    | none => cur) [] stx

-- Implement code to gather the tactic frequencies of each theorem
-- Claude: Help here
def getTacticFrequencies (thm : TheoremInfoAndStx) : List TacticFrequency :=
  sorry
