


import Lean
import Regex


inductive IllegalType where
  | illegalPrefix
  | illegalSubstring


structure IllegalSubstring where
  original : String
  illegalSubstring : String
  illegalType : IllegalType


structure ErrorHandler where
  /-
  Handler name for debugging & error messages.
  -/
  name : String

  /-
  When ran on an error message, returns a bool deciding if this
  handler should be ran on that error.
  -/
  trigger : String → Bool

  /-
  Given an error message, a proof, and the syntax tree of the proof
  return either a
  -/
  getInvalidPrefix : String → String → Lean.Syntax → Option IllegalSubstring


builtin_initialize errorHandlers : IO.Ref (List ErrorHandler) ← IO.mkRef []


def noPrefix (msg proof : String) (stx : Lean.Syntax) : Option IllegalSubstring := none


def toTacticStartPrefix (msg proof : String) (stx : Lean.Syntax) : Option IllegalSubstring := none



def registerPrefixErrorHandler (handler : ErrorHandler) : IO Unit := do
  if !(← Lean.initializing) then
    throw <| IO.userError s!"Failed to register Error prefix handler for '{handler.name}': only possible during initialization"
  errorHandlers.modify (λ hs => handler :: hs)


#check Lean.Server.registerLspRequestHandler
/-
Based on Lean.Server.registerLspRequestHandler
-/


def unsolvedGoalsHandler : ErrorHandler := {
  name := "unsolved_goals_handler",
  trigger := fun (msg : String) => msg == "unsolved goals",
  getInvalidPrefix := noPrefix,
}


def inductiveAlternativesHandler : ErrorHandler := {
  name := "alternative_not_provided_handler",
  trigger := fun (msg : String) =>
    let re := regex% r"Alternative `(.*?)` has not been provided"
    let captures := Regex.captures msg re
    match captures with
    | none => False
    | some _ => True
  ,
  getInvalidPrefix := noPrefix,
}



-- def noGoalsHandler : ErrorHandler := {
--   name := "no_goals_to_be_solved_handler",
--   trigger := fun (msg : String) => msg == "No goals to be solved",
--   getInvalidPrefix :=
-- }
