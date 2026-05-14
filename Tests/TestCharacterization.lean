
import Tests.Common
import LlmInstruments.TheoremCharacterization

namespace Tests

open LlmInstruments

theorem testTheorem (n : Nat): True := by
  cases n with
  | zero => simp
  | succ n =>
    have bar := Nat.add_comm
    have foo : True := by trivial
    simp_all


unsafe def testBagOfTactics : Test := {
  name := "testBagOfTactics",
  run := do
    let expected : List TacticInfo := [
      { name := "cases", kind := "Lean.Parser.Tactic.cases" },
      { name := "simp", kind := "Lean.Parser.Tactic.simp" },
      { name := "have", kind := "Lean.Parser.Tactic.tacticHave__" },
      { name := "have", kind := "Lean.Parser.Tactic.tacticHave__" },
      { name := "trivial", kind := "Lean.Parser.Tactic.tacticTrivial" },
      { name := "simp_all", kind := "Lean.Parser.Tactic.simpAll" }
    ]

    let file := "Tests/TestCharacterization.lean"
    let thm := "Tests.testTheorem"
    let (_, theorems) ← panicOnError (← findTheorems file)
    let thmInfo ← panicOnNone (theorems.find? (fun t => t.name == thm)) "Theorem not found"
    let tactics := getTactics thmInfo.stx
    if tactics != expected then
      throw (IO.userError s!"Expected {expected}, got {tactics}")
}
