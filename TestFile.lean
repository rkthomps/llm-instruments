
import Lean.Parser.Command
open Lean

-- higher priority to override the one in Batteries
/-- `lemma` means the same as `theorem`. It is used to denote "less important" theorems -/
syntax (name := lemma) (priority := default + 1) declModifiers
  group("lemma " declId ppIndent(declSig) declVal) : command


@[macro «lemma»] def expandLemma : Macro := fun stx =>
  -- Not using a macro match, to be more resilient against changes to `lemma`.
  -- This implementation ensures that any future changes to `theorem` are reflected in `lemma`
  let stx := stx.modifyArg 1 fun stx =>
    let stx := stx.modifyArg 0 (mkAtomFrom · "theorem" (canonical := true))
    stx.setKind ``Parser.Command.theorem
  pure <| stx.setKind ``Parser.Command.declaration

namespace Cat

lemma Cherry.cat : True ∨ False :=
  by simp

end Cat

theorem foo : True :=
  by simp

#print "hi"

theorem bar : False :=
  sorry
