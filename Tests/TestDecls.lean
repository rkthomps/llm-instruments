import Tests.Common
import LlmInstruments.FindDecls

namespace Tests

open Lean
open LlmInstruments

def declKind : DeclInfo → String
  | .«abbrev» ..          => "abbrev"
  | .«def» ..             => "def"
  | .«theorem» ..         => "theorem"
  | .«opaque» ..          => "opaque"
  | .«instance» ..        => "instance"
  | .«axiom» ..           => "axiom"
  | .«example» ..         => "example"
  | .«inductive» ..       => "inductive"
  | .«class inductive» .. => "class inductive"
  | .«structure» ..       => "structure"
  | .«class» ..           => "class"

def declName : DeclInfo → Option Name
  | .«abbrev» n          => some n
  | .«def» n             => some n
  | .«theorem» n         => some n
  | .«opaque» n          => some n
  | .«axiom» n           => some n
  | .«inductive» n       => some n
  | .«class inductive» n => some n
  | .«structure» n       => some n
  | .«class» n           => some n
  | .«instance» n        => n
  | .«example»           => none

def countKind (decls : Array Decl) (kind : String) : Nat :=
  decls.foldl (fun acc d => if declKind d.info == kind then acc + 1 else acc) 0

def hasNameKind (decls : Array Decl) (name : Name) (kind : String) : Bool :=
  decls.any fun d => declKind d.info == kind && declName d.info == some name


unsafe def testDeclsCounts : Test := {
  name := "testDeclsCounts",
  run := do
    let file := "Tests/TestFiles/Decls.lean"
    let (_, decls) ← panicOnError (← findDecls file)
    let expected : List (String × Nat) := [
      ("abbrev",          3),
      ("def",             7),
      ("theorem",         6),
      ("opaque",          3),
      ("axiom",           3),
      ("example",         3),
      ("inductive",       3),
      ("class inductive", 3),
      ("structure",       3),
      ("class",           3),
      ("instance",        7)
    ]
    for (k, n) in expected do
      let actual := countKind decls k
      if actual != n then
        throw (IO.userError s!"Expected {n} '{k}' decls, got {actual}")
}


unsafe def testDeclsNames : Test := {
  name := "testDeclsNames",
  run := do
    let file := "Tests/TestFiles/Decls.lean"
    let (_, decls) ← panicOnError (← findDecls file)
    let expected : List (Name × String) := [
      -- top level
      (`TopAbbrev,                            "abbrev"),
      (`topDef,                               "def"),
      (`topTheorem,                           "theorem"),
      (`topOpaque,                            "opaque"),
      (`topAxiom,                             "axiom"),
      (`TopInductive,                         "inductive"),
      (`TopClassInductive,                    "class inductive"),
      (`TopStructure,                         "structure"),
      (`TopClass,                             "class"),
      (`topNamedInstance,                     "instance"),
      (`privateDef,                           "def"),
      (`noncomputableDef,                     "def"),
      (`privateTheorem,                       "theorem"),
      -- inside `namespace MyNamespace`
      (`MyNamespace.NsAbbrev,                 "abbrev"),
      (`MyNamespace.nsDef,                    "def"),
      (`MyNamespace.nsTheorem,                "theorem"),
      (`MyNamespace.NsInductive,              "inductive"),
      (`MyNamespace.NsClassInductive,         "class inductive"),
      (`MyNamespace.NsStructure,              "structure"),
      (`MyNamespace.NsClass,                  "class"),
      (`MyNamespace.nsNamedInstance,          "instance"),
      -- inside `section MySection` (sections don't affect names)
      (`SecAbbrev,                            "abbrev"),
      (`secDef,                               "def"),
      (`secTheorem,                           "theorem"),
      (`SecInductive,                         "inductive"),
      (`SecClassInductive,                    "class inductive"),
      (`SecStructure,                         "structure"),
      (`SecClass,                             "class"),
      (`secNamedInstance,                     "instance"),
      -- nested namespace
      (`Outer.Inner.deeplyNested,             "def"),
      (`Outer.Inner.deepTheorem,              "theorem"),
      -- namespace inside section
      (`InsideSection.withinSection,          "def"),
      (`InsideSection.withinSectionTheorem,   "theorem")
    ]
    for (n, k) in expected do
      unless hasNameKind decls n k do
        throw (IO.userError s!"Expected to find {k} named {n}")
}

end Tests
