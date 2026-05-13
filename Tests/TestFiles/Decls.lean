-- Fixture for the decl-extraction logic: exercises every variant of
-- `LlmInstruments.Decl` at the top level, inside a namespace, and
-- inside a section.

-- ===== Top level =====

abbrev TopAbbrev := Nat

def topDef : Nat := 0

theorem topTheorem : True := trivial

opaque topOpaque : Nat

axiom topAxiom : True

example : True := trivial

inductive TopInductive where
  | a
  | b

class inductive TopClassInductive where
  | mk

structure TopStructure where
  field : Nat

class TopClass where
  method : Nat

instance : TopClass where
  method := 0

instance topNamedInstance : TopClass where
  method := 1


-- ===== Modifiers =====

private def privateDef : Nat := 0

noncomputable def noncomputableDef : Nat := 0

private theorem privateTheorem : True := trivial


-- ===== Inside a namespace =====

namespace MyNamespace

abbrev NsAbbrev := Nat
def nsDef : Nat := 0
theorem nsTheorem : True := trivial
opaque nsOpaque : Nat
axiom nsAxiom : True
example : True := trivial

inductive NsInductive where
  | a
  | b

class inductive NsClassInductive where
  | mk

structure NsStructure where
  field : Nat

class NsClass where
  method : Nat

instance : NsClass where
  method := 0

instance nsNamedInstance : NsClass where
  method := 1

scoped instance : NsClass where
  method := 2

end MyNamespace


-- ===== Inside a section =====

section MySection

abbrev SecAbbrev := Nat
def secDef : Nat := 0
theorem secTheorem : True := trivial
opaque secOpaque : Nat
axiom secAxiom : True
example : True := trivial

inductive SecInductive where
  | a
  | b

class inductive SecClassInductive where
  | mk

structure SecStructure where
  field : Nat

class SecClass where
  method : Nat

instance : SecClass where
  method := 0

instance secNamedInstance : SecClass where
  method := 1

end MySection


-- ===== Nested namespace =====

namespace Outer.Inner

def deeplyNested : Nat := 0
theorem deepTheorem : True := trivial

end Outer.Inner


-- ===== Namespace inside section =====

section

namespace InsideSection

def withinSection : Nat := 0
theorem withinSectionTheorem : True := trivial

end InsideSection

end
