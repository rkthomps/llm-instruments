


import Tests.Common
import Tests.TestCharacterization
import Tests.TestDecls

namespace Tests

unsafe def tests : List Test := [
  testBagOfTactics,
  testDeclsCounts,
  testDeclsNames
]

end Tests

unsafe def main : IO Unit := do
  for test in Tests.tests do
    try
      IO.println s!"Running test: {test.name}"
      test.run
      IO.println s!"Test passed: {test.name}\n"
    catch e =>
      IO.println s!"Test failed: {test.name}\nError: {e}\n"
