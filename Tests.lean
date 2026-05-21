


import Tests.Common
import Tests.TestCharacterization
import Tests.TestDecls
import Tests.TestLspWorker

namespace Tests

unsafe def tests : List Test := [
  testBagOfTactics,
  testDeclsCounts,
  testDeclsNames,
  testLspWorkerSearchPath,
  testLspWorkerInitializers
]

end Tests

unsafe def main : IO UInt32 := do
  let mut failures : Array String := #[]
  for test in Tests.tests do
    try
      IO.println s!"Running test: {test.name}"
      test.run
      IO.println s!"Test passed: {test.name}\n"
    catch e =>
      IO.println s!"Test failed: {test.name}\nError: {e}\n"
      failures := failures.push test.name
  if failures.isEmpty then
    return 0
  IO.eprintln s!"FAILED: {failures.size} test(s): {", ".intercalate failures.toList}"
  return 1
