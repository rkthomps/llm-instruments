
namespace Tests

structure Test where
  name : String
  run : IO Unit


def panicOnError (result : Except String α) : IO α := do
  match result with
  | Except.ok v => return v
  | Except.error e => throw (IO.userError e)


def panicOnNone (result : Option α) (errorMsg : String) : IO α := do
  match result with
  | some v => return v
  | none => throw (IO.userError errorMsg)


end Tests
