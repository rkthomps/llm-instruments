import LlmInstruments.FindTheorems



structure TheoremInfoArguments where
  filePath : String


unsafe def runTheoremInfoCommand (args : TheoremInfoArguments) : IO Unit := do
  let theoremInfo ← findTheorems args.filePath
  match theoremInfo with
  | Except.error e => throw (IO.userError s!"{e}\nCould not get theorem info for file {args.filePath}")
  | Except.ok ti =>
    IO.print (Lean.toJson ti)


inductive Command where
  | theoremInfo (args : TheoremInfoArguments)


unsafe def runCommand : Command → IO Unit
  | .theoremInfo args => runTheoremInfoCommand args


def parseTheoremInfoArgs (args : List String) : IO TheoremInfoArguments := do
  match args with
  | [filePath] => return {filePath := filePath}
  | _ => throw (IO.userError "Expected single file as argument to parseTheoremInfoArgs")


def parseArgs (args : List String) : IO Command := do
  match args with
  | "theorem-info" :: args' =>
    return Command.theoremInfo (← parseTheoremInfoArgs args')
  | _ => throw (IO.userError "Expected command: [theorem-info]")


unsafe def main (args : List String) : IO Unit := do
  let command ← parseArgs args
  runCommand command
