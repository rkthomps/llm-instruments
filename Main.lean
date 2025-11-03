import LlmInstruments.FindTheorems


structure TheoremInfoArguments where
  filePath : String


/--
The only purpose of the heartbeat command is to return
a 0 exit code to show that the instruments exist.
-/
def runHeartbeatCommand : IO Unit := do
  return ()

unsafe def runTheoremInfoCommand (args : TheoremInfoArguments) : IO Unit := do
  let theoremInfo ← findTheorems args.filePath
  match theoremInfo with
  | Except.error e => throw (IO.userError s!"{e}\nCould not get theorem info for file {args.filePath}")
  | Except.ok ti =>
    IO.print (Lean.toJson ti)


inductive Command where
  | heartBeat
  | theoremInfo (args : TheoremInfoArguments)


unsafe def runCommand : Command → IO Unit
  | .heartBeat => runHeartbeatCommand
  | .theoremInfo args => runTheoremInfoCommand args


def parseTheoremInfoArgs (args : List String) : IO TheoremInfoArguments := do
  match args with
  | [filePath] => return {filePath := filePath}
  | _ => throw (IO.userError "Expected single file as argument to parseTheoremInfoArgs")


def parseArgs (args : List String) : IO Command := do
  match args with
  | ["heartbeat"] => return Command.heartBeat
  | "theorem-info" :: args' =>
    return Command.theoremInfo (← parseTheoremInfoArgs args')
  | _ => throw (IO.userError "Expected command: [heartbeat, theorem-info]")


unsafe def main (args : List String) : IO Unit := do
  let command ← parseArgs args
  runCommand command
