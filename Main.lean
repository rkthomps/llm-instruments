import Lean
import LlmInstruments

open Lean
namespace LlmInstruments

structure TheoremInfoArguments where
  filePath : String

structure ProofSampleArguments where
  expandProportion : Float
  depthWeight : Float -- > 0 means prefer deeper nodes, < 0 means prefer shallower nodes
  temperature : Float -- 0: always pick the best candidate, higher values increase randomness
  seed : Nat
deriving Lean.ToJson


structure ProofSample where
  groundTruth : String
  sample : String
  arguments : ProofSampleArguments
deriving Lean.ToJson


def depthSampleArguments (proportion : Float) : ProofSampleArguments :=
  { expandProportion := proportion, depthWeight := 1.0, temperature := 0.0, seed := 0 }

def breadthSampleArguments (proportion : Float) : ProofSampleArguments :=
  { expandProportion := proportion, depthWeight := -1.0, temperature := 0.0, seed := 0 }


instance : Monad List where
  pure := List.pure
  bind := List.bind
instance : Monad List := inferInstance


def defaultSampleQueries : List ProofSampleArguments := do
  let p ← [0.25, 0.5, 0.75]
  [depthSampleArguments p, breadthSampleArguments p]


structure ExtendedTheoremInfo extends TheoremInfo where
  bagOfTactics : List TacticInfo
  numExpands : Nat
  samples : List ProofSample
deriving Lean.ToJson


/--
The only purpose of the heartbeat command is to return
a 0 exit code to show that the instruments exist.
-/
def runHeartbeatCommand : IO Unit := do
  return ()


def extendTheoremInfo (ti : TheoremInfoAndStx) : MetaM ExtendedTheoremInfo := do
  let bagOfTactics := getTactics ti.stx
  let initialHidden := createInitialHiddenTacticSyntax ti.stx
  let numExpands := initialHidden.getExpandRange
  let samples : List ProofSample ← defaultSampleQueries.mapM fun args => do
    let sampleStx ← expandProportion ti.stx args.expandProportion (selectDepthWeighted args.depthWeight args.temperature) args.seed
    let groundTruth ← Lean.PrettyPrinter.ppCategory `command ti.stx
    let sample ← Lean.PrettyPrinter.ppCategory `command sampleStx
    return { groundTruth := toString groundTruth, sample := toString sample, arguments := args }
  return { ti.toTheoremInfo with bagOfTactics, numExpands, samples }


def runMetaM (env : Environment) (m : MetaM α) : IO α := do
  let ((a, _), _) ← (m.run).toIO
    { fileName := "<runMetaM>", fileMap := default }
    { env := env }
  return a


unsafe def runTheoremInfoCommand (args : TheoremInfoArguments) : IO Unit := do
  let result ← findTheorems args.filePath
  match result with
  | Except.error e => throw (IO.userError s!"{e}\nCould not get theorem info for file {args.filePath}")
  | Except.ok (env, ti) =>
    let extendedInfos : Array ExtendedTheoremInfo ← ti.mapM (fun ti => runMetaM env (extendTheoremInfo ti))
    IO.print (Lean.toJson extendedInfos)


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

end LlmInstruments

unsafe def main (args : List String) : IO Unit := do
  let command ← LlmInstruments.parseArgs args
  LlmInstruments.runCommand command
