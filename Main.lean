import Lean
import LlmInstruments

open Lean
namespace LlmInstruments

structure ProofSampleArguments where
  expandProportion : Float
  depthWeight : Float -- > 0 means prefer deeper nodes, < 0 means prefer shallower nodes
  temperature : Float -- 0: always pick the best candidate, higher values increase randomness
  seed : Nat
deriving Lean.ToJson, Lean.FromJson


structure TheoremInfoArguments where
  filePath : String
  samples : List ProofSampleArguments


structure ProofSample where
  groundTruth : String
  sample : String
  arguments : ProofSampleArguments
deriving Lean.ToJson


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


def extendTheoremInfo (sampleArgs : List ProofSampleArguments) (ti : TheoremInfoAndStx) : MetaM ExtendedTheoremInfo := do
  let bagOfTactics := getTactics ti.stx
  let initialHidden := createInitialHiddenTacticSyntax ti.stx
  let numExpands := initialHidden.getExpandRange
  let samples : List ProofSample ← sampleArgs.mapM fun args => do
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
    let extendedInfos : Array ExtendedTheoremInfo ← ti.mapM (fun ti => runMetaM env (extendTheoremInfo args.samples ti))
    IO.print (Lean.toJson extendedInfos)


inductive Command where
  | heartBeat
  | theoremInfo (args : TheoremInfoArguments)


unsafe def runCommand : Command → IO Unit
  | .heartBeat => runHeartbeatCommand
  | .theoremInfo args => runTheoremInfoCommand args


def parseSampleArg (s : String) : IO ProofSampleArguments := do
  match Lean.Json.parse s with
  | Except.error e => throw (IO.userError s!"Invalid JSON for --sample: {e}")
  | Except.ok j =>
    match Lean.fromJson? (α := ProofSampleArguments) j with
    | Except.error e => throw (IO.userError s!"--sample JSON did not match ProofSampleArguments: {e}")
    | Except.ok args => return args

partial def parseTheoremInfoArgs (args : List String) : IO TheoremInfoArguments := do
  let rec go (rest : List String) (filePath : Option String) (samples : Array ProofSampleArguments)
      : IO TheoremInfoArguments := do
    match rest with
    | [] =>
      match filePath with
      | none => throw (IO.userError "theorem-info requires a file path")
      | some fp => return { filePath := fp, samples := samples.toList }
    | "--sample" :: jsonStr :: rest' =>
      let parsed ← parseSampleArg jsonStr
      go rest' filePath (samples.push parsed)
    | "--sample" :: [] => throw (IO.userError "--sample requires a JSON argument")
    | arg :: rest' =>
      if arg.startsWith "--" then
        throw (IO.userError s!"Unknown flag: {arg}")
      match filePath with
      | some _ => throw (IO.userError s!"Unexpected positional argument: {arg}")
      | none => go rest' (some arg) samples
  go args none #[]


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
