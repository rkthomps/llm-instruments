/-
Contains logic to run Lean's parser and elaborator on a file and
get the resulting information.
-/
import Lean

open Lean in
def getErrorsStr (ml : MessageLog) : IO String := do
  let errorMsgs := ml.toList.filter (λ m => m.severity == .error)
  let errors ← errorMsgs.mapM (λ m => m.toString)
  let errorTxt := errors.foldl (λ acc e => acc ++ "\n" ++ e) ""
  return errorTxt


open Lean in
open Lean.Elab in
/--

Notes:
  - Inspired by https://github.com/robertylewis/lean4-autograder-main
  - Can infer the workspace because this instrumentation will be running
    within the workspace.
-/
unsafe def runFile (file : String) : IO (Except String (Frontend.State × Parser.InputContext)) := do
  let fileContents ← IO.FS.readFile file
  let fileCtx := Parser.mkInputContext fileContents file
  let (fileHeader, parState, messages) ← Parser.parseHeader fileCtx
  enableInitializersExecution
  initSearchPath (← findSysroot)
  if messages.hasErrors then
    let errStr ← getErrorsStr messages
    return Except.error s!"{errStr}\nThere was an error parsing the imports of file {file}"

  let (fileHeadEnv, fileMsgs)
    ← processHeader fileHeader {} messages fileCtx

  if fileMsgs.hasErrors then
    let errStr ← getErrorsStr fileMsgs
    return Except.error s!"{errStr}\nThere was an error elaborating the imports of file {file}"

  let sheetCmdState : Command.State := Command.mkState fileHeadEnv fileMsgs {}
  let sheetFrontEndState ← IO.processCommands fileCtx parState sheetCmdState
  return (Except.ok (sheetFrontEndState, fileCtx))
