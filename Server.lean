import Lean
import LlmInstruments.FindTheoremsLsp
import LlmInstruments.FindDeclsLsp

open LlmInstruments

open Lean.Server in
builtin_initialize
  registerLspRequestHandler
    "$/lean/findTheorems"
    FindTheoremsParams
    FindTheoremsResult
    handleFindTheorems

def myFindWorkerPath : IO System.FilePath := do
  let mut workerPath ← IO.appPath
  if let some path := (←IO.getEnv "LEAN_SYSROOT") then
    workerPath := System.FilePath.mk path / "bin" / "lean"
      |>.addExtension System.FilePath.exeExtension
  if let some path := (←IO.getEnv "LEAN_WORKER_PATH") then
    workerPath := System.FilePath.mk path
  return workerPath

/-
    let workerProc ← Process.spawn {
      toStdioConfig := workerCfg
      cmd           := st.workerPath.toString
      args          := #["--worker"] ++ st.args.toArray ++ #[m.uri]
      -- open session for `kill` above
      setsid        := true
    }
-/

def main (args : List String): IO Unit := do
  let _ ← Lean.findSysroot
  let sysroot ← IO.getEnv "LEAN_SYSROOT"
  let appPath ← IO.appPath
  let myWorkerPath ← myFindWorkerPath
  let workerPath ← Lean.Server.Watchdog.findWorkerPath
  dbg_trace s!"Starting LLM instruments server at {appPath}; worker at {workerPath}; myworker at {myWorkerPath}; sysroot {sysroot}"
  match args with
  | [] =>
    let _ ← Lean.Server.Watchdog.watchdogMain []
  | ["--worker", f] =>
    dbg_trace s!"starting worker for {f}"
    let _ ← Lean.Server.FileWorker.workerMain {}
  | _ => throw <| IO.userError s!"unexpected arguments: {args}"
