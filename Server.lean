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
  registerLspRequestHandler
    "$/lean/findDecls"
    FindDeclsParams
    FindDeclsResult
    handleFindDecls

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

unsafe def main (args : List String): IO Unit := do
  let _ ← Lean.findSysroot
  let sysroot ← IO.getEnv "LEAN_SYSROOT"
  let appPath ← IO.appPath
  let myWorkerPath ← myFindWorkerPath
  let workerPath ← Lean.Server.Watchdog.findWorkerPath
  dbg_trace s!"Starting LLM instruments server at {appPath}; worker at {workerPath}; myworker at {myWorkerPath}; sysroot {sysroot}"
  -- Custom worker binaries don't get the stock worker's startup. Besides the
  -- search path (below), they must enable execution of imported modules'
  -- `initialize`/`[init]` code, or any imported `initialize`d `IO.Ref`
  -- (e.g. Velvet's `globalMutVarsCtx`) is left uninitialized and the first
  -- elaboration that reads it crashes the worker.
  Lean.enableInitializersExecution
  -- Lean ≥ 4.24 no longer initializes `searchPathRef` from `LEAN_PATH` inside
  -- `workerMain`/`watchdogMain`. Custom worker binaries must do it themselves
  -- or the worker boots with an empty search path and every `import` fails
  -- with "unknown module prefix" before user code is reached.
  Lean.searchPathRef.set (← Lean.addSearchPathFromEnv {})
  match args with
  | [] =>
    let _ ← Lean.Server.Watchdog.watchdogMain []
  | ["--worker", f] =>
    dbg_trace s!"starting worker for {f}"
    let _ ← Lean.Server.FileWorker.workerMain {}
  | _ => throw <| IO.userError s!"unexpected arguments: {args}"
