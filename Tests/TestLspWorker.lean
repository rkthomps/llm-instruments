import Tests.Common
import Lean
import Lean.Data.Lsp
import Lean.Data.Lsp.Communication
import Lean.Data.JsonRpc

namespace Tests

open Lean
open Lean.Lsp
open Lean.JsonRpc

/-- Substring containment that works on every Lean toolchain we target
(`String.contains` only accepts a `String` pattern from 4.29 onward). -/
private def strContains (s pat : String) : Bool :=
  (s.splitOn pat).length > 1

/-- Server binary that this test drives. Resolved relative to the package root,
which is the CWD when `lake exe test` runs. -/
private def serverBinPath : System.FilePath :=
  "." / ".lake" / "build" / "bin" / "llm-instruments-server"

private def searchPathFixturePath : System.FilePath :=
  "Tests" / "TestFiles" / "ImportInit.lean"

private def initSentinelFixturePath : System.FilePath :=
  "Tests" / "TestFiles" / "UseInitSentinel.lean"

/-- Read LSP messages off `s` until `stop` returns `true` on one of them. Every
`publishDiagnostics` notification we see along the way is appended to `diags`. -/
private partial def drainUntil
    (s : IO.FS.Stream)
    (stop : JsonRpc.Message → Bool)
    (diags : IO.Ref (Array PublishDiagnosticsParams))
    (budget : Nat) : IO JsonRpc.Message := do
  if budget = 0 then
    throw <| IO.userError "exceeded message budget while waiting for LSP response"
  let m ← s.readLspMessage
  match m with
  | .notification "textDocument/publishDiagnostics" (some params) =>
    match (fromJson? (toJson params) : Except String PublishDiagnosticsParams) with
    | .ok pd => diags.modify (·.push pd)
    | .error _ => pure ()
  | _ => pure ()
  if stop m then return m
  drainUntil s stop diags (budget - 1)

/-- Regression test for the worker-spawn search-path bug.

Background. Starting with Lean 4.24, `Lean.Server.FileWorker.workerMain` no
longer populates `Lean.searchPathRef` from `LEAN_PATH` on its own. A custom
worker binary that doesn't do so itself boots with an empty search path, and
the very first `import` in every opened file fails with "unknown module prefix".

This test exercises the actual worker-spawn handshake — anything purely
in-process would miss the bug, since the in-process elaborator inherits the
lake-managed search path.

What we do:
  1. Build and spawn `llm-instruments-server` with `LEAN_WORKER_PATH` set to
     itself, so the watchdog spawns the same binary as the worker.
  2. Drive `initialize` → `initialized` → `didOpen` for a small fixture that
     starts with `import Init`, then `waitForDiagnostics`.
  3. Assert that no diagnostic carries the "unknown module prefix" message.
  4. Negative control: assert the worker's stderr contains `starting worker for`,
     so a future refactor that bypasses the worker entirely (and silently
     makes this test pass for the wrong reason) is caught. -/
def testLspWorkerSearchPath : Test := {
  name := "testLspWorkerSearchPath",
  run := do
    -- Build the server binary on demand; this is a no-op if up to date.
    let buildOut ← IO.Process.output {
      cmd := "lake", args := #["build", "llm-instruments-server"]
    }
    if buildOut.exitCode != 0 then
      throw <| IO.userError <|
        s!"`lake build llm-instruments-server` failed (exit {buildOut.exitCode}):\n" ++
        s!"stdout:\n{buildOut.stdout}\nstderr:\n{buildOut.stderr}"

    unless ← serverBinPath.pathExists do
      throw <| IO.userError s!"server binary missing at {serverBinPath} after build"
    unless ← searchPathFixturePath.pathExists do
      throw <| IO.userError s!"LSP fixture missing at {searchPathFixturePath}"

    let absBin     ← IO.FS.realPath serverBinPath
    let absFixture ← IO.FS.realPath searchPathFixturePath
    let fixtureText ← IO.FS.readFile absFixture
    let fileUri := s!"file://{absFixture}"

    let child ← IO.Process.spawn {
      cmd    := absBin.toString
      args   := #[]
      stdin  := .piped
      stdout := .piped
      stderr := .piped
      env    := #[("LEAN_WORKER_PATH", some absBin.toString)]
    }
    -- Drain stderr in a background task so the pipe buffer never blocks the
    -- worker; we read the collected bytes after `child.wait`.
    let stderrTask ← IO.asTask child.stderr.readToEnd Task.Priority.dedicated

    let toServer := IO.FS.Stream.ofHandle child.stdin
    let fromServer := IO.FS.Stream.ofHandle child.stdout

    let diags ← IO.mkRef (#[] : Array PublishDiagnosticsParams)

    -- 1. initialize
    let initParams : InitializeParams := {
      processId? := none
      clientInfo? := some { name := "llm-instruments-tests", version? := none }
      capabilities := {}
      trace := .off
    }
    toServer.writeLspRequest (α := InitializeParams)
      { id := .num 1, method := "initialize", param := initParams }
    let _ ← drainUntil fromServer
      (fun | .response (.num 1) _ => true | _ => false)
      diags 64

    -- 2. initialized
    toServer.writeLspNotification (α := InitializedParams)
      { method := "initialized", param := InitializedParams.mk }

    -- 3. didOpen for a file that imports Init
    let didOpenParams : LeanDidOpenTextDocumentParams := {
      textDocument := {
        uri        := fileUri
        languageId := "lean"
        version    := 1
        text       := fixtureText
      }
    }
    toServer.writeLspNotification (α := LeanDidOpenTextDocumentParams)
      { method := "textDocument/didOpen", param := didOpenParams }

    -- 4. waitForDiagnostics — collect every publishDiagnostics until the
    --    server says it's done.
    let waitParams : WaitForDiagnosticsParams := { uri := fileUri, version := 1 }
    toServer.writeLspRequest (α := WaitForDiagnosticsParams)
      { id := .num 2, method := "textDocument/waitForDiagnostics", param := waitParams }
    let _ ← drainUntil fromServer
      (fun
        | .response      (.num 2) _   => true
        | .responseError (.num 2) _ _ _ => true
        | _                             => false)
      diags 512

    -- Polite shutdown so the worker isn't killed mid-write.
    toServer.writeLspRequest (α := Json)
      { id := .num 3, method := "shutdown", param := Json.null }
    try
      let _ ← drainUntil fromServer
        (fun | .response (.num 3) _ => true
             | .responseError (.num 3) _ _ _ => true
             | _ => false)
        diags 64
    catch _ => pure ()
    toServer.writeLspNotification (α := Json)
      { method := "exit", param := Json.null }

    let _ ← child.wait
    let stderrResult ← IO.wait stderrTask
    let stderrText :=
      match stderrResult with
      | .ok t    => t
      | .error _ => ""

    -- Assertion: no "unknown module prefix" diagnostic.
    let allDiags ← diags.get
    for pd in allDiags do
      for d in pd.diagnostics do
        if strContains d.message "unknown module prefix" then
          throw <| IO.userError <|
            "worker emitted an 'unknown module prefix' diagnostic — " ++
            "Lean.searchPathRef appears uninitialized in the worker process.\n" ++
            s!"diagnostic: {d.message}\n" ++
            s!"worker stderr:\n{stderrText}"

    -- Negative control: confirm we actually reached the worker.
    unless strContains stderrText "starting worker for" do
      throw <| IO.userError <|
        "expected worker stderr to contain 'starting worker for' — the test " ++
        "may have passed for the wrong reason (e.g. the watchdog handled the " ++
        s!"request without spawning a worker).\nstderr:\n{stderrText}"
}

/-- Regression test for the worker-spawn initializer-execution bug.

Background. `Lean.Server.FileWorker.workerMain` does not call
`Lean.enableInitializersExecution` for the host binary; the stock `lean`
executable enables initializer execution itself before booting the worker.
A custom worker binary that doesn't do so boots with imported modules'
`initialize`/`[init]` declarations left unevaluated, so the first elaboration
that reads any imported `initialize`d `IO.Ref` crashes the worker with
`cannot evaluate '[init]' declaration … in the same module` (surfaced to the
client as RPC `-32902`, "Server process … crashed").

This test exercises the worker-spawn handshake against a fixture that imports
`LlmInstruments.InitSentinel` (a plain `initialize`d `IO.Ref`) and reads it,
and asserts that the `waitForDiagnostics` response is a normal response (not a
`-32902` `responseError`) and that no diagnostic carries the `cannot evaluate`
/ `sentinelRef` message. The negative control mirrors `testLspWorkerSearchPath`. -/
def testLspWorkerInitializers : Test := {
  name := "testLspWorkerInitializers",
  run := do
    let buildOut ← IO.Process.output {
      cmd := "lake", args := #["build", "llm-instruments-server"]
    }
    if buildOut.exitCode != 0 then
      throw <| IO.userError <|
        s!"`lake build llm-instruments-server` failed (exit {buildOut.exitCode}):\n" ++
        s!"stdout:\n{buildOut.stdout}\nstderr:\n{buildOut.stderr}"

    unless ← serverBinPath.pathExists do
      throw <| IO.userError s!"server binary missing at {serverBinPath} after build"
    unless ← initSentinelFixturePath.pathExists do
      throw <| IO.userError s!"LSP fixture missing at {initSentinelFixturePath}"

    let absBin     ← IO.FS.realPath serverBinPath
    let absFixture ← IO.FS.realPath initSentinelFixturePath
    let fixtureText ← IO.FS.readFile absFixture
    let fileUri := s!"file://{absFixture}"

    let child ← IO.Process.spawn {
      cmd    := absBin.toString
      args   := #[]
      stdin  := .piped
      stdout := .piped
      stderr := .piped
      env    := #[("LEAN_WORKER_PATH", some absBin.toString)]
    }
    let stderrTask ← IO.asTask child.stderr.readToEnd Task.Priority.dedicated

    let toServer := IO.FS.Stream.ofHandle child.stdin
    let fromServer := IO.FS.Stream.ofHandle child.stdout

    let diags ← IO.mkRef (#[] : Array PublishDiagnosticsParams)

    let initParams : InitializeParams := {
      processId? := none
      clientInfo? := some { name := "llm-instruments-tests", version? := none }
      capabilities := {}
      trace := .off
    }
    toServer.writeLspRequest (α := InitializeParams)
      { id := .num 1, method := "initialize", param := initParams }
    let _ ← drainUntil fromServer
      (fun | .response (.num 1) _ => true | _ => false)
      diags 64

    toServer.writeLspNotification (α := InitializedParams)
      { method := "initialized", param := InitializedParams.mk }

    let didOpenParams : LeanDidOpenTextDocumentParams := {
      textDocument := {
        uri        := fileUri
        languageId := "lean"
        version    := 1
        text       := fixtureText
      }
    }
    toServer.writeLspNotification (α := LeanDidOpenTextDocumentParams)
      { method := "textDocument/didOpen", param := didOpenParams }

    let waitParams : WaitForDiagnosticsParams := { uri := fileUri, version := 1 }
    toServer.writeLspRequest (α := WaitForDiagnosticsParams)
      { id := .num 2, method := "textDocument/waitForDiagnostics", param := waitParams }
    let waitResp ← drainUntil fromServer
      (fun
        | .response      (.num 2) _   => true
        | .responseError (.num 2) _ _ _ => true
        | _                             => false)
      diags 512

    toServer.writeLspRequest (α := Json)
      { id := .num 3, method := "shutdown", param := Json.null }
    try
      let _ ← drainUntil fromServer
        (fun | .response (.num 3) _ => true
             | .responseError (.num 3) _ _ _ => true
             | _ => false)
        diags 64
    catch _ => pure ()
    toServer.writeLspNotification (α := Json)
      { method := "exit", param := Json.null }

    let _ ← child.wait
    let stderrResult ← IO.wait stderrTask
    let stderrText :=
      match stderrResult with
      | .ok t    => t
      | .error _ => ""

    -- Assertion: `waitForDiagnostics` returned a normal response, not an
    -- error indicating the worker process died (RPC -32902).
    match waitResp with
    | .responseError _ code msg _ =>
      throw <| IO.userError <|
        s!"waitForDiagnostics returned responseError (code {toJson code}): {msg}\n" ++
        "this is the symptom of the worker crashing because " ++
        "`Lean.enableInitializersExecution` was not called in `Server.lean`.\n" ++
        s!"worker stderr:\n{stderrText}"
    | _ => pure ()

    -- Assertion: no `cannot evaluate '[init]' declaration` diagnostic.
    let allDiags ← diags.get
    for pd in allDiags do
      for d in pd.diagnostics do
        if strContains d.message "cannot evaluate" then
          throw <| IO.userError <|
            "worker emitted a 'cannot evaluate' diagnostic — imported " ++
            "`initialize`/`[init]` declarations appear unevaluated in the " ++
            "worker process (missing `Lean.enableInitializersExecution`).\n" ++
            s!"diagnostic: {d.message}\n" ++
            s!"worker stderr:\n{stderrText}"
        if strContains d.message "sentinelRef" && strContains d.message "in the same module" then
          throw <| IO.userError <|
            "worker emitted a 'sentinelRef … in the same module' diagnostic — " ++
            "imported `initialize`d ref left uninitialized.\n" ++
            s!"diagnostic: {d.message}\n" ++
            s!"worker stderr:\n{stderrText}"

    -- Also catch the case where the failure surfaced only on the worker's
    -- stderr (e.g. the worker terminated via libc++abi before publishing
    -- diagnostics).
    if strContains stderrText "cannot evaluate" then
      throw <| IO.userError <|
        "worker stderr contains 'cannot evaluate' — imported `initialize` " ++
        "declarations were not executed (missing " ++
        "`Lean.enableInitializersExecution`).\n" ++
        s!"stderr:\n{stderrText}"

    unless strContains stderrText "starting worker for" do
      throw <| IO.userError <|
        "expected worker stderr to contain 'starting worker for' — the test " ++
        "may have passed for the wrong reason (e.g. the watchdog handled the " ++
        s!"request without spawning a worker).\nstderr:\n{stderrText}"
}

end Tests
