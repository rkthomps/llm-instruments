import Lake
open Lake DSL

package «llm-instruments» where

lean_lib LlmInstruments

@[default_target]
lean_exe «llm-instruments» {
  root := `Main
  supportInterpreter := true
}

lean_exe «llm-instruments-server» {
  root := `Server
}

lean_lib Tests

lean_exe «test» {
  root := `Tests
  supportInterpreter := true
}
