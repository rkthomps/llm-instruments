import Lake
open Lake DSL

package «llm-instruments» where

lean_lib LlmInstruments

@[default_target]
lean_exe «llm-instruments» {
  root := `Main
}
