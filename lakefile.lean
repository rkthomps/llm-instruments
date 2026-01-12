import Lake
open Lake DSL

package «llm-instruments» where

require Regex from git "https://github.com/bergmannjg/regex" @ "v4.24.0"

lean_lib LlmInstruments

@[default_target]
lean_exe «llm-instruments» {
  root := `Main
  supportInterpreter := true
}


lean_exe «illegal-prefix» {
  root := `Prefix
  supportInterpreter := true
}
