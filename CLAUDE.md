# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Build & Run

```bash
# Build everything
lake build

# Build just the executable
lake build llm-instruments

# Run commands
./build/bin/llm-instruments heartbeat
./build/bin/llm-instruments theorem-info <path/to/file.lean>
```

CI uses `leanprover/lean-action@v1` (see `.github/workflows/lean_action_ci.yml`). Lean version is pinned in `lean-toolchain` (currently `leanprover/lean4:v4.10.0`).

## Architecture

The executable (`Main.lean`) exposes two CLI commands:

- **`heartbeat`** — returns exit code 0; used by callers to verify the binary exists and works.
- **`theorem-info <file>`** — runs Lean's elaborator on a `.lean` file, extracts all theorems/lemmas with their names and LSP ranges (full declaration, signature, proof value), and prints JSON.

### Data flow for `theorem-info`

1. **`RunFile.lean`** — `runFile`: parses header, processes imports via `processHeader`, then runs `IO.processCommands` to elaborate the full file. Returns `(Frontend.State, Parser.InputContext)`. This is marked `unsafe` because it calls `enableInitializersExecution`.

2. **`FindTheorems.lean`** — `findTheorems` calls `runFile`, then passes the resulting `Frontend.State` to `theoremInfosFromState`. That function walks the `InfoTree` array from `state.commandState.infoState.trees`, calling `traverseITree` on each. `checkForTheoremInfo` matches `.ofCommandInfo` nodes against the `theorem` syntax pattern to extract `TheoremInfo`.

3. **`TheoremInfo`** struct (in `FindTheorems.lean`) holds `name : String`, `range : Range`, `sigRange : Range`, `valRange : Range` — all LSP ranges — and derives `ToJson`.

### Lemma handling

`lemma` declarations require special handling because Lean's `lemma` keyword comes from Batteries (not imported here). `TestFile.lean` defines a custom `lemma` syntax macro that re-encodes lemmas as `theorem` declarations. In `FindTheorems.lean`, lemmas that don't match the `theorem` quote pattern are handled via a fallback that checks `stx.getKind == \`lemma` and manually indexes into the syntax array.

### In-progress files

- **`LlmInstruments/ProofPrefix.lean`** — exploratory work on sampling proof prefixes from syntax trees; not yet wired into the CLI.
- **`LlmInstruments/TheoremCharacterization.lean`** — stub for future syntactic characterization of theorems.
