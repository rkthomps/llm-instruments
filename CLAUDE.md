# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Build & Run

```bash
# Build everything
lake build

# Build just the executable
lake build llm-instruments

# Run commands
./.lake/build/bin/llm-instruments heartbeat
./.lake/build/bin/llm-instruments theorem-info <path/to/file.lean>

# theorem-info with sample queries (repeatable; default is zero samples)
./.lake/build/bin/llm-instruments theorem-info <path/to/file.lean> \
  --sample '{"expandProportion":0.5,"depthWeight":1.0,"temperature":0.0,"seed":0}' \
  --sample '{"expandProportion":0.5,"depthWeight":-1.0,"temperature":0.0,"seed":0}'
```

CI uses `leanprover/lean-action@v1` (see `.github/workflows/lean_action_ci.yml`). Lean version is pinned in `lean-toolchain` (currently `leanprover/lean4:v4.10.0`).

## Architecture

The executable (`Main.lean`) exposes two CLI commands:

- **`heartbeat`** — returns exit code 0; used by callers to verify the binary exists and works.
- **`theorem-info <file> [--sample <json>]...`** — runs Lean's elaborator on a `.lean` file, extracts all theorems/lemmas, and prints a JSON array of `ExtendedTheoremInfo` records. Each `--sample` flag takes a JSON object matching `ProofSampleArguments` (`expandProportion`, `depthWeight`, `temperature`, `seed`) and produces one entry in each theorem's `samples` array. Default is zero samples.

### Data flow for `theorem-info`

1. **`RunFile.lean`** — `runFile`: parses header, processes imports via `processHeader`, then runs `IO.processCommands` to elaborate the full file. Returns `(Frontend.State, Parser.InputContext)`. This is marked `unsafe` because it calls `enableInitializersExecution`.

2. **`FindTheorems.lean`** — `findTheorems` calls `runFile`, then passes the resulting `Frontend.State` to `theoremInfosFromState`. That function walks the `InfoTree` array from `state.commandState.infoState.trees`, calling `traverseITree` on each. `checkForTheoremInfo` matches `.ofCommandInfo` nodes against the `theorem` syntax pattern to extract `TheoremInfoAndStx` (which extends `TheoremInfo` with the raw `Syntax`).

3. **`TheoremInfo`** struct (in `FindTheorems.lean`) holds `name : String`, `range : Range`, `sigRange : Range`, `valRange : Range` — all LSP ranges — and derives `ToJson`.

4. **`Main.lean`** — `extendTheoremInfo` runs in `MetaM` per theorem and produces `ExtendedTheoremInfo`, which adds `bagOfTactics : List TacticInfo` (via `getTactics` from `TheoremCharacterization.lean`), `numExpands : Nat` (the maximum expand range from `ProofPrefix.lean`'s `HiddenTacticSyntax`), and `samples : List ProofSample` (one per `--sample` flag, each pretty-printed alongside its ground-truth source and the originating arguments).

### Lemma handling

`lemma` declarations require special handling because Lean's `lemma` keyword comes from Batteries (not imported here). `Tests/TestFiles/TestFile.lean` defines a custom `lemma` syntax macro that re-encodes lemmas as `theorem` declarations. In `FindTheorems.lean`, lemmas that don't match the `theorem` quote pattern are handled via a fallback that checks `stx.getKind == \`lemma` and manually indexes into the syntax array.

### Sampling internals

- **`LlmInstruments/ProofPrefix.lean`** — implements proof-prefix sampling. `createInitialHiddenTacticSyntax` wraps the proof's tactic sequence in a `HiddenTacticSyntax` tree where all tactic-sequence children start hidden. `getExpandCandidates` enumerates the next expansion steps; `iterateExpand` repeatedly applies a `SelectFn` to grow the visible prefix; `expandProportion` runs that loop for `round(proportion * maxExpands)` steps. `selectDepthWeighted depthWeight temperature` is the selector used by the CLI: positive `depthWeight` prefers deeper candidates, negative prefers shallower; `temperature == 0` is greedy, higher values softmax-sample.

- **`LlmInstruments/TheoremCharacterization.lean`** — `getTactics` walks a theorem's syntax tree and returns each tactic occurrence as a `TacticInfo` (`name`, `kind`). `getTacticFrequencies` aggregates those into `TacticFrequency` counts (defined but not yet emitted by the CLI).
