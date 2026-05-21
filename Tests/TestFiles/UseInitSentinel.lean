import LlmInstruments.InitSentinel

#eval show IO Unit from do
  IO.println s!"sentinel = {← sentinelRef.get}"
