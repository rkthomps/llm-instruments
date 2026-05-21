/-- Regression fixture support: a plain `initialize`d `IO.Ref`. Its
initializer runs on import only when the importing process has called
`Lean.enableInitializersExecution`. -/
initialize sentinelRef : IO.Ref Nat ← IO.mkRef 41
