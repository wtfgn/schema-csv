/-
`lake test` driver.

Everything the core claims is checked at *build* time: `Tests/Model.lean` and
`Tests/Check.lean` use `#guard` (which evaluates the checkers) and
`example … := by decide`, so `lake build` already fails if a checker misbehaves.

This driver exists for the suites that need to run as a program — casting and
CSV in M3 — and returns 1 as soon as any suite fails.
-/

def main : IO UInt32 := do
  IO.println "tests: core cases are checked at build time (Tests/Model.lean, Tests/Check.lean)"
  IO.println "tests: 0 runtime suites registered (M3: casting, CSV)"
  return 0
