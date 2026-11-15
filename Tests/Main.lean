/-
`lake test` driver.

The model cases in `Tests/Model.lean` run at *build* time (`#guard`), so
`lake build` already fails if a checker misbehaves. This driver is for the
behavioural suites that need to run as a program — casting and CSV in M2/M3 —
and returns 1 as soon as any suite fails.
-/

def main : IO UInt32 := do
  IO.println "tests: model cases are checked at build time (Tests/Model.lean)"
  IO.println "tests: 0 runtime suites registered (M2/M3)"
  return 0
