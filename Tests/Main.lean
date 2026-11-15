/-
`lake test` driver.

M0 only wires the plumbing: suite runners are registered in M2 (`Tests/Check.lean`)
and M3 (`Tests/Csv.lean`). Returning 0 means "no suites registered yet" — it is
NOT a claim that the library is correct. Real assertions arrive with those
milestones, and this driver returns 1 as soon as any suite fails.
-/

def main : IO UInt32 := do
  IO.println "tests: 0 suites registered (suite runners land at M2/M3)"
  return 0
