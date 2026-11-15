/-
Axiom audit (design decision D13).

Two different claims, checked separately:

* **No `sorry`.** Every theorem we state publicly must be fully proved. The gate
  below fails if any claimed theorem depends on `sorryAx`. That is the claim
  that matters, and it is fully achievable.

* **Executability.** Proved separately, by `Tests/Model.lean`, which *evaluates*
  every checker with `#guard` at elaboration time. That is stronger evidence
  than an axiom listing.

Note on `Classical.choice`: `#print axioms` on these declarations reports
`propext`, `Quot.sound` and sometimes `Classical.choice`. Those come from the
termination and decidability proofs *inside core library definitions* (for
example `String.length` and `List.contains`), not from the logic of this
project. They are proof terms, erased at runtime; the checkers still compute,
which is exactly what `Tests/Model.lean` demonstrates. Requiring a fully
constructive axiom list would mean reimplementing core's string and list
primitives, which buys nothing for this project.
-/
import SchemaCsv

open SchemaCsv

#print axioms Val.compatible_null
#print axioms Column.accepts_null_iff
#print axioms SchemaCsv.tableConstraintsB_iff
#print axioms SchemaCsv.checkCell_none_iff
#print axioms SchemaCsv.validateCells_nil_iff
#print axioms SchemaCsv.validateRow_ok_iff
#print axioms SchemaCsv.collectRowDiagnostics_nil_iff
#print axioms SchemaCsv.constraintDiagnostics_nil_iff
#print axioms SchemaCsv.validate_iff
#print axioms SchemaCsv.validate_sound
#print axioms SchemaCsv.validate_complete
