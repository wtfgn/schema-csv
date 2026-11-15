/-
Axiom audit gate (design decision D13).

Any theorem this project *claims* publicly must be free of `sorryAx`; the goal is
also to stay free of `Classical.choice` so the checker remains constructive and
executable. CI runs this file and fails when a forbidden axiom shows up.

TEMPORARY (M0): these are theorems of the pre-rewrite model. They are replaced
at M2 by the v0.1 core theorems (`validate_sound`, `validate_complete`,
`validate_iff`, ...), which is the list that actually matters.
-/
import SchemaCsv

open SchemaCsv

#print axioms HasColList.field_mem
#print axioms Schema.field_eq_of_name_eq
#print axioms HasCol.required_of_primaryKey
