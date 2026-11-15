module

public import SchemaCsv.Core.Check

/-!
# Certified tables

A `Certified s` is a table together with a proof that it satisfies `s`. This is
the "proof-carrying data" story in its cheapest useful form: the proof is a
predicate on the whole table, so downstream verified code can take `Certified s`
as input and know the contract holds, without any per-cell dependent types.
-/

public section

namespace SchemaCsv

/-- A table that provably satisfies a schema. -/
abbrev Certified (s : Schema) : Type :=
  { t : Table // Satisfies s t }

/-- Promote a table, given the proof. -/
def certify (s : Schema) (t : Table) (h : Satisfies s t) : Certified s :=
  ⟨t, h⟩

/-- Promote a table that `validate` accepted. -/
def certifyOfValidate (s : Schema) (t : Table) (h : validate s t = .ok ()) :
    Certified s :=
  ⟨t, (validate_iff s t).mp h⟩

namespace Certified

theorem satisfies {s : Schema} (ct : Certified s) : Satisfies s ct.val :=
  ct.property

end Certified

end SchemaCsv
