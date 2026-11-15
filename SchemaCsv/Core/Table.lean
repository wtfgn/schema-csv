module

public import SchemaCsv.Core.Schema

/-!
# Rows and tables

A row is a plain list of values, aligned with `Schema.fields` by position.
Nothing about a row's *shape* is in its type; width agreement is a property
checked by `rowAccepts`, so a malformed row is a value that fails validation
rather than a value that cannot be written down.

All cell access here is structural (walk two lists together) rather than
index-based, which is what makes the satisfaction proofs in `Satisfies` and
`Check` straightforward.
-/

public section

namespace SchemaCsv

abbrev Row := List Val

abbrev Table := List Row

/-- The cell of the column named `name`, if this row has one.

Walks `fields` and the row together, so a ragged row simply stops contributing
cells instead of producing an out-of-bounds access. Whether the row was the
right width is decided separately, by `rowAccepts`. -/
def cellOfAux (name : String) : List Column → Row → Option Val
  | [], _ => none
  | c :: cs, v :: vs => if c.name == name then some v else cellOfAux name cs vs
  | _ :: _, [] => none

/-- The cell of the named column in this row. -/
def cellOf (s : Schema) (r : Row) (name : String) : Option Val :=
  cellOfAux name s.fields r

/-- All values of the named column, in row order. -/
def columnValues (s : Schema) (t : Table) (name : String) : List Val :=
  t.filterMap fun r => cellOfAux name s.fields r

end SchemaCsv
