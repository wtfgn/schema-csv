module

public import SchemaCsv.Core.Table

/-!
# Satisfaction

`Satisfies s t` is the contract: what it means for a table to conform to a
schema. The mathematical statement is `docs/SEMANTICS.md` §7; the definitions
here are its executable form.

The three conjuncts mirror the three kinds of constraint:

* `rowAccepts` — a *cell* property, one column at a time, plus width agreement;
* `uniqueOK` — a *column* property, across all rows;
* `primaryKeyOK` — a *key* property, across all rows.
-/

public section

namespace SchemaCsv

/-! ## Row acceptance -/

/-- Executable form: walk `fields` and the row together, requiring each cell to
be accepted by its column, and requiring both lists to end at the same time.
A width mismatch is `false`, never padding. -/
@[expose]
def rowAcceptsAux : List Column → Row → Bool
  | [], [] => true
  | c :: cs, v :: vs => c.acceptsB v && rowAcceptsAux cs vs
  | _, _ => false

/-- Does every cell of this row satisfy its column, and is the row the right
number of columns? -/
abbrev rowAccepts (s : Schema) (r : Row) : Prop := rowAcceptsAux s.fields r = true

/-! ## Column uniqueness -/

/-- Executable form: every column marked `unique` has pairwise-distinct
**non-null** values.

Nulls are filtered out before the check, so two nulls never collide
(PostgreSQL's reading, policy 2 in `docs/SEMANTICS.md`). The opposite convention
is a policy flag, not a different model. -/
@[expose]
def uniqueOKB (s : Schema) (t : Table) : Bool :=
  (s.fields.filter (·.unique)).all fun c =>
    decide ((columnValues s t c.name).filter (fun v => !v.isNull)).Nodup

abbrev uniqueOK (s : Schema) (t : Table) : Prop := uniqueOKB s t = true

/-! ## Primary key -/

/-- The primary-key projection of a row, in schema field order.

Fields not named in `primaryKey` contribute nothing, so the result is a tuple of
the key columns. Because `Schema.WellFormed` requires key columns to be
`required`, no element of this projection can be null. -/
@[expose]
def keyOf (s : Schema) (r : Row) : List Val :=
  s.fields.filterMap fun c =>
    if s.primaryKey.contains c.name then cellOfAux c.name s.fields r else none

/-- Executable form: no two rows share a primary key. An empty `primaryKey`
means "no key check", which is `true` by convention. -/
@[expose]
def primaryKeyOKB (s : Schema) (t : Table) : Bool :=
  s.primaryKey.isEmpty || decide (t.map (keyOf s)).Nodup

abbrev primaryKeyOK (s : Schema) (t : Table) : Prop := primaryKeyOKB s t = true

/-! ## The contract -/

/-- Both table-level constraint families hold. Kept separate from `Satisfies`
because `validate` checks them after the rows, and the two have different
failure modes. -/
@[expose]
def tableConstraintsB (s : Schema) (t : Table) : Bool :=
  uniqueOKB s t && primaryKeyOKB s t

theorem tableConstraintsB_iff (s : Schema) (t : Table) :
    tableConstraintsB s t = true ↔ uniqueOK s t ∧ primaryKeyOK s t := by
  unfold tableConstraintsB uniqueOK primaryKeyOK
  rw [Bool.and_eq_true]

/-- A table satisfies a schema when the schema is well-formed, every row is
accepted cell by cell, and the table-level constraints hold.

`WellFormed` is part of the predicate on purpose: a malformed schema cannot make
data "valid", and including it means `validate` returning `ok` also certifies the
schema. -/
abbrev Satisfies (s : Schema) (t : Table) : Prop :=
  s.WellFormed ∧
  (∀ r ∈ t, rowAccepts s r) ∧
  uniqueOK s t ∧
  primaryKeyOK s t

end SchemaCsv
