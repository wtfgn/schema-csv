module

public import SchemaCsv.Core.Column

/-!
# Schemas and schema well-formedness

A schema is a value: it can be stored, compared, and (in M7) proved to be a
relaxation of another schema. That is the whole reason constraints live in this
record rather than in the type of a cell.
-/

public section

namespace SchemaCsv

structure Schema where
  /-- Optional document name, used in messages. -/
  name : Option String := none
  /-- Optional schema version string. Free-form until M7. -/
  version : Option String := none
  fields : List Column := []
  /-- Physical texts that mean "no value". Applied before casting. -/
  missingValues : List String := [""]
  /-- Composite primary key, as field names. Empty means "no key check". -/
  primaryKey : List String := []
  trueValues : List String := ["true", "True", "TRUE"]
  falseValues : List String := ["false", "False", "FALSE"]
  deriving Repr, DecidableEq

namespace Schema

def fieldNames (s : Schema) : List String :=
  s.fields.map (·.name)

/-- Look up a column by name. -/
def fieldOf? (s : Schema) (n : String) : Option Column :=
  s.fields.find? fun c => c.name == n

/-- Is this physical text one of the schema's missing values? -/
def isMissingValue (s : Schema) (raw : String) : Bool :=
  s.missingValues.contains raw

/-- Executable form: every column is well-formed. -/
@[expose]
def fieldsOKB (s : Schema) : Bool :=
  s.fields.all fun c => c.wellFormedB

abbrev fieldsOK (s : Schema) : Prop := fieldsOKB s = true

/-- Every primary-key field is required, so a key cell can never be null. -/
abbrev pkRequired (s : Schema) : Prop :=
  ∀ n ∈ s.primaryKey, ∃ c ∈ s.fields, c.name = n ∧ c.required = true

/-- A schema is well-formed when column names are unique, each column is
well-formed, and the declared key is a subset of the fields and covers only
required columns.

Note what is *not* required: a non-empty `fields`. An empty schema is
well-formed and accepts any table of zero-width rows, which keeps the predicate
closed under the obvious constructors. -/
abbrev WellFormed (s : Schema) : Prop :=
  fieldsOK s ∧
  s.fieldNames.Nodup ∧
  s.primaryKey ⊆ s.fieldNames ∧
  s.primaryKey.Nodup ∧
  pkRequired s

end Schema

end SchemaCsv
