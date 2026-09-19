module

public import SchemaCsv.Field

public section

namespace SchemaCsv

abbrev SchemaFields := List Field

structure Schema where
  fields : SchemaFields
  missingValues : List String := [""] -- default to be empty string
  primaryKey : List FieldName := []
  -- TODO: add foreign key support
  -- foreignKey : List ForeignKey := []
  deriving Repr, DecidableEq

abbrev Schema.types (s : Schema) : List FieldType :=
  s.fields.map (·.type)

abbrev Schema.fieldNames (s : Schema) : List FieldName :=
  s.fields.map (·.name)

def Schema.uniqueFields (s : Schema) : List Field :=
  s.fields.filter (fun f =>
    match f.type, f.constraints with
    | .string, c => c.unique
    | .integer, c => c.unique
    | .number, c => c.unique
    | .boolean, c => c.unique)

def Schema.fieldByName? (s : Schema) (n : FieldName) : Option Field :=
  s.fields.find? (fun f => f.name = n)

/-- A schema is well-formed when:
  - field names are unique
    - every field name is non-empty
    - PK combination is a subset of field names
    - PK fields are unique
    - PK fields are required
-/
abbrev Schema.WellFormed (s : Schema) : Prop :=
  (s.fieldNames.Nodup) ∧
  (∀ n ∈ s.fieldNames, n ≠ "") ∧
  (s.primaryKey ⊆ s.fieldNames) ∧
  (s.primaryKey.Nodup) ∧
  (∀ n ∈ s.primaryKey, ∃ f ∈ s.fields,
    f.name = n ∧ f.required = true)

instance (s : Schema) : Decidable (s.WellFormed) := by
  dsimp [Schema.WellFormed]
  infer_instance

@[expose]
def WellFormedSchema : Type :=
  { s : Schema // s.WellFormed }

def Schema.mkWf
    (s : Schema)
    (h : s.WellFormed := by decide)
    : WellFormedSchema :=
  ⟨s, h⟩

end SchemaCsv
