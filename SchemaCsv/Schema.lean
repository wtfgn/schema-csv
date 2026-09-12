module

public import SchemaCsv.Field

public section

namespace SchemaCsv

abbrev SchemaFields := List Field

structure Schema where
  fields : SchemaFields
  missingValues : Array String := #[""] -- default to be empty string
  primaryKey : Option $ List FieldName := none
  foreignKey : Option $ List FieldName := none
  deriving Repr, DecidableEq

def Schema.types (s : Schema) : List FieldType :=
  s.fields.map (·.type)

def Schema.fieldNames (s : Schema) : List FieldName :=
  s.fields.map (·.name)

def Schema.uniqueFields (s : Schema) : List Field :=
  s.fields.filter (fun f =>
    match f.type, f.constraints with
    | .string, c => c.unique
    | .integer, c => c.unique
    | .number, c => c.unique
    | .boolean, c => c.unique)

/-- A schema is well-formed when:
    - every field name is non-empty
    - field names are unique
    - (optional later) primaryKey / foreignKey names actually exist
-/
abbrev Schema.WellFormed (s : Schema) : Prop :=
  (s.fieldNames.Nodup) ∧
  ∀ n ∈ s.fieldNames, n ≠ ""

def Schema.isWellFormed (s : Schema) : Bool :=
  decide (s.fieldNames.Nodup) &&
  s.fieldNames.all (fun n => !n.value.isEmpty)

instance (s : Schema) : Decidable (s.WellFormed) := by
  dsimp [Schema.WellFormed]
  infer_instance

@[expose]
def WellFormedSchema : Type :=
  { s : Schema // s.WellFormed }

def Schema.mkWf (s : Schema) (h : s.WellFormed := by decide) : WellFormedSchema :=
  ⟨s, h⟩

end SchemaCsv
