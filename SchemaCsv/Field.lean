module

public import SchemaCsv.Constraints
public import SchemaCsv.Format

public section

namespace SchemaCsv

structure Field where
  name : FieldName
  type : FieldType := .string
  title : Option String := none
  format: FormatOf type := default
  exampleValue : Option String := none
  description : Option String := none
  constraints : ConstraintsOf type
  deriving Repr, DecidableEq

@[expose]
def Field.refinedType (f : Field) : Type :=
  match f.type, f.constraints with
  | .string, (c : StringConstraints .string) =>
      { s : String //
          optLower c.minLength s.length ∧
          optUpper c.maxLength s.length ∧
          optEnum c.enum s
          -- pattern: omit for now, or add `Matches c.pattern s` later
      }
  | .integer, (c : IntegerConstraints .integer) =>
      { n : Int //
          optLower c.minimum n ∧
          optUpper c.maximum n ∧
          optEnum c.enum n
      }
  | .number, (c : NumberConstraints .number) =>
      { x : Float //
          optLower c.minimum x ∧
          optUpper c.maximum x ∧
          optEnum c.enum x
      }
  | .boolean, (c : BooleanConstraints .boolean) =>
      { b : Bool // optEnum c.enum b }

@[expose]
def Field.required (f : Field) : Bool :=
  match f.type, f.constraints with
  | .string,  (c : StringConstraints .string) => c.required
  | .integer, (c : IntegerConstraints .integer) => c.required
  | .number,  (c : NumberConstraints .number) => c.required
  | .boolean, (c : BooleanConstraints .boolean) => c.required

@[expose]
def Field.cellType (f : Field) : Type :=
  let P := f.refinedType
  if f.required then P else Option P

instance {f : Field} : DecidableEq f.refinedType := by
  cases f with
  | mk _ type =>
      cases type <;> simp [Field.refinedType] <;> infer_instance

instance {f : Field} : Repr f.refinedType := by
  cases f with
  | mk _ type =>
      cases type <;> simp [Field.refinedType] <;> infer_instance

instance {f : Field} : Repr f.cellType := by
  by_cases h : f.required = true <;> simp [Field.cellType, h] <;> infer_instance

instance {f : Field} : DecidableEq f.cellType := by
  by_cases h : f.required = true <;> simp [Field.cellType, h] <;> infer_instance

end SchemaCsv
