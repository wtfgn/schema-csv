module

public import SchemaCsv.Constraints

public section

namespace SchemaCsv

structure Field where
  name : FieldName
  type : FieldType := .string
  title : Option String := none
  format: Option String := none
  exampleValue : Option String := none
  description : Option String := none
  constraints : ConstraintsOf type
  -- deriving Repr, BEq
  -- need a manual instance because of the dependent field

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

def Field.required (f : Field) : Bool :=
  match f.type, f.constraints with
  | .string,  (c : StringConstraints .string) => c.required
  | .integer, (c : IntegerConstraints .integer) => c.required
  | .number,  (c : NumberConstraints .number) => c.required
  | .boolean, (c : BooleanConstraints .boolean) => c.required

def Field.cellType (f : Field) : Type :=
  let P := f.refinedType
  if f.required then P else Option P

end SchemaCsv
