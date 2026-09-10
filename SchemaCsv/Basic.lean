
def hello := "world"

structure FieldName where
  toString : String
  deriving DecidableEq, Repr

namespace FieldName

def ofString (s : String) : FieldName := ⟨s⟩

instance : ToString FieldName where
  toString := FieldName.toString

instance : Coe String FieldName where
  coe := FieldName.ofString

end FieldName

inductive FieldType where
  | string
  | integer
  | number
  | boolean
  deriving Repr, BEq, DecidableEq

abbrev FieldType.asType : FieldType → Type
  | .string => String
  | .integer => Int
  | .number => Float -- or Rat?
  | .boolean => Bool

/-- Constraints that apply to ALL field types -/
structure CommonConstraints (t : FieldType)  where
  required : Bool := false
  unique   : Bool := false
  enum     : Option (List t.asType) := none

structure CollectonConstraints where
  maxLength : Option Nat := none
  minLength : Option Nat := none

structure StringConstraints (t : FieldType) extends CommonConstraints t, CollectonConstraints where
  pattern   : Option String := none

structure IntegerConstraints (t : FieldType) extends CommonConstraints t where
  minimum : Option Int := none
  maximum : Option Int := none

structure NumberConstraints (t : FieldType) extends CommonConstraints t where
  minimum : Option Float := none
  maximum : Option Float := none

structure BooleanConstraints (t : FieldType) extends CommonConstraints t where

/-- Constraints that make sense for a given field type. -/
def ConstraintsOf (t : FieldType) : Type :=
  match t with
  | .string  => StringConstraints t
  | .integer => IntegerConstraints t
  | .number  => NumberConstraints t
  | .boolean => BooleanConstraints t
  -- collections
  -- | .array  => ArrayConstraints   -- minLength, maxLength, common, enum, …
  -- | .object => ObjectConstraints
  -- ordered temporal / numeric-like
  -- | .date | .time | .datetime | .year | .yearmonth =>
  --     TemporalConstraints  -- minimum, maximum with the right payload type

def optLower {α : Type u} [LE α] (bound : Option α) (n : α) : Prop :=
  match bound with
  | none => True
  | some lo => lo ≤ n

def optUpper {α : Type u} [LE α] (bound : Option α) (n : α) : Prop :=
  match bound with
  | none => True
  | some hi => n ≤ hi

def optEnum {α : Type} (e : Option (List α)) (x : α) : Prop :=
  match e with
  | none => True
  | some vs => x ∈ vs

instance {α : Type u} [LE α] [DecidableLE α] (bound : Option α) (n : α) :
    Decidable (optLower bound n) := by
  cases bound <;> dsimp [optLower] <;> infer_instance

instance {α : Type u} [LE α] [DecidableLE α] (bound : Option α) (n : α) :
    Decidable (optUpper bound n) := by
  cases bound <;> dsimp [optUpper] <;> infer_instance

instance {α : Type} [DecidableEq α]
    (e : Option (List α)) (x : α) :
    Decidable (optEnum e x) := by
  cases e <;> dsimp [optEnum] <;> infer_instance

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
  | .string, c =>
      { s : String //
          optLower c.minLength s.length ∧
          optUpper c.maxLength s.length ∧
          optEnum c.enum s
          -- pattern: omit for now, or add `Matches c.pattern s` later
      }
  | .integer, c =>
      { n : Int //
          optLower c.minimum n ∧
          optUpper c.maximum n ∧
          optEnum c.enum n
      }
  | .number, c =>
      { x : Float //
          optLower c.minimum x ∧
          optUpper c.maximum x ∧
          optEnum c.enum x
      }
  | .boolean, c =>
      { b : Bool // optEnum c.enum b }

def Field.required (f : Field) : Bool :=
  match f.type, f.constraints with
  | .string,  c => c.required
  | .integer, c => c.required
  | .number,  c => c.required
  | .boolean, c => c.required

def Field.cellType (f : Field) : Type :=
  let P := f.refinedType
  if f.required then P else Option P

abbrev SchemaFields := List Field

structure Schema where
  fields : SchemaFields
  missingValues : Array String := #[""] -- default to be empty string
  primaryKey : Option $ List FieldName := none
  foreignKey : Option $ List FieldName := none
  -- deriving Repr, BEq

def Schema.types (s : Schema) : List FieldType :=
  s.fields.map (·.type)

def Schema.fieldNames (s : Schema) : List FieldName :=
  s.fields.map (·.name)

/-- A schema is well-formed when:
    - every field name is non-empty
    - field names are unique
    - (optional later) primaryKey / foreignKey names actually exist
-/
def Schema.WellFormed (s : Schema) : Prop :=
  (s.fieldNames.Nodup) ∧
  (s.fieldNames.all (not ∘ String.isEmpty ∘ toString))

def Schema.isWellFormed (s : Schema) : Bool :=
  s.fieldNames.Nodup &&
  s.fieldNames.all (not ∘ String.isEmpty ∘ toString)


-- Now the instance is immediate
instance (s : Schema) : Decidable s.WellFormed :=
  decidable_of_bool s.isWellFormed (by sorry)

def WfSchema : Type :=
  { s : Schema // s.WellFormed }

def Schema.mkWf (s : Schema) (h : s.WellFormed := by decide) : WfSchema :=
  ⟨s, h⟩

inductive HList {α : Type v} (β : α → Type u) : List α → Type (max u v)
  | nil  : HList β []
  | cons {i is} : β i → HList β is → HList β (i :: is)

def HList.nth {α β} : {ts : List α} → HList β ts → Nat → Option ((t : α) × β t)
  | _, .nil,       _   => none
  | _, .cons x _,  0   => some ⟨_, x⟩
  | _, .cons _ xs, i+1 => xs.nth i

def Row (s : WfSchema) : Type :=
  HList Field.cellType s.val.fields

def Table (s : WfSchema) : Type :=
  List (Row s)

inductive HasColList : SchemaFields → FieldName → Type where
  | here  {f : Field} {rest : SchemaFields} {n : FieldName}
      (eq : f.name = n) :
      HasColList (f :: rest) n
  | there {f : Field} {rest : SchemaFields} {n : FieldName}
      (h : HasColList rest n) :
      HasColList (f :: rest) n

def HasColList.toIndex {fs : SchemaFields} {n : FieldName} :
    HasColList fs n → Nat
  | .here _  => 0
  | .there h => h.toIndex + 1

/-- Recover the field that the witness points to. -/
def HasColList.field {fs : SchemaFields} {n : FieldName} :
    HasColList fs n → Field
  | @HasColList.here f _ _ _ => f
  | .there h => HasColList.field h

def HasColList.type {fs : SchemaFields} {n : FieldName}
    (h : HasColList fs n) : FieldType :=
  (HasColList.field h).type

def HasColList.get {fs : SchemaFields} {n : FieldName}
    (r : HList Field.cellType fs) (h : HasColList fs n) :
    Field.cellType h.field :=
  match h, r with
  | @HasColList.here f .., .cons x _  => x
  | @HasColList.there f rest _ h', .cons _ xs => HasColList.get xs h'

/-- Lift to a well-formed schema. -/
def HasCol (s : WfSchema) (n : FieldName) : Type :=
  HasColList s.val.fields n

def HasCol.type {s : WfSchema} {n : FieldName} (h : HasCol s n) : FieldType :=
  HasColList.type h

def HasCol.toIndex {s : WfSchema} {n : FieldName} (h : HasCol s n) : Nat :=
  HasColList.toIndex h

def List.findHasCol? (fs : SchemaFields) (n : FieldName) :
    Option (HasColList fs n) :=
  match fs with
  | [] => none
  | f :: rest =>
      if h : f.name = n then
        some (.here h)
      else
        (findHasCol? rest n).map .there

def WfSchema.findHasCol? (s : WfSchema) (n : FieldName) :
    Option (HasCol s n) :=
  List.findHasCol? s.val.fields n

def Row.get {s : WfSchema} {n : FieldName}
    (r : Row s) (h : HasCol s n) : Field.cellType (HasColList.field h) :=
  HasColList.get r h

def pid : Field := {
  name := "id",
  type := .integer,
  constraints := {
    required := true
  }
}
def name : Field := {
  name := "name",
  type := .string
  constraints := {
    minLength := some 1
    maxLength := some 10
    pattern := some ".*"
    enum := ["alice", "tom", "billy"]
  }
}
def age : Field := {
  name := "age",
  type := .number
  constraints := {
    required := false
    minimum := some 0
    maximum := some 150
  }
}

def people : WfSchema :=
  Schema.mkWf {
    fields := [
      pid, name, age
    ]
  }

def age30 : age.refinedType :=
  ⟨1.50, by decide⟩

def nameAlice : name.refinedType :=
  ⟨"alice", by decide⟩

-- #check (30 : Float)
-- --
def alice : Row people :=
  .cons ⟨1, by decide⟩ <|
  .cons (some ⟨"alice", by decide⟩) <|
  .cons (some ⟨30, by decide⟩) <|
  .nil

def tom : Row people :=
  .cons ⟨1, by decide⟩ <|
  .cons (some ⟨"tom", by decide⟩) <|
  .cons (some ⟨14, by decide⟩) .nil

def billy : Row people :=
  .cons ⟨2, by decide⟩ <|
  .cons (some ⟨"billy", by decide⟩) <|
  .cons none .nil

def peopleTable : Table people :=
  [ alice
  , tom
  , billy ]
--
-- --
-- #eval! (people.findHasCol? "id").map (·.toIndex)    -- some 0
-- #eval! (people.findHasCol? "name").map (·.toIndex)  -- some 1
-- #eval! (people.findHasCol? "age").map (·.toIndex)   -- some 2
-- #eval! (people.findHasCol? "nope").map (·.toIndex)  -- none
