module

public import SchemaCsv.Basic

public section

namespace SchemaCsv

/-- Constraints that apply to ALL field types -/
structure CommonConstraints (t : FieldType)  where
  required : Bool := false
  unique   : Bool := false -- This is just a declaration, not related to implementation directled
  enum     : Option (List t.asType) := none

structure CollectionConstraints where
  maxLength : Option Nat := none
  minLength : Option Nat := none

structure StringConstraints (t : FieldType) extends CommonConstraints t, CollectionConstraints where
  -- TODO: This constraint is sepcific to string
  -- This represents reguralr expression that can be used to test field values
  -- Maybe a Lean regex parser is needed
  pattern   : Option String := none

structure IntegerConstraints (t : FieldType) extends CommonConstraints t where
  minimum : Option Int := none
  maximum : Option Int := none

structure NumberConstraints (t : FieldType) extends CommonConstraints t where
  minimum : Option Float := none
  maximum : Option Float := none

structure BooleanConstraints (t : FieldType) extends CommonConstraints t where

/-- Constraints that make sense for a given field type. -/
@[expose]
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

@[expose]
def optLower {α : Type u} [LE α] (bound : Option α) (n : α) : Prop :=
  match bound with
  | none => True
  | some lo => lo ≤ n

@[expose]
def optUpper {α : Type u} [LE α] (bound : Option α) (n : α) : Prop :=
  match bound with
  | none => True
  | some hi => n ≤ hi

@[expose]
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

end SchemaCsv
