module

public import SchemaCsv.Basic

public section

namespace SchemaCsv

inductive StringFormat where
  | default -- any valid string
  | email -- a valid email address
  | uri -- a valid URI
  | binary -- a based64-encoded string representing binary data
  | uuid -- a string that is a uuid
  deriving Repr, DecidableEq, Inhabited

inductive IntegerFormat where
  | default
  deriving Repr, DecidableEq, Inhabited

inductive NumberFormat where
  | default
  deriving Repr, DecidableEq, Inhabited

inductive BooleanFormat where
  | default
  deriving Repr, DecidableEq, Inhabited

-- inductive DateFormat where
--   | default
--   | any
--   | pattern (p : String)
--   deriving Repr, DecidableEq

@[expose]
def FormatOf (t : FieldType) : Type :=
  match t with
  | .string => StringFormat
  | .integer => IntegerFormat
  | .number => NumberFormat
  | .boolean => BooleanFormat

instance (t : FieldType) : Repr (FormatOf t) := by
  cases t <;> dsimp [FormatOf] <;> infer_instance

instance (t : FieldType) : DecidableEq (FormatOf t) := by
  cases t <;> dsimp [FormatOf] <;> infer_instance

instance (t : FieldType) : Inhabited (FormatOf t) := by
  cases t <;> dsimp [FormatOf] <;> infer_instance
