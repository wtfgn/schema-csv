module

public section

namespace SchemaCsv

structure FieldName where
  value : String
  deriving DecidableEq, Repr

namespace FieldName

def ofString (s : String) : FieldName := ⟨s⟩

instance : ToString FieldName where
  toString := FieldName.value

instance : Coe String FieldName where
  coe := FieldName.ofString

end FieldName

inductive FieldType where
  | string
  | integer
  | number
  | boolean
  deriving Repr, DecidableEq

abbrev FieldType.asType : FieldType → Type
  | .string => String
  | .integer => Int
  | .number => Float
  | .boolean => Bool

instance {t : FieldType} : Repr t.asType := by
  cases t <;> dsimp [FieldType.asType] <;> infer_instance

instance {t : FieldType} : DecidableEq t.asType := by
  cases t <;> dsimp [FieldType.asType] <;> infer_instance

end SchemaCsv
