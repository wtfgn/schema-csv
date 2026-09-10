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
  deriving Repr, BEq, DecidableEq

abbrev FieldType.asType : FieldType → Type
  | .string => String
  | .integer => Int
  | .number => Float
  | .boolean => Bool

end SchemaCsv





-- def pid : Field := {
--   name := "id",
--   type := .integer,
--   constraints := {
--     required := true
--   }
-- }
-- def name : Field := {
--   name := "name",
--   type := .string
--   constraints := {
--     minLength := some 1
--     maxLength := some 10
--     pattern := some ".*"
--     enum := ["alice", "tom", "billy"]
--   }
-- }
-- def age : Field := {
--   name := "age",
--   type := .number
--   constraints := {
--     required := false
--     minimum := some 0
--     maximum := some 150
--   }
-- }

-- def people : WfSchema :=
--   Schema.mkWf {
--     fields := [
--       pid, name, age
--     ]
--   }

-- def age30 : age.refinedType :=
--   ⟨1.50, by decide⟩

-- def nameAlice : name.refinedType :=
--   ⟨"alice", by decide⟩

-- -- #check (30 : Float)
-- -- --
-- def alice : Row people :=
--   .cons ⟨1, by decide⟩ <|
--   .cons (some ⟨"alice", by decide⟩) <|
--   .cons (some ⟨30, by decide⟩) <|
--   .nil

-- def tom : Row people :=
--   .cons ⟨1, by decide⟩ <|
--   .cons (some ⟨"tom", by decide⟩) <|
--   .cons (some ⟨14, by decide⟩) .nil

-- def billy : Row people :=
--   .cons ⟨2, by decide⟩ <|
--   .cons (some ⟨"billy", by decide⟩) <|
--   .cons none .nil

-- def peopleTable : Table people :=
--   [ alice
--   , tom
--   , billy ]
--
-- --
-- #eval! (people.findHasCol? "id").map (·.toIndex)    -- some 0
-- #eval! (people.findHasCol? "name").map (·.toIndex)  -- some 1
-- #eval! (people.findHasCol? "age").map (·.toIndex)   -- some 2
-- #eval! (people.findHasCol? "nope").map (·.toIndex)  -- none
