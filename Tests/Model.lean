/-
Hand-computed cases from `docs/SEMANTICS.md`.

These run at elaboration time: `#guard` *evaluates* the checkers, so a compile
error here is the real proof that the executable core computes. Every case in
SEMANTICS.md §7 appears below.
-/
import SchemaCsv

open SchemaCsv

/-! ### 1. Width subtyping and null -/

#guard Val.compatibleB .int (.int 3)
#guard Val.compatibleB .str (.str "x")
#guard Val.compatibleB .num (.num (1/2))
#guard Val.compatibleB .bool (.bool true)
#guard !Val.compatibleB .str (.int 3)
#guard !Val.compatibleB .bool (.str "true")
-- a null inhabits every type
#guard Val.compatibleB .int Val.null
#guard Val.compatibleB .bool Val.null

/-! ### 2. Ordering between values -/

#guard Val.le (.int 1) (.int 2)
#guard Val.le (.int 2) (.int 2)
#guard !Val.le (.int 3) (.int 2)
#guard Val.le (.num (1/2)) (.num (2/3))
#guard !Val.le (.num (2/3)) (.num (1/2))
-- incomparable pairs are not ordered (unreachable from a well-formed schema)
#guard !Val.le (.int 1) (.str "1")

/-! ### 3. Rendering -/

#guard Val.render Val.null == ""
#guard Val.render (.str "alice") == "alice"
#guard Val.render (.int (-7)) == "-7"
#guard Val.render (.bool true) == "true"
#guard Val.render (.num 30) == "30"

/-! ### 4. Bounds -/

#guard Column.boundsB (some (.int 0)) (some (.int 10)) (.int 5)
#guard Column.boundsB (some (.int 0)) (some (.int 10)) (.int 0)
#guard Column.boundsB (some (.int 0)) (some (.int 10)) (.int 10)
#guard !Column.boundsB (some (.int 0)) (some (.int 10)) (.int 11)
#guard !Column.boundsB (some (.int 0)) (some (.int 10)) (.int (-1))
-- absent bounds are unrestrictive
#guard Column.boundsB none none (.str "anything")

/-! ### 5. Length -/

#guard Column.lengthsB (some 2) (some 4) (.str "abc")
#guard !Column.lengthsB (some 2) (some 4) (.str "a")
#guard !Column.lengthsB (some 2) (some 4) (.str "abcde")
-- absent constraints are unrestrictive
#guard Column.lengthsB none none (.str "")
-- a non-string cannot satisfy a declared length (blocked by well-formedness)
#guard !Column.lengthsB (some 1) none (.int 5)

/-! ### 6. Enumeration -/

#guard Column.memberB none (.str "whatever")
#guard Column.memberB (some [.int 1, .int 2]) (.int 2)
#guard !Column.memberB (some [.int 1, .int 2]) (.int 3)

/-! ### 7. Column well-formedness -/

def ageCol : Column :=
  { name := "age", ty := .int, required := true,
    minimum := some (.int 0), maximum := some (.int 150) }

def nameCol : Column :=
  { name := "name", ty := .str, required := true,
    minLength := some 1, maxLength := some 10 }

#guard ageCol.wellFormedB
#guard nameCol.wellFormedB

-- a nameless column is not well-formed
#guard !({ name := "", ty := .int } : Column).wellFormedB
-- bounds on a string column are a schema error (not silently ignored)
#guard !({ name := "s", ty := .str, minimum := some (.int 0) } : Column).wellFormedB
-- length on an integer column is a schema error
#guard !({ name := "n", ty := .int, minLength := some 1 } : Column).wellFormedB
-- an empty enumeration is a schema error
#guard !({ name := "e", ty := .int, enum := some [] } : Column).wellFormedB
-- enumeration values must have the column's type
#guard !({ name := "e", ty := .int, enum := some [.str "x"] } : Column).wellFormedB
-- enumeration values must not be null
#guard !({ name := "e", ty := .int, enum := some [Val.null] } : Column).wellFormedB
-- min > max is a schema error
#guard !Column.boundsOrderedB (some (.int 5)) (some (.int 2))
#guard !Column.lengthOrderedB (some 5) (some 2)
-- `pattern` and `format` are reserved: reported, never silently ignored
#guard !({ name := "p", ty := .str, pattern := some "x" } : Column).wellFormedB
#guard !({ name := "f", ty := .str, format := some .email } : Column).wellFormedB

/-! ### 8. Acceptance -/

def requiredId : Column := { name := "id", ty := .int, required := true }
def optionalAge : Column :=
  { name := "age", ty := .int, minimum := some (.int 0), maximum := some (.int 150) }

-- a required column rejects a null ...
#guard !requiredId.acceptsB .null
-- ... and an optional one accepts it
#guard optionalAge.acceptsB .null
#guard requiredId.acceptsB (.int 7)
#guard !requiredId.acceptsB (.str "seven")
#guard optionalAge.acceptsB (.int 30)
#guard !optionalAge.acceptsB (.int 200)

-- the null rule is the theorem, not just a test
example (c : Column) : c.accepts .null ↔ c.required = false :=
  Column.accepts_null_iff c

/-! ### 9. Schemas -/

def idCol : Column := { name := "id", ty := .int, required := true, unique := true }

def peopleSchema : Schema :=
  { name := some "people", fields := [idCol, nameCol], primaryKey := ["id"] }

#guard Schema.fieldsOKB peopleSchema
#guard peopleSchema.fieldNames == ["id", "name"]
#guard (peopleSchema.fieldOf? "name").isSome
#guard !(peopleSchema.fieldOf? "nmae").isSome
#guard peopleSchema.isMissingValue ""
#guard !peopleSchema.isMissingValue "NA"
#guard ({ peopleSchema with missingValues := ["", "NA"] }).isMissingValue "NA"

example : peopleSchema.WellFormed := by decide

-- duplicate column names are not well-formed
def dupSchema : Schema :=
  { fields := [{ name := "a", ty := .int }, { name := "a", ty := .str }] }
example : ¬ dupSchema.WellFormed := by decide

-- a primary key over a column that is not required is not well-formed
def badPkSchema : Schema :=
  { fields := [{ name := "id", ty := .int }], primaryKey := ["id"] }
example : ¬ badPkSchema.WellFormed := by decide

-- a primary key naming a column that does not exist is not well-formed
def ghostPkSchema : Schema :=
  { fields := [idCol], primaryKey := ["ghost"] }
example : ¬ ghostPkSchema.WellFormed := by decide

-- a duplicated primary-key entry is not well-formed
def dupPkSchema : Schema :=
  { fields := [idCol], primaryKey := ["id", "id"] }
example : ¬ dupPkSchema.WellFormed := by decide

-- the empty schema is well-formed
example : ({} : Schema).WellFormed := by decide
