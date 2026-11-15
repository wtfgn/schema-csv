/-
Behavioural tests for satisfaction and the validator.

Two kinds of check here:

* `#guard` — evaluates `validate` on concrete tables. These are golden tests of
  the *decisions* and of the *messages*.
* `example … := by decide` — the same facts stated as propositions about
  `Satisfies`, closing the loop between the checker and the contract.

`validate_iff` is the theorem that makes the two agree for *all* inputs; these
tests are what catch message-level regressions, which the theorem deliberately
does not cover.
-/
import SchemaCsv

open SchemaCsv

/-! ### The test schema -/

def chkId : Column := { name := "id", ty := .int, required := true, unique := true }

def chkName : Column :=
  { name := "name", ty := .str, required := true, minLength := some 1, maxLength := some 10 }

def people : Schema :=
  { name := some "people", fields := [chkId, chkName], primaryKey := ["id"] }

def alice : Row := [.int 1, .str "alice"]
def bob : Row := [.int 2, .str "bob"]

/-! ### Accepting -/

#guard Result.isOk (validate people [alice, bob])
#guard Result.isOk (validate people [])

example : Satisfies people [alice, bob] := by decide
example : Satisfies people [] := by decide

-- a validated table can be promoted to a certificate.
-- The acceptance proof comes through `validate_iff` rather than `decide` on the
-- `Except` value, because core provides no `DecidableEq (Except ε α)`.
theorem peopleValid : validate people [alice, bob] = .ok () :=
  (validate_iff people [alice, bob]).mpr (by decide)

def peopleCert : Certified people :=
  certifyOfValidate people [alice, bob] peopleValid

example : Satisfies people peopleCert.val := Certified.satisfies peopleCert

/-! ### Rejecting: cell-level -/

-- wrong type for the column
#guard !Result.isOk (validate people [[.int 1, .int 2]])
-- value fails `minLength`
#guard !Result.isOk (validate people [[.int 1, .str ""]])
-- null in a required column
#guard !Result.isOk (validate people [[.null, .str "alice"]])

example : ¬ Satisfies people [[.int 1, .int 2]] := by decide
example : ¬ Satisfies people [[.null, .str "alice"]] := by decide

/-! ### Rejecting: width -/

#guard !Result.isOk (validate people [[.int 1]])
#guard !Result.isOk (validate people [[.int 1, .str "alice", .int 9]])

example : ¬ Satisfies people [[.int 1]] := by decide

-- width errors are reported as `fieldCount`
#guard (Result.diags (validate people [[.int 1]])).map (·.code) == [.fieldCount]
#guard (Result.diags (validate people [[.int 1, .str "a", .int 9]])).map (·.code)
        == [.fieldCount]

/-! ### Rejecting: primary key -/

#guard !Result.isOk (validate people [alice, alice])
#guard Result.isOk (validate people [alice, bob])

example : ¬ Satisfies people [alice, alice] := by decide

#guard (Result.diags (validate people [alice, alice])).map (·.code) == [.duplicateKey]

-- the primary key projection is the key tuple, in field order
#guard keyOf people alice == [.int 1]
#guard keyOf people bob == [.int 2]

/-! ### Rejecting: the schema itself -/

def badSchema : Schema := { fields := [{ name := "a", ty := .int }, { name := "a", ty := .str }] }

#guard !Result.isOk (validate badSchema [])
#guard (Result.diags (validate badSchema [])).map (·.code) == [.schemaInvalid]
example : ¬ Satisfies badSchema [] := by decide

/-! ### Diagnostics are collected, not short-circuited -/

-- two bad rows produce two diagnostics
#guard (Result.diags (validate people [[.int 1], [.int 2]])).length == 2
-- a bad row and a duplicate key both surface
#guard (Result.diags (validate people [[.int 1], [.int 1], [.int 2]])).length >= 2

-- the message names the expected type and the offending value
#guard (Result.diags (validate people [[.int 1, .int 2]])).head?.map (·.detail)
        == some "expected string, got \"2\""

/-! ### Unique columns and nulls -/

def tagCol : Column := { name := "tag", ty := .int, unique := true }

def tags : Schema := { fields := [tagCol] }

-- nulls are distinct: two nulls do not collide
#guard Result.isOk (validate tags [[.null], [.null]])
-- real duplicates do collide
#guard !Result.isOk (validate tags [[.int 1], [.int 1]])

example : Satisfies tags [[.null], [.null]] := by decide
example : ¬ Satisfies tags [[.int 1], [.int 1]] := by decide

/-! ### Empty schema and empty table -/

example : Satisfies ({} : Schema) [] := by decide
#guard Result.isOk (validate ({} : Schema) [])
