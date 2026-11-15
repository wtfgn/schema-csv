module

/-!
# Diagnostics

The data types for reporting a failure. Rendering, grouping, and location
plumbing arrive in M3; this module only fixes the vocabulary so that `validate`
can return something useful instead of a bare `Bool`.

Nothing here computes anything — it is data.
-/

public section

namespace SchemaCsv

/-- Where a failure happened. `line` is 1-based; `column` is the field name. -/
structure Loc where
  file : String := ""
  line : Nat := 0
  column : Option String := none
  deriving Repr, DecidableEq, Inhabited

/-- Why a value or table was rejected.

Deliberately coarse in v0.1: casting (M3) is what distinguishes "not a number"
from "in the enumeration but below the minimum". Until then every cell-level
failure is `invalidValue` with a human-readable `detail`. -/
inductive Code where
  /-- The schema itself is not well-formed. -/
  | schemaInvalid
  /-- A row has the wrong number of fields. -/
  | fieldCount
  /-- A cell does not satisfy its column. -/
  | invalidValue
  /-- Two rows share a primary key. -/
  | duplicateKey
  deriving Repr, DecidableEq, Inhabited

namespace Code

def label : Code → String
  | .schemaInvalid => "invalid schema"
  | .fieldCount => "field count"
  | .invalidValue => "invalid value"
  | .duplicateKey => "duplicate key"

instance : ToString Code := ⟨Code.label⟩

end Code

structure Diagnostic where
  loc : Loc := {}
  code : Code
  detail : String := ""
  deriving Repr, DecidableEq, Inhabited

/-- The result of a validation step: a value, or the diagnostics that forbid it. -/
abbrev Result (α : Type) := Except (List Diagnostic) α

namespace Result

/-- Did this result succeed? -/
def isOk : Result α → Bool
  | .ok _ => true
  | .error _ => false

/-- The diagnostics of a failed result; empty when it succeeded. -/
def diags : Result α → List Diagnostic
  | .ok _ => []
  | .error ds => ds

end Result

end SchemaCsv
