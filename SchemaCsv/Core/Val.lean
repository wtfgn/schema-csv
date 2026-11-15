module

/-!
# Logical values and types

This is the bottom of the verified core: what a cell *is*, once a physical
string has been cast. Nothing here knows about CSV, files, or JSON.

The normative description of these definitions is `docs/SEMANTICS.md`.
-/

public section

namespace SchemaCsv

/-- The value types supported by v0.1. -/
inductive Ty where
  | str
  | int
  | num
  | bool
  deriving Repr, DecidableEq, BEq, Inhabited

namespace Ty

/-- Human-readable name, used in diagnostics. -/
def label : Ty → String
  | .str => "string"
  | .int => "integer"
  | .num => "number"
  | .bool => "boolean"

instance : ToString Ty := ⟨Ty.label⟩

/-- Types that carry an order, and may therefore have `minimum` / `maximum`. -/
def isNumeric : Ty → Bool
  | .int | .num => true
  | _ => false

end Ty

/-- A logical cell value.

`null` is a value, not an absence: it is what a *missing value* in the physical
data becomes. It inhabits every type, so type checking never has to special-case
it; whether a null is *acceptable* in a given column is decided by
`Column.accepts`. -/
inductive Val where
  | null
  | str (s : String)
  | int (i : Int)
  | num (q : Rat)
  | bool (b : Bool)
  deriving Repr, DecidableEq, BEq, Inhabited

namespace Val

def isNull : Val → Bool
  | .null => true
  | _ => false

/-- Executable form of the inhabitation relation. `null` inhabits every type. -/
@[expose]
def compatibleB (t : Ty) (v : Val) : Bool :=
  match v with
  | .null => true
  | .str _ => t == .str
  | .int _ => t == .int
  | .num _ => t == .num
  | .bool _ => t == .bool

/-- `v` inhabits type `t`. `null` inhabits every type.

Declared as an `abbrev` on purpose: the proposition *is* the checker returning
`true`, so it stays definitionally transparent and `Decidable` comes for free. -/
abbrev compatible (t : Ty) (v : Val) : Prop :=
  compatibleB t v = true

/-- `le a b` is the truth value of `a ≤ b` for two values of the same numeric
type, and `false` otherwise.

Comparisons other than `int`/`num` are unreachable from a loaded schema:
`Column.shapeOKB` rejects `minimum`/`maximum` on any other type. That matters
for constructivity: `String.compare` is defined in core through a classical
instance, so using it here would make the checker non-constructive for nothing. -/
def le : Val → Val → Bool
  | .int a, .int b => decide (a ≤ b)
  | .num a, .num b => decide (a ≤ b)
  | _, _ => false

/-- Canonical textual form of a value, i.e. what a cell looks like when written
back out as CSV.

v0.1 limitation: rationals render through `toString`, so a non-integral value
renders as `num/den` (`3/2`). Exact decimal rendering belongs to M3, together
with the cast/render round-trip theorem that constrains it. -/
def render : Val → String
  | .null => ""
  | .str s => s
  | .int i => toString i
  | .num q => toString q
  | .bool b => if b then "true" else "false"

theorem compatible_null (t : Ty) : compatible t .null := rfl

end Val

end SchemaCsv
