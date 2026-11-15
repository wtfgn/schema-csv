module

public import SchemaCsv.Core.Val

/-!
# Columns and their constraints

A column is a plain record. Type/constraint *agreement* is not enforced by the
structure; it is enforced by `Column.WellFormed`, which is decidable and can
report which part is wrong. That is deliberate: schemas arrive as text from
users, so the failure mode we need is "this schema is wrong, here is why", not
"this cannot be written down".

Every predicate here is an `abbrev` for "checker returns `true`", so it stays
definitionally transparent and `Decidable` needs no hand-written instance.
-/

public section

namespace SchemaCsv

/-- String formats reserved by the schema language.

Not implemented in v0.1: `Column.WellFormed` rejects any column that sets one,
so a format is *reported as unsupported* rather than silently ignored. M3 turns
these into real checks. -/
inductive Fmt where
  | email
  | uri
  | uuid
  | binary
  deriving Repr, DecidableEq, BEq, Inhabited

namespace Fmt

def label : Fmt → String
  | .email => "email"
  | .uri => "uri"
  | .uuid => "uuid"
  | .binary => "binary"

instance : ToString Fmt := ⟨Fmt.label⟩

end Fmt

structure Column where
  name : String
  ty : Ty
  required : Bool := false
  unique : Bool := false
  enum : Option (List Val) := none
  minimum : Option Val := none
  maximum : Option Val := none
  minLength : Option Nat := none
  maxLength : Option Nat := none
  format : Option Fmt := none
  pattern : Option String := none
  title : Option String := none
  description : Option String := none
  deriving Repr, DecidableEq

namespace Column

/-! ## Leaf checks -/

/-- Executable form: `v` lies within the bounds that are actually present. -/
@[expose]
def boundsB (lo hi : Option Val) (v : Val) : Bool :=
  (match lo with
    | none => true
    | some b => Val.le b v) &&
  (match hi with
    | none => true
    | some b => Val.le v b)

/-- `v` lies within the present bounds. -/
abbrev bounds (lo hi : Option Val) (v : Val) : Prop := boundsB lo hi v = true

/-- Executable form: the length constraints hold.

`minLength` / `maxLength` are only well-formed on strings; on any other value
they hold exactly when absent, which `shapeOKB` guarantees for a loaded schema. -/
@[expose]
def lengthsB (lo hi : Option Nat) (v : Val) : Bool :=
  match v with
  | .str s =>
      (match lo with
        | none => true
        | some n => decide (n ≤ s.length)) &&
      (match hi with
        | none => true
        | some n => decide (s.length ≤ n))
  | _ => lo.isNone && hi.isNone

/-- The length constraints hold. -/
abbrev lengths (lo hi : Option Nat) (v : Val) : Prop := lengthsB lo hi v = true

/-- Executable form: membership in the optional enumeration. -/
@[expose]
def memberB (e : Option (List Val)) (v : Val) : Bool :=
  match e with
  | none => true
  | some vs => vs.contains v

/-- The value is in the enumeration, if one is declared. -/
abbrev member (e : Option (List Val)) (v : Val) : Prop := memberB e v = true

/-! ## Well-formedness of a column -/

/-- Executable form: the enumeration is non-empty and holds only non-null values
of the column's type. -/
@[expose]
def enumOKB (ty : Ty) (e : Option (List Val)) : Bool :=
  match e with
  | none => true
  | some vs => !vs.isEmpty && vs.all (fun v => !v.isNull && Val.compatibleB ty v)

abbrev enumOK (ty : Ty) (e : Option (List Val)) : Prop := enumOKB ty e = true

/-- Executable form: only constraints that make sense for the column's type are
present. -/
@[expose]
def shapeOKB (ty : Ty) (mn mx : Option Val) (mnl mxl : Option Nat)
    (fmt : Option Fmt) : Bool :=
  match ty with
  | .str => mn.isNone && mx.isNone && fmt.isNone
  | .int | .num => mnl.isNone && mxl.isNone && fmt.isNone
  | .bool => mn.isNone && mx.isNone && mnl.isNone && mxl.isNone && fmt.isNone

abbrev shapeOK (ty : Ty) (mn mx : Option Val) (mnl mxl : Option Nat)
    (fmt : Option Fmt) : Prop :=
  shapeOKB ty mn mx mnl mxl fmt = true

/-- Executable form: `minimum ≤ maximum`, when both are present. -/
@[expose]
def boundsOrderedB (lo hi : Option Val) : Bool :=
  match lo, hi with
  | some a, some b => Val.le a b
  | _, _ => true

abbrev boundsOrdered (lo hi : Option Val) : Prop := boundsOrderedB lo hi = true

/-- Executable form: `minLength ≤ maxLength`, when both are present. -/
@[expose]
def lengthOrderedB (lo hi : Option Nat) : Bool :=
  match lo, hi with
  | some a, some b => decide (a ≤ b)
  | _, _ => true

abbrev lengthOrdered (lo hi : Option Nat) : Prop := lengthOrderedB lo hi = true

/-- Executable form of column well-formedness. -/
@[expose]
def wellFormedB (c : Column) : Bool :=
  !c.name.isEmpty &&
  enumOKB c.ty c.enum &&
  shapeOKB c.ty c.minimum c.maximum c.minLength c.maxLength c.format &&
  boundsOrderedB c.minimum c.maximum &&
  lengthOrderedB c.minLength c.maxLength &&
  c.pattern.isNone

/-- A column is well-formed when it has a name, its constraints are meaningful
for its type, its bounds are consistent, and the reserved-but-unimplemented
features are absent. -/
abbrev WellFormed (c : Column) : Prop := wellFormedB c = true

/-! ## Acceptance -/

/-- Executable form of value acceptance.

A null is accepted exactly when the column is not required. Every other value
must inhabit the column's type and satisfy the declared constraints. `unique` is
absent on purpose: it is a property of a column across all rows, not of one
cell, so it belongs to `Satisfies`. -/
@[expose]
def acceptsB (c : Column) (v : Val) : Bool :=
  match v with
  | .null => !c.required
  | _ =>
      Val.compatibleB c.ty v &&
      boundsB c.minimum c.maximum v &&
      lengthsB c.minLength c.maxLength v &&
      memberB c.enum v

/-- Does this column accept this value? -/
abbrev accepts (c : Column) (v : Val) : Prop := acceptsB c v = true

/-- A null is accepted exactly by the non-required columns. -/
theorem accepts_null_iff (c : Column) : c.accepts .null ↔ c.required = false := by
  show (!c.required = true) ↔ (c.required = false)
  cases hb : c.required with
  | false => constructor <;> intro _ <;> rfl
  | true => constructor <;> intro h <;> exact absurd h (by decide)

end Column

end SchemaCsv
