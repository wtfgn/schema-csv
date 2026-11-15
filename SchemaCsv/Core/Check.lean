module

public import SchemaCsv.Core.Report
public import SchemaCsv.Core.Satisfies

/-!
# The validator

`validate` decides `Satisfies` and, when it says no, explains why. The claims
that matter are proved at the bottom of this file:

* `validate_sound`    — if it accepts, the table really satisfies the schema;
* `validate_complete` — if the table satisfies the schema, it accepts;
* `validate_iff`      — therefore acceptance *is* satisfaction.

What is **not** proved: that the diagnostics it prints are accurate or complete.
Accept/reject is verified; the messages are covered by golden tests in
`Tests/Check.lean`. That is a deliberate split — see `docs/SEMANTICS.md` §12.
-/

public section

namespace SchemaCsv

/-! ## Cells -/

/-- One cell against one column. `none` when the column accepts the value. -/
@[expose]
def checkCell (c : Column) (v : Val) : Option Diagnostic :=
  if c.acceptsB v then
    none
  else
    some { code := .invalidValue, detail := s!"expected {c.ty}, got \"{v.render}\"" }

theorem checkCell_none_iff (c : Column) (v : Val) :
    checkCell c v = none ↔ c.acceptsB v = true := by
  by_cases h : c.acceptsB v = true <;> simp [checkCell, h]

/-- Every cell of a row against its column, walking both lists together.
A width mismatch yields exactly one diagnostic. -/
@[expose]
def validateCells : List Column → Row → List Diagnostic
  | [], [] => []
  | c :: cs, v :: vs =>
      match checkCell c v with
      | none => validateCells cs vs
      | some d => d :: validateCells cs vs
  | [], _ :: _ => [{ code := .fieldCount, detail := "too many fields" }]
  | _ :: _, [] => [{ code := .fieldCount, detail := "too few fields" }]

theorem validateCells_nil_iff (cs : List Column) (r : Row) :
    validateCells cs r = [] ↔ rowAcceptsAux cs r = true := by
  induction cs generalizing r with
  | nil => cases r <;> simp [validateCells, rowAcceptsAux]
  | cons c cs ih =>
      cases r with
      | nil => simp [validateCells, rowAcceptsAux]
      | cons v vs =>
          have h := ih vs
          cases hb : c.acceptsB v <;>
            simp [validateCells, rowAcceptsAux, checkCell, hb, h]

/-! ## Rows -/

/-- Turn a diagnostic list into a result. -/
@[expose]
def finish (ds : List Diagnostic) : Result Unit :=
  if ds.isEmpty then .ok () else .error ds

theorem finish_ok_iff (ds : List Diagnostic) : finish ds = .ok () ↔ ds = [] := by
  cases ds with
  | nil => simp [finish]
  | cons d ds => simp [finish]

/-- One row. -/
@[expose]
def validateRow (s : Schema) (r : Row) : Result Unit :=
  finish (validateCells s.fields r)

theorem validateRow_ok_iff (s : Schema) (r : Row) :
    validateRow s r = .ok () ↔ rowAccepts s r := by
  unfold validateRow rowAccepts
  rw [finish_ok_iff, validateCells_nil_iff]

/-- Diagnostics from every row, in order.

Deliberately *collects* rather than short-circuits: a rejected file should list
every bad row, not only the first. -/
@[expose]
def collectRowDiagnostics (s : Schema) : List Row → List Diagnostic
  | [] => []
  | r :: rs => validateCells s.fields r ++ collectRowDiagnostics s rs

theorem collectRowDiagnostics_nil_iff (s : Schema) (rs : List Row) :
    collectRowDiagnostics s rs = [] ↔ ∀ r ∈ rs, rowAccepts s r := by
  induction rs with
  | nil => simp [collectRowDiagnostics]
  | cons r rs ih =>
      have h : validateCells s.fields r = [] ↔ rowAccepts s r :=
        validateCells_nil_iff s.fields r
      simp [collectRowDiagnostics, h, ih]

/-! ## Table constraints -/

/-- Diagnostics for the table-level constraints. v0.1 reports one summary
diagnostic; naming the offending rows is M3 work. -/
@[expose]
def constraintDiagnostics (s : Schema) (t : Table) : List Diagnostic :=
  if tableConstraintsB s t = true then
    []
  else
    [{ code := .duplicateKey, detail := "violates unique constraint or primary key" }]

theorem constraintDiagnostics_nil_iff (s : Schema) (t : Table) :
    constraintDiagnostics s t = [] ↔ uniqueOK s t ∧ primaryKeyOK s t := by
  unfold constraintDiagnostics
  split
  · next h => exact ⟨fun _ => (tableConstraintsB_iff s t).mp h, fun _ => rfl⟩
  · next h =>
      have hc : ¬ (uniqueOK s t ∧ primaryKeyOK s t) :=
        fun hcon => h ((tableConstraintsB_iff s t).mpr hcon)
      exact ⟨fun hnil => absurd hnil (by simp), fun hcon => absurd hcon hc⟩

/-! ## The validator -/

/-- Validate a table against a schema, collecting diagnostics. -/
@[expose]
def validate (s : Schema) (t : Table) : Result Unit :=
  if s.WellFormed then
    finish (collectRowDiagnostics s t ++ constraintDiagnostics s t)
  else
    .error [{ code := .schemaInvalid, detail := "schema is not well-formed" }]

theorem append_nil_iff (a b : List Diagnostic) : a ++ b = [] ↔ a = [] ∧ b = [] := by
  cases a <;> simp

theorem validate_iff (s : Schema) (t : Table) :
    validate s t = .ok () ↔ Satisfies s t := by
  unfold validate
  split
  · next hwf =>
      rw [finish_ok_iff, append_nil_iff, collectRowDiagnostics_nil_iff,
          constraintDiagnostics_nil_iff]
      exact ⟨fun h => ⟨hwf, h⟩, fun h => h.2⟩
  · next hwf =>
      exact ⟨fun h => absurd h (by simp), fun h => absurd h.1 hwf⟩

theorem validate_sound (s : Schema) (t : Table) :
    validate s t = .ok () → Satisfies s t :=
  (validate_iff s t).mp

theorem validate_complete (s : Schema) (t : Table) :
    Satisfies s t → validate s t = .ok () :=
  (validate_iff s t).mpr

end SchemaCsv
