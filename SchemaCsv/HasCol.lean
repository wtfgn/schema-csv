module

public import SchemaCsv.HList
public import SchemaCsv.Schema

public section

namespace SchemaCsv

inductive HasColList : SchemaFields → FieldName → Type where
  | here  {f : Field} {rest : SchemaFields} {n : FieldName}
      (eq : f.name = n) :
      HasColList (f :: rest) n
  | there {f : Field} {rest : SchemaFields} {n : FieldName}
      (h : HasColList rest n) :
      HasColList (f :: rest) n

def HasColList.toIndex {fs : SchemaFields} {n : FieldName} :
    HasColList fs n → Nat
  | .here _  => 0
  | .there h => h.toIndex + 1

/-- Recover the field that the witness points to. -/
def HasColList.field {fs : SchemaFields} {n : FieldName} :
    HasColList fs n → Field
  | @HasColList.here f _ _ _ => f
  | .there h => HasColList.field h

def HasColList.type {fs : SchemaFields} {n : FieldName}
    (h : HasColList fs n) : FieldType :=
  (HasColList.field h).type

def HasColList.get {fs : SchemaFields} {n : FieldName}
    (r : HList Field.cellType fs) (h : HasColList fs n) :
    Field.cellType h.field :=
  match h, r with
  | @HasColList.here f .., .cons x _  => x
  | @HasColList.there f rest _ h', .cons _ xs => HasColList.get xs h'

/-- Lift to a well-formed schema. -/
abbrev HasCol (s : WellFormedSchema) (n : FieldName) : Type :=
  HasColList s.val.fields n

abbrev HasCol.type {s : WellFormedSchema} {n : FieldName} (h : HasCol s n) : FieldType :=
  HasColList.type h

abbrev HasCol.toIndex {s : WellFormedSchema} {n : FieldName} (h : HasCol s n) : Nat :=
  HasColList.toIndex h

def List.hasCol? (fs : SchemaFields) (n : FieldName) :
    Option (HasColList fs n) :=
  match fs with
  | [] => none
  | f :: rest =>
      if h : f.name = n then
        some (.here h)
      else
        (hasCol? rest n).map .there

def WellFormedSchema.hasCol? (s : WellFormedSchema) (n : FieldName) :
    Option (HasCol s n) :=
  List.hasCol? s.val.fields n

/-- Name membership in the field list. -/
theorem List.hasCol?_isSome_of_memName
    {fs : SchemaFields} {n : FieldName}
    (h : n ∈ fs.map (·.name)) :
    (List.hasCol? fs n).isSome := by
  induction fs with
  | nil =>
      -- h : n ∈ []  is impossible
      contradiction
  | cons f rest ih =>
      -- h : n ∈ (f.name :: rest.map name)
      simp [List.hasCol?]
      by_cases heq : f.name = n
      · -- found at head
        simp [heq]
      · -- n must be in the tail names
        have htail : n ∈ rest.map (·.name) := by
          rw [List.map_cons, List.mem_cons] at h
          cases h with
          | inl hl => exact (heq hl.symm).elim
          | inr hr => exact hr
        -- ih gives (findHasCol? rest n).isSome
        have : (hasCol? rest n).isSome := ih htail
        cases hfind : List.hasCol? rest n with
        | none =>
            simp [hfind] at this
        | some w =>
            simp [heq]

/-- If a field name is in the schema, then `findHasCol?` returns a witness. -/
theorem WellFormedSchema.hasCol?_isSome_of_mem
    {s : WellFormedSchema} {n : FieldName}
    (h : n ∈ s.val.fieldNames) :
    (s.hasCol? n).isSome := by
  exact List.hasCol?_isSome_of_memName h

theorem HasColList.field_name
    {fs n} (h : HasColList fs n) :
    h.field.name = n := by
  induction h with
  | here eq => exact eq
  | there _ ih => exact ih

theorem HasColList.field_mem
    {fs : SchemaFields} {n : FieldName}
    (h : HasColList fs n) :
    h.field ∈ fs := by
  induction h with
  | here h =>
      exact List.mem_cons_self
  | there h ih =>
      exact List.mem_cons_of_mem _ ih

/-- If a field name is in the schema, then `findHasCol?` returns a witness. -/
def WellFormedSchema.hasCol
    {s : WellFormedSchema} {n : FieldName}
    (hin : n ∈ s.val.fieldNames) : HasCol s n :=
  (s.hasCol? n).get
    (WellFormedSchema.hasCol?_isSome_of_mem hin)

