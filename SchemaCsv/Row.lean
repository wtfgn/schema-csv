module

public import SchemaCsv.HList
public import SchemaCsv.Schema

public section

namespace SchemaCsv

abbrev Row (s : WellFormedSchema) : Type :=
  HList Field.cellType s.val.fields

abbrev Table (s : WellFormedSchema) : Type :=
  List (Row s)

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
@[expose]
def HasCol (s : WellFormedSchema) (n : FieldName) : Type :=
  HasColList s.val.fields n

def HasCol.type {s : WellFormedSchema} {n : FieldName} (h : HasCol s n) : FieldType :=
  HasColList.type h

def HasCol.toIndex {s : WellFormedSchema} {n : FieldName} (h : HasCol s n) : Nat :=
  HasColList.toIndex h

def List.findHasCol? (fs : SchemaFields) (n : FieldName) :
    Option (HasColList fs n) :=
  match fs with
  | [] => none
  | f :: rest =>
      if h : f.name = n then
        some (.here h)
      else
        (findHasCol? rest n).map .there

def WellFormedSchema.findHasCol? (s : WellFormedSchema) (n : FieldName) :
    Option (HasCol s n) :=
  List.findHasCol? s.val.fields n

def Row.get {s : WellFormedSchema} {n : FieldName}
    (r : Row s) (h : HasCol s n) : Field.cellType (HasColList.field h) :=
  HasColList.get r h

def Table.columnCells {s : WellFormedSchema} (t : Table s) (h : HasCol s n) :
    List (Field.cellType h.field) :=
  t.map (fun r => r.get h)

/-- Get non-null values given a specific column -/
def Table.columnValues {s : WellFormedSchema} (t : Table s) (h : HasCol s n) :
    List h.field.refinedType := by
  by_cases hr : h.field.required
  · exact t.map fun r => by
      simpa [Field.cellType, hr] using (r.get h)
  · exact (t.map fun r => by
      simpa [Field.cellType, hr] using (r.get h)).filterMap id

/-- Check if a column contains only unique values -/
def Table.columnUnique {s : WellFormedSchema} (t : Table s) (h : HasCol s n) : Bool :=
  decide (t.columnValues h).Nodup

-- def Table.primaryKeyMatches {s : WellFormedSchema} (r₁ r₂ : Row s) : Bool :=
--   s.val.primaryKey.all fun n =>
--     match s.findHasCol? n with
--     | none => false
--     | some h => decide (r₁.get h = r₂.get h)

/-- Name membership in the field list. -/
theorem List.findHasCol?_isSome_of_memName
    (fs : SchemaFields) (n : FieldName)
    (h : n ∈ fs.map (·.name)) :
    (List.findHasCol? fs n).isSome := by
  induction fs with
  | nil =>
      -- h : n ∈ []  is impossible
      contradiction
  | cons f rest ih =>
      -- h : n ∈ (f.name :: rest.map name)
      simp [List.findHasCol?]
      by_cases heq : f.name = n
      · -- found at head
        simp [heq]
      · -- n must be in the tail names
        have htail : n ∈ rest.map (·.name) := by
          simp at h
          cases h with
          | inl hl => exact (heq hl.symm).elim
          | inr hr => simp [hr]
        -- ih gives (findHasCol? rest n).isSome
        have := ih htail
        cases hfind : List.findHasCol? rest n with
        | none =>
            simp [hfind] at this
        | some w =>
            simp [heq]

/-- If a field name is in the schema, then `findHasCol?` returns a witness. -/
theorem WellFormedSchema.findHasCol?_isSome_of_mem
    (s : WellFormedSchema) (n : FieldName)
    (h : n ∈ s.val.fieldNames) :
    (s.findHasCol? n).isSome := by
  exact List.findHasCol?_isSome_of_memName _ _ h

theorem absurd_find_none
    (s : WellFormedSchema) (n : FieldName)
    (hin : n ∈ s.val.fieldNames)
    (hnone : s.findHasCol? n = none) :
    False := by
  have := WellFormedSchema.findHasCol?_isSome_of_mem s n hin
  simp [hnone] at this

/-- From WellFormed: PK names are field names. -/
theorem WellFormedSchema.primaryKey_subset_fieldNames
    (s : WellFormedSchema) :
    (s.val.primaryKey ⊆ s.val.fieldNames) := by
  rcases s.property with
    ⟨_, _, hSubset, _, _⟩
  exact hSubset

/-- From WellFormed: each PK field is required. -/
theorem WellFormedSchema.primaryKey_required
    (s : WellFormedSchema) (n : FieldName) (hn : n ∈ s.val.primaryKey) :
    ∃ f ∈ s.val.fields, f.name = n ∧ f.required = true := by
  rcases s.property with ⟨_, _, _, _, hPkReq⟩
  exact hPkReq n hn

def Row.primaryKeyProjection? {s : WellFormedSchema} (r : Row s) :
    Option (List ((f : Field) × Field.refinedType f)) :=
  s.val.primaryKey.mapM fun n =>
    match s.findHasCol? n with
    | none   => none
    | some h =>
        -- PK fields are required ⇒ cellType = refinedType
        if hreq : h.field.required then
          let cell := by
            simpa [Field.cellType, hreq] using r.get h
          some ⟨h.field, cell⟩
        else
           none -- should never happened if schema is well-formed

def Table.primaryKeyOK {s : WellFormedSchema} (t : Table s) : Bool :=
  s.val.primaryKey.isEmpty ||
  let keys := t.filterMap (Row.primaryKeyProjection? (s := s))
  keys.length == t.length && decide keys.Nodup

/-- Check if the uniqueness constraint of all specified columns are satisfied -/
def Table.uniqueOK {s : WellFormedSchema} (t : Table s) : Bool :=
  s.val.uniqueFields.all fun f =>
    match s.findHasCol? f.name with
    | none => true -- column without constraint just passes
    | some h => t.columnUnique h 

abbrev Table.WellFormed {s : WellFormedSchema} (t : Table s) : Prop :=
  t.uniqueOK ∧
  t.primaryKeyOK
  

@[expose]
def WellFormedTable (s : WellFormedSchema) : Type :=
  { t : Table s // t.WellFormed }

def Table.mkWf {s : WellFormedSchema}
    (t : Table s)
    (h : t.WellFormed := by decide)
    : WellFormedTable s :=
  ⟨t, h⟩

end SchemaCsv
