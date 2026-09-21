module

public import SchemaCsv.Field

public section

namespace SchemaCsv

abbrev SchemaFields := List Field

structure Schema where
  fields : SchemaFields
  missingValues : List String := [""] -- default to be empty string
  primaryKey : List FieldName := []
  -- TODO: add foreign key support
  -- foreignKey : List ForeignKey := []
  deriving Repr, DecidableEq

abbrev Schema.types (s : Schema) : List FieldType :=
  s.fields.map (·.type)

abbrev Schema.fieldNames (s : Schema) : List FieldName :=
  s.fields.map (·.name)

def Schema.uniqueFields (s : Schema) : List Field :=
  s.fields.filter (fun f =>
    match f.type, f.constraints with
    | .string, c => c.unique
    | .integer, c => c.unique
    | .number, c => c.unique
    | .boolean, c => c.unique)

def Schema.fieldByName? (s : Schema) (n : FieldName) : Option Field :=
  s.fields.find? (fun f => f.name = n)

/-- A schema is well-formed when:
  - field names are unique
    - every field name is non-empty
    - PK combination is a subset of field names
    - PK fields are unique
    - PK fields are required
-/
abbrev Schema.WellFormed (s : Schema) : Prop :=
  (s.fieldNames.Nodup) ∧
  (∀ n ∈ s.fieldNames, n ≠ "") ∧
  (s.primaryKey ⊆ s.fieldNames) ∧
  (s.primaryKey.Nodup) ∧
  (∀ n ∈ s.primaryKey, ∃ f ∈ s.fields,
    f.name = n ∧ f.required = true)

instance (s : Schema) : Decidable (s.WellFormed) := by
  dsimp [Schema.WellFormed]
  infer_instance

@[expose]
def WellFormedSchema : Type :=
  { s : Schema // s.WellFormed }

def Schema.mkWf
    (s : Schema)
    (h : s.WellFormed := by decide)
    : WellFormedSchema :=
  ⟨s, h⟩

theorem WellFormedSchema.fieldNames_nodup
    {s : WellFormedSchema} :
    (s.val.fieldNames.Nodup) := by
  rcases s.property with
    ⟨hNodup, _, _, _, _⟩
  exact hNodup

theorem WellFormedSchema.fieldNames_nonempty
    {s : WellFormedSchema} {n : FieldName}
    (hn : n ∈ s.val.fieldNames) :
    n ≠ "" := by
  rcases s.property with
    ⟨_, hNonEmpty, _, _, _⟩
  exact hNonEmpty n hn

/-- From WellFormed: PK names are field names. -/
theorem WellFormedSchema.primaryKey_subset_fieldNames
    {s : WellFormedSchema} :
    (s.val.primaryKey ⊆ s.val.fieldNames) := by
  rcases s.property with
    ⟨_, _, hSubset, _, _⟩
  exact hSubset

theorem WellFormedSchema.primaryKey_nodup
    {s : WellFormedSchema} :
    (s.val.primaryKey.Nodup) := by
  rcases s.property with
    ⟨_, _, _, hPkNodup, _⟩
  exact hPkNodup

/-- From WellFormed: each PK field is required. -/
theorem WellFormedSchema.primaryKey_required
    {s : WellFormedSchema} {n : FieldName}
    (hn : n ∈ s.val.primaryKey) :
    ∃ f ∈ s.val.fields, f.name = n ∧ f.required = true := by
  rcases s.property with
    ⟨_, _, _, _, hPkReq⟩
  exact hPkReq n hn


theorem List.eq_of_mem_of_name_eq_of_nodup
    {α β} [DecidableEq β] (name : α → β)
    {l : List α} (hs : (l.map name).Nodup)
    {x y : α} (hx : x ∈ l) (hy : y ∈ l) (hne : name x = name y) :
    x = y := by
  induction l with
  | nil => trivial
  | cons a rest ih =>
      have ⟨hna, hsRest⟩ := List.nodup_cons.mp hs
      simp only [List.mem_cons] at hx hy
      cases hx with
      | inl hx =>
          subst hx
          cases hy with
          | inl hy => exact hy.symm
          | inr hy =>
              exact absurd (List.mem_map.mpr ⟨y, hy, hne.symm⟩) hna
      | inr hx =>
          cases hy with
          | inl hy =>
              subst hy
              exact absurd (List.mem_map.mpr ⟨x, hx, hne⟩) hna
          | inr hy =>
              exact ih hsRest hx hy

theorem Schema.field_eq_of_name_eq
    {s : Schema} (hs : s.fieldNames.Nodup)
    {f₁ f₂ : Field}
    (h₁ : f₁ ∈ s.fields) (h₂ : f₂ ∈ s.fields)
    (hne : f₁.name = f₂.name) :
    f₁ = f₂ := by
  dsimp [Schema.fieldNames] at hs
  exact List.eq_of_mem_of_name_eq_of_nodup (·.name) hs h₁ h₂ hne


end SchemaCsv
