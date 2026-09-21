module

public import SchemaCsv.HasCol
public import SchemaCsv.Table.Basic
import SchemaCsv.Schema

public section

namespace SchemaCsv

theorem HasCol.required_of_primaryKey
    {s : WellFormedSchema} {n : FieldName}
    (hn : n ∈ s.val.primaryKey) (h : HasCol s n) :
    (HasColList.field h).required = true := by
  -- 1. From WellFormed: some required field named n
  obtain ⟨f, hfMem, hname, hreq⟩ :
      ∃ f ∈ s.val.fields, f.name = n ∧ f.required = true := by
    exact WellFormedSchema.primaryKey_required hn
  -- 2. The HasCol witness points at a field in the list named n
  have hMem : h.field ∈ s.val.fields :=
    HasColList.field_mem h
  have hName : h.field.name = n :=
    HasColList.field_name h
  -- 3. Same name + both ∈ fields + Nodup names ⇒ same field
  have hNodup : s.val.fieldNames.Nodup := by
    rcases s.property with ⟨hNodup, _⟩
    exact hNodup
  have hEq : h.field = f :=
    Schema.field_eq_of_name_eq hNodup hMem hfMem
      (hName.trans hname.symm)
  -- 4. Transfer required
  rw [hEq]
  exact hreq

def Row.pkCell {s : WellFormedSchema}
    (r : Row s) (n : FieldName) (hn : n ∈ s.val.primaryKey) :
    (f : Field) × f.refinedType :=
  have hin : n ∈ s.val.fieldNames :=
    WellFormedSchema.primaryKey_subset_fieldNames hn
  let h : HasCol s n := s.hasCol hin
  have hr : h.field.required = true :=
    HasCol.required_of_primaryKey hn h
  let cell : h.field.refinedType := by
    simpa [Field.cellType, hr] using r.get h
  ⟨h.field, cell⟩

def Row.primaryKeyProjection {s : WellFormedSchema} (r : Row s) :
    List ((f : Field) × f.refinedType) :=
  s.val.primaryKey.attach.map fun ⟨n, hn⟩ =>
    Row.pkCell r n hn

def Row.primaryKeyProjection? {s : WellFormedSchema} (r : Row s) :
    Option (List ((f : Field) × Field.refinedType f)) :=
  s.val.primaryKey.mapM fun n =>
    match s.hasCol? n with
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
    decide (t.map (Row.primaryKeyProjection (s := s))).Nodup

