module

public import SchemaCsv.HList
public import SchemaCsv.Schema
public import SchemaCsv.HasCol
public import Mathlib.Data.List.Nodup

public section

namespace SchemaCsv

abbrev Row (s : WellFormedSchema) : Type :=
  HList Field.cellType s.val.fields

abbrev Table (s : WellFormedSchema) : Type :=
  List (Row s)

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

/-- Check if the uniqueness constraint of all specified columns are satisfied -/
def Table.uniqueOK {s : WellFormedSchema} (t : Table s) : Bool :=
  s.val.uniqueFields.all fun f =>
    match s.hasCol? f.name with
    | none => true -- column without constraint just passes
    | some h => t.columnUnique h

end SchemaCsv
