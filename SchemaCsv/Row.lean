module

public import SchemaCsv.HList
public import SchemaCsv.Schema

public section

namespace SchemaCsv

@[expose]
def Row (s : WellFormedSchema) : Type :=
  HList Field.cellType s.val.fields

def Table (s : WellFormedSchema) : Type :=
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

end SchemaCsv
