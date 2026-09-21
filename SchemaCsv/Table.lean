module

public import SchemaCsv.Table.Basic
public import SchemaCsv.Table.PrimaryKey
public import Mathlib.Data.List.Nodup

public section

namespace SchemaCsv

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

