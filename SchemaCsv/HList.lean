module

public section

namespace SchemaCsv

inductive HList {α : Type v} (β : α → Type u) : List α → Type (max u v)
  | nil  : HList β []
  | cons {i is} : β i → HList β is → HList β (i :: is)

def HList.nth {α β} : {ts : List α} → HList β ts → Nat → Option ((t : α) × β t)
  | _, .nil,       _   => none
  | _, .cons x _,  0   => some ⟨_, x⟩
  | _, .cons _ xs, i+1 => xs.nth i

end SchemaCsv
