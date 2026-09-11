import SchemaCsv

open SchemaCsv

def pid : Field := {
  name := "id",
  type := .integer,
  constraints := {
    required := true,
    enum := some [1, 2, 3]
  }
}
def name : Field := {
  name := "name",
  type := .string
  constraints := {
    minLength := some 1
    maxLength := some 10
    pattern := some ".*"
    enum := ["alice", "tom", "billy"]
  }
}
def age : Field := {
  name := "age",
  type := .number
  constraints := {
    required := false
    minimum := some 0
    maximum := some 150
  }
}

def people : WellFormedSchema :=
  Schema.mkWf
    { fields := [pid, name, age] }

def alice : Row people :=
  .cons ⟨1, by decide⟩ <|
  .cons (some ⟨"alice", by decide⟩) <|
  .cons (some ⟨30, by decide⟩) <|
  .nil

def tom : Row people :=
  .cons ⟨1, by decide⟩ <|
  .cons (some ⟨"tom", by decide⟩) <|
  .cons (some ⟨14, by decide⟩) .nil

def billy : Row people :=
  .cons ⟨2, by decide⟩ <|
  .cons (some ⟨"billy", by decide⟩) <|
  .cons none .nil

def peopleTable : Table people :=
  [ alice
  , tom
  , billy ]
