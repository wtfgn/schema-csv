# SchemaCsv

A **Lean 4** library for **schema-aware tabular data**, inspired by [Frictionless Table Schema](https://specs.frictionlessdata.io/table-schema/).

Plain CSV has no reliable types or contracts: parsers guess, nulls are ambiguous, and constraints are informal. SchemaCsv models tables so that **field types, nullability, bounds, enums, uniqueness, and primary keys** are part of the formal structure—enforced by Lean’s type system where practical, and by decidable checks where constraints span whole tables.

---

## Motivation

| Problem with plain CSV | Approach in SchemaCsv |
|------------------------|------------------------|
| No types | `FieldType` + dependent cell types |
| Silent null / missing values | Logical `Option` cells; `missingValues` for physical→logical cast |
| No schema contract | `WellFormedSchema` subtype |
| Constraints only in docs | Type-indexed constraints + refined subtypes |
| Keys are informal | Table-level `unique` / primary key checks (+ optional total PK projection) |


---

## Features

### Schema layer
- **`FieldName`**, **`FieldType`** (`string` | `integer` | `number` | `boolean`)
- **Type-indexed formats** (`FormatOf`) and **constraints** (`ConstraintsOf`)
  - Shared: `required`, `unique`, `enum`
  - String: `minLength`, `maxLength` (pattern reserved)
  - Integer / number: `minimum`, `maximum`
- **`Schema`**: fields, `missingValues`, `primaryKey`, …
- **`WellFormedSchema`**: unique non-empty names; PK ⊆ fields; PK fields required

### Cell / row layer
- **`refinedType`**: values refined by bounds / length / enum (subtypes)
- **`cellType`**: `refinedType` if `required`, else `Option refinedType`
- **`Row`**: heterogeneous list of cells indexed by the schema’s fields
- **`HasCol`**: proof-relevant column membership (`here` / `there`)
- Total **`Row.get`** given a `HasCol` witness

### Table constraints
- Per-column **`unique`** (`columnValues` + `Nodup`)
- **Primary key**: composite uniqueness over required key columns
- **`WellFormedTable`**: `uniqueOK ∧ primaryKeyOK`

### Design principles
- Physical strings vs logical cells kept distinct
- Field-level constraints → types; table-level constraints → predicates / subtypes
- Decidable checks for concrete data (`decide` / `native_decide`)

---

## Project layout

```text
SchemaCsv/
├── Basic.lean          -- FieldName, FieldType, asType
├── Constraints.lean    -- ConstraintsOf, optLower / optUpper / optEnum
├── Format.lean         -- FormatOf (string/integer/number/boolean)
├── Field.lean          -- Field, refinedType, cellType
├── Schema.lean         -- Schema, WellFormed, WellFormedSchema
├── HList.lean          -- Generic heterogeneous lists
├── Table.lean          -- Row, Table, HasCol, unique / PK, WellFormedTable
└── Example.lean        -- Sample schema and rows (optional)
```

---

## Quick example

```lean
import SchemaCsv

open SchemaCsv

def pid : Field := {
  name := "id", type := .integer
  constraints := { required := true, unique := true, enum := some [1, 2, 3] }
}

def name : Field := {
  name := "name", type := .string
  constraints := {
    required := true
    minLength := some 1
    maxLength := some 10
    enum := some ["alice", "tom", "billy"]
  }
}

def age : Field := {
  name := "age", type := .number
  constraints := { minimum := some 0, maximum := some 150 }
}

def people : WellFormedSchema :=
  Schema.mkWf {
    fields := [pid, name, age]
    primaryKey := [pid.name]
  }

def alice : Row people :=
  .cons ⟨1, by decide⟩ <|
  .cons ⟨"alice", by decide⟩ <|
  .cons (some ⟨30, by decide⟩) <|
  .nil

def peopleTable : WellFormedTable people :=
  Table.mkWf [alice]
```

Out-of-range ages, empty required names, or duplicate primary keys fail either at **type checking** (`decide` on refinements) or when building a **`WellFormedTable`**.

---

## Building

Requires a Lean 4 toolchain compatible with your Mathlib pin (for `List.Nodup`, etc.).

```bash
lake build
```

Example / test modules:

```bash
lake env lean SchemaCsv/Example.lean
```

---

## Status

| Area | Status |
|------|--------|
| Core types & refined cells | Implemented |
| Well-formed schemas | Implemented |
| HasCol + row access | Implemented |
| Unique + primary key (table-level) | Implemented |
| Physical cast (`missingValues`, parse) | Planned |
| Format-driven validation (email, uri, …) | Partial (types only) |
| Pattern constraints | Deferred |
| Foreign keys | Placeholder |
| JSON Table Schema import/export | Planned |

