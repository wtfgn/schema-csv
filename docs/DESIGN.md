# SchemaCsv — design

> Status: **rewrite in progress (M0 of M8)**. This document describes the target
> v0.1 design and records the decisions behind it. Anything marked *pre-rewrite*
> is the old model and is scheduled for deletion; see [ROADMAP.md](ROADMAP.md).

## 1. What this is

A schema-aware tabular data tool whose checker is written in Lean 4 and whose
correctness claims are machine-checked.

**Goal (v0.1).** A newcomer writes a JSON schema next to a CSV and runs one
command; they get either `OK (n rows)` or `file:line: column: expected X, got "Y"`
diagnostics — and the checker that produced those answers is a Lean function
formally proved to accept exactly the files the written semantics accepts.

Two halves, both required:

* **Usability** — it runs on real files and explains failures.
* **Soundness** — a written contract exists, and the implementation is proved to
  match it.

**Non-goals for v0.1.** Regex `pattern` constraints, date/time types, foreign
keys, schema inference, `clean`/normalising output, streaming, bindings to other
languages, Arrow/Parquet, YAML parsing. Each is a documented later item, not a
gap to be improvised.

## 2. The problem being solved

Plain CSV is a great interchange format and a terrible data contract. The
specific failures this project targets, and the reason each one is a *design*
problem rather than a feature request:

| # | Problem | Why it is structural |
|---|---|---|
| RP1 | No schema is attached, so "the data is valid" is unprovable | Needs a written semantics before any checker can be judged |
| RP2 | Type/constraint information lives in prose, README tables, or brittle scripts | Needs schema-as-data with checked well-formedness |
| RP3 | Nothing can say "v2 of this schema still accepts all valid v1 data" | Needs schemas to be *values* that can be compared, not type formers |
| RP4 | Casting `String → typed value` is where corruption happens (leading zeros, `N/A`, `1,2e3`) | Needs an explicit physical→logical boundary with a defined cast rule per type |
| RP5 | Rejection without provenance is useless | Needs location-carrying diagnostics threaded through casting, designed in from the start |
| RP6 | Every tool in this space is either informal or heavyweight | Needs a small verified core plus a 200-line `IO` shell — no extraction boundary |
| RP7 | Documentation drifts from behaviour | Needs every documented statement backed by a test or a `#check` |

### Why a rewrite rather than a patch

The pre-rewrite tree encoded validity **in the type of each cell** (`Field.refinedType`,
`Field.cellType`, `HList` rows indexed by the field list, `HasCol` membership
witnesses). That has three consequences that cannot be patched away:

1. **There is no semantics to be sound against.** The types are downstream of a
   predicate that was never written. Any `Satisfies` added later would need a
   large proof about the encoding rather than about the data.
2. **The guarantee is unusable from executable code.** Every cell read goes
   through dependent elimination (`simpa [Field.cellType, hr]` at four sites), and
   nothing in the library can consume a `String`. A CSV reader would have to
   re-derive the guarantee anyway.
3. **Schema evolution becomes unstatable** (RP3). If constraints are baked into
   cell *types*, two schemas cannot be compared for relaxation, so the project's
   headline differentiator is foreclosed.

The rewrite inverts the encoding: **certify the table, not the cells.**

## 3. Architecture

### 3.1 Layers and trust boundary

```
┌───────────────────────────────────────────────────────────────┐
│  CLI  (`schema-csv check|info|infer`)          unverified I/O  │
│  arg parsing · file reading · exit codes · output format      │
├───────────────────────────────────────────────────────────────┤
│  Report: Diagnostic · Loc · Code · render · aggregation       │
├───────────────────────────────────────────────────────────────┤
│  Syntax: JSON ⇄ Schema   (Frictionless-compatible subset)     │
├───────────────────────────────────────────────────────────────┤
│  Csv: parseRecords (with line numbers) · renderRecords        │
├───────────────────────────────────────────────────────────────┤
│  ★ VERIFIED CORE ★                                            │
│  Cast:   castVal : Column → String → Result Val               │
│  Check:  validate : Schema → List Row → Result Unit           │
│  Spec:   Satisfies : Schema → List Row → Prop                 │
│  Proofs: sound · complete · cast_refines_spec                 │
│  Cert:   Certified := { t // Satisfies s t }                  │
└───────────────────────────────────────────────────────────────┘
   no Mathlib · no `sorry` · no `Classical` · no extraction boundary
```

The trust boundary sits at the very top. File I/O and argument parsing are the
only unverified parts, and both are trivial. **The tool *is* the verified core
plus an `IO` shell** — there is no Rust re-implementation to drift from the model.

### 3.2 Module tree (target)

```
SchemaCsv/            -- lean library, zero dependencies
  Core/
    Val.lean          -- Val, Ty, compatibility, comparison, rendering
    Column.lean       -- Column, Column.WellFormed, Column.accepts
    Schema.lean       -- Schema, Schema.WellFormed, field lookup
    Table.lean        -- Row := List Val, Table := List Row
    Satisfies.lean    -- rowAccepts, uniqueOK, primaryKeyOK, Satisfies
    Check.lean        -- validate + soundness/completeness proofs
    Cast.lean         -- castVal, castRow + cast_refines_spec
    Certified.lean    -- Certified, toSatisfies
  Csv/
    Parse.lean        -- CsvOpts, RawRecord, parseRecords + round-trip
  Syntax/
    Json.lean         -- Schema.toJson / ofJson + decode diagnostics
  Report.lean         -- Loc, Code, Diagnostic, render
  Cli.lean            -- argument parsing, subcommands, exit codes
  Main.lean           -- entry point
Tests/                -- `lake test`; every doc claim appears here
examples/             -- schemas + good/bad CSVs, shared by tests and docs
docs/                 -- DESIGN.md, ROADMAP.md, SEMANTICS.md;
                         SCHEMA.md lands at M4
```

**Layering rule (enforced in CI):** a module under `Core/` may import only from
`Core/`. That keeps the verified kernel isolated and reviewable in one sitting.

### 3.3 Core API

```lean
-- Core/Val.lean
inductive Ty | str | int | num | bool
inductive Val
  | null
  | str  (s : String)
  | int  (i : Int)
  | num  (q : Rat)      -- exact; not Float
  | bool (b : Bool)
  deriving Repr, DecidableEq, BEq, Inhabited

def Val.compatible : Ty → Val → Prop     -- `.null` is compatible with every Ty
def Val.le         : Val → Val → Bool    -- total; false when incomparable
def Val.render     : Val → String        -- canonical form

-- Core/Column.lean
structure Column where
  name        : String
  ty          : Ty
  required    : Bool := false
  unique      : Bool := false
  enum        : Option (List Val) := none
  minimum     : Option Val := none
  maximum     : Option Val := none
  minLength   : Option Nat := none
  maxLength   : Option Nat := none
  format      : Option Fmt := none        -- email | uri | uuid | binary
  pattern     : Option String := none     -- reserved; rejected in v0.1
  title       : Option String := none
  description : Option String := none

def Column.WellFormed : Column → Prop
def Column.accepts  : Column → Val → Prop

-- Core/Schema.lean
structure Schema where
  name          : Option String := none
  version       : Option String := none
  fields        : List Column
  missingValues : List String := [""]
  primaryKey    : List String := []
  trueValues    : List String := ["true", "True", "TRUE"]
  falseValues   : List String := ["false", "False", "FALSE"]

def Schema.WellFormed : Schema → Prop
def Schema.fieldOf?  : Schema → String → Option Column

-- Core/Satisfies.lean  (the contract)
def rowAccepts   (s : Schema) (r : Row) : Prop
def uniqueOK     (s : Schema) (t : Table) : Prop
def primaryKeyOK (s : Schema) (t : Table) : Prop
def Satisfies    (s : Schema) (t : Table) : Prop :=
  s.WellFormed ∧ (∀ r ∈ t, s.rowAccepts r) ∧ s.uniqueOK t ∧ s.primaryKeyOK t

-- Core/Check.lean  (the deliverable, and its proof)
def validate (s : Schema) (t : Table) : Result Unit
theorem validate_sound    : validate s t = .ok () → Satisfies s t
theorem validate_complete : Satisfies s t → validate s t = .ok ()
theorem validate_iff      : validate s t = .ok () ↔ Satisfies s t

-- Core/Cast.lean  (the physical boundary)
def castVal (s : Schema) (c : Column) (raw : String) : Result Val
def castRow (s : Schema) (r : List String) : Result Row
theorem castVal_spec : castVal s c raw = .ok v → c.accepts v
```

### 3.4 Pipeline

```
bytes ──IO.FS──▶ String
  ──parseRecords──▶ List RawRecord            (fields + start line)
  ──castRow──────▶ List Row                   (+ Diagnostics: line, column name)
  ──validate─────▶ ok | Diagnostics
```

`castRow` and `validate` are kept separate on purpose:

* `castRow` owns **lexical** failure (not an integer, not in enum, missing
  required value) and can attach a line and a column name.
* `validate` owns **structural** failure (field count, `unique`, primary key).
* `Satisfies` is stated on `List Row` only, so the contract never mentions
  strings. That is what makes the soundness theorem tractable.

## 4. Decision log

| ID | Decision | Rationale | Rejected alternative |
|---|---|---|---|
| **D1** | Validity is a decidable predicate on a table; certification is a subtype carrying its proof | Matches the deliverable 1:1; enables schema comparison; removes dependent elimination | Per-cell refined types (pre-rewrite) |
| **D2** | `Row = List Val`, not a heterogeneous list | Homogeneous rows make every operation a `map`/`zip`; field count is a validated invariant, not a type index | `HList` indexed by `List Ty` |
| **D3** | `Val` has a `.null` constructor | One type, uniform errors, SQL-faithful null semantics, direct mapping from `missingValues` | `Option Val` per cell |
| **D4** | `num` is `Rat`, not `Float` | The motivating bug is precisely "large integers become floats" / "1.2e3" | `Float` |
| **D5** | One flat `Column` record + `WellFormed` predicate, not type-indexed constraint structures | Schemas arrive as text; users need messages ("`minimum` is not allowed on a string field") more than impossible states | `ConstraintsOf ty` (pre-rewrite) |
| **D6** | Truth in `Prop`; checkers return `Result` and are proved equivalent | One definition of truth, one implementation, one bridge theorem — no drift | Bool-only predicates |
| **D7** | JSON (Frictionless subset) is the only schema syntax in v0.1 | `Lean.Data.Json` ships with the toolchain (zero deps); JSON is valid YAML 1.2, so `.yaml` files containing JSON already work | Hand-written YAML parser; custom DSL |
| **D8** | Zero external dependencies; stable toolchain `v4.35.0` | Measured: 27 build jobs / ~7 s cold vs 974 jobs / ~10 min with Mathlib, which contributed nothing | Mathlib (used only for `List.Nodup`, which is core) |
| **D9** | Pure CSV parser on `String`; whole file in memory; records carry line numbers | Provable properties need a pure function; line numbers are the cheapest real provenance | Streaming `IO.FS.Stream` parser (unprovable; deferred) |
| **D10** | Diagnostics are a first-class module, not strings | Required: `file:line:column`, `--json` output, error aggregation with a cap, exit codes 0/1/2 | `Except String` |
| **D11** | `docs/SEMANTICS.md` is written before the validator and is the specification of record | Plan Stage 1's acceptance test: an independent reader can decide schema+table by hand | Code-first |
| **D12** | Delete `HList.lean`, `HasCol.lean`, `refinedType`, `cellType`, `primaryKeyProjection?`, `Test.lean` | Redundant under D1/D2; git history is the archive; two row models is worse than either | Archive in-tree |
| **D13** | CI gates: `--wfail`, forbidden-construct grep, `sorryAx` audit, `#guard` evaluation tests | "No sorry" must be a build gate. Executability is gated by evaluation, not by axiom lists: `Classical.choice` in `#print axioms` comes from core's own termination proofs and is erased at runtime | Trust review; a fully constructive axiom list |
| **D14** | Name stays `SchemaCsv`; binary is `schema-csv` | Module paths, history and toolchain already agree; the plan's `tabular` was a placeholder | Rename to `tabular` |

## 5. Semantic policies (the contract)

These are normative. They are restated with formal notation in
`docs/SEMANTICS.md`, which is written in M1 and is the document the Lean
is checked against.

1. **Nulls.** `.null` arises only from a physical string listed in
   `missingValues`. `required = true` plus a missing value is an error
   (`missingRequired`), never a silent null.
2. **`unique` and nulls.** Nulls are **distinct**: two nulls do not collide
   (Postgres semantics). A `nullsDistinct` policy flag is reserved for the
   opposite (one-null) reading.
3. **Primary key.** Composite over the listed columns; every key cell must be
   non-null (`nullKey`); duplicates are `duplicateKey`. An empty `primaryKey`
   means no key check.
4. **Column identity and order.** Identity is the field name. Matching is by
   header name by default, positional with `--positional`. Extra columns are
   `tooManyFields`; missing columns and ragged rows are errors carrying the row's
   line number.
5. **Missing values.** Default `[""]` (Frictionless). Substitution happens
   *before* casting, so `""` is a null and not an empty string.
6. **Lexical rules for numbers.** After trimming ASCII spaces, `int` and `num`
   accept `[+-]?digits([.digits])?([eE][+-]?digits)?`. No thousands separators,
   no locale decimals, no `NaN`/`Inf`. `"007"` casts to `7` — a leading-zero
   identifier must be typed `str`, and the diagnostic says so.
7. **Round-trip is semantic, not lexical.** Validation preserves meaning, not
   bytes. Canonical output may render `"1.0"` as `1`, and SEMANTICS.md says so.
8. **Unsupported in v0.1, reported rather than ignored:** `pattern`,
   `decimalChar`, `groupChar`, date/time types, foreign keys.

## 6. Verification gates

CI fails on any of:

* a build warning (`lake build --wfail`);
* `sorry`, `admit`, `axiom`, `unsafe`, `partial def`, `native_decide` anywhere
  under `SchemaCsv/`;
* a claimed theorem depending on `sorryAx`;
* a failing `lake test` suite — which is also the executability gate, because
  `Tests/Model.lean` *evaluates* every checker with `#guard`;
* a doc example that no longer reproduces (`examples/` + golden outputs).

**Deliberately not gated: `Classical.choice`.** It appears in `#print axioms`
output for declarations that unfold core definitions such as `String.length` or
`List.contains`, whose own termination proofs use it. Those are proof terms,
erased at runtime: the checkers still compute, as `#guard` demonstrates. Making
the axiom list fully constructive would mean reimplementing core's string and
list primitives, which buys this project nothing. The property we actually need
— *the checker sets no obligation aside* — is covered by the `sorryAx` gate plus
the evaluation tests.

## 7. Extension policy

Adding a field type or constraint is expected to be **one edit plus the cases
the compiler demands**, never a hunt through four files. If a proposed feature
requires touching `Column.WellFormed`, `Column.accepts`, `Satisfies`, and the
decoder, that is a signal the model is wrong, not that the feature is hard.

Things deliberately kept out of the type system: per-cell refinement, dependent
row shapes, and anything that makes two schemas incomparable.
