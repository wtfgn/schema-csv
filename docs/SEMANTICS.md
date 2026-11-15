# SchemaCsv — semantics

> **Status:** M1. This document is the **specification of record**. The Lean in
> `SchemaCsv/Core/` is required to match it, and
> [`Tests/Model.lean`](../Tests/Model.lean) encodes every worked example below as
> an executable check. When the two disagree, this document is right and the
> code is a bug.
>
> Implemented here: types, values, columns, schemas — §2–§6.
> Designed here, implemented in M2/M3: rows, tables, satisfaction, casting —
> §7–§9 (marked).

---

## 1. Purpose

The project claims that *"this file satisfies this schema"* is a statement with
a proof behind it. For that claim to mean anything, "satisfies" must be defined
independently of the code that checks it, precisely enough that a reader can
decide a case by hand. That is this document.

Two layers are kept strictly apart:

| Layer | Question | Where |
|---|---|---|
| **Logical** | Does this *value* satisfy this *column*? | §4–§6, implemented |
| **Physical** | How does the text `"007"` become the value `7`? | §8, M3 |

The logical layer never mentions strings, files, or encodings. All ambiguity —
leading zeros, `N/A`, locale decimals, `1e3` — is confined to the physical layer,
where it is resolved by explicit rules and reported as diagnostics.

## 2. Notation

| Symbol | Meaning |
|---|---|
| `⊥` | the `null` value |
| `𝔹`, `ℤ`, `ℚ` | booleans, integers, exact rationals |
| `String` | Unicode text |
| `|s|` | number of characters in `s` |
| `𝒪(α)` | `Option α`, i.e. `⊥` (absent) or `some a` |
| `t`, `v`, `c`, `s`, `r` | a type, value, column, schema, row |
| `⊤` / `⊥` | truth / falsity, when used in a proposition position |

Types and values:

```
Ty  ::= str | int | num | bool
Val ::= ⊥ | str s | int n | num q | bool b        (s : String, n : ℤ, q : ℚ, b : 𝔹)
```

`num` is `ℚ`, **not** a floating-point type. `num 0.1` is exactly 1/10. This is
deliberate: "large integers become floats" is one of the failures the tool
exists to prevent, so the model does not reintroduce it.

`Int` and `Rat` in Lean are arbitrary precision, matching this.

## 3. Inhabitation

```
inhabits : Ty → Val → Prop
inhabits t ⊥        = ⊤                     -- null inhabits every type
inhabits str (str s) = ⊤
inhabits int (int n) = ⊤
inhabits num (num q) = ⊤
inhabits bool (bool b) = ⊤
inhabits t v         = ⊥                    -- any other pairing
```

`⊥` inhabits every type because a null is *typed by its column*: whether a null
is acceptable is a constraint question (§5), not a typing question. This keeps
the type layer total and moves all null policy into one predicate.

Lean: `Val.compatibleB`, with the proposition `Val.compatible t v` being
`Val.compatibleB t v = true`.

> **Design note.** Every predicate in the core is defined as "this `Bool` checker
> returns `true`", and the proposition is an `abbrev` for that equation. One
> definition, no spec/implementation drift, and `Decidable` comes for free. The
> mathematical statement is this document; the checker is the Lean `…B` function.

## 4. Ordering

```
le : Val → Val → Bool
le (int a) (int b) = a ≤ b
le (num a) (num b) = a ≤ b
le _ _            = ⊥
```

Ordering is only defined between two values of the *same numeric type*.
Comparisons of strings, booleans, or mismatched types are **not** ordered and
return `⊥`.

That is sound because of §5: a well-formed column may only declare
`minimum`/`maximum` on `int`/`num`, so an unordered comparison cannot arise from
a schema that passed `WellFormed`. The `⊥` case exists to keep `le` total, not
because it is meaningful.

Lean: `Val.le`.

## 5. Columns

```
Column ::= { name, ty, required, unique, enum, minimum, maximum,
             minLength, maxLength, format, pattern, title, description }
```

A column is a **plain record**. Type/constraint agreement is not enforced by the
structure — it is enforced by `WellFormed` below. Schemas arrive as text from
users, so the failure mode that matters is *"this schema is wrong, and here is
which part"*, not *"this cannot be written down"*.

### 5.1 Acceptance

```
accepts c v =
  if v = ⊥ then ¬ c.required
  else inhabits c.ty v
     ∧ bounds c v
     ∧ lengths c v
     ∧ member c v
```

with

```
bounds c v  = (c.minimum = ⊥  ∨  lo ≤ v)        when c.minimum = some lo
            ∧ (c.maximum = ⊥  ∨  v ≤ hi)        when c.maximum = some hi

lengths c v = v = str s  ⟹  (c.minLength = ⊥ ∨ c.minLength ≤ |s|)
                          ∧ (c.maxLength = ⊥ ∨ |s| ≤ c.maxLength)
              v ≠ string  ⟹  c.minLength = ⊥ ∧ c.maxLength = ⊥

member c v  = c.enum = ⊥  ∨  v ∈ c.enum
```

A null is accepted **exactly** when the column is not required, regardless of
bounds, enumeration, or length. Constraints describe values; a null is the
absence of one.

`unique` is **absent** from `accepts` on purpose. It is a property of a column
across all rows, not of a single cell, so it belongs to table satisfaction (§7).

Lean: `Column.acceptsB` / `Column.accepts`; `boundsB`, `lengthsB`, `memberB`.

### 5.2 Well-formedness

```
WellFormed c =
    c.name ≠ ""
  ∧ (c.enum = none ∨ (c.enum = some vs ∧ vs ≠ [] ∧ ∀ x ∈ vs, x ≠ ⊥ ∧ inhabits c.ty x))
  ∧ shape(  c.ty = str          ⟹ c.minimum = ⊥ ∧ c.maximum = ⊥ ∧ c.format = ⊥
          ∧ c.ty ∈ {int, num}   ⟹ c.minLength = ⊥ ∧ c.maxLength = ⊥ ∧ c.format = ⊥
          ∧ c.ty = bool         ⟹ c.minimum = ⊥ ∧ c.maximum = ⊥
                                ∧ c.minLength = ⊥ ∧ c.maxLength = ⊥ ∧ c.format = ⊥ )
  ∧ (c.minimum = some a ∧ c.maximum = some b ⟹ a ≤ b)
  ∧ (c.minLength = some a ∧ c.maxLength = some b ⟹ a ≤ b)
  ∧ c.pattern = ⊥
```

Three things are worth calling out.

* **`minimum` on a string is an error.** It is not ignored, not coerced, not
  "best effort". A schema that says it is rejected, because silently ignoring a
  constraint is the behaviour this project exists to replace.
* **`minLength > maxLength` is an error.** The absence of that check in the
  pre-rewrite code was a real defect: it produced a column type with no
  inhabitants, reported at an unrelated use site.
* **`pattern` and `format` are rejected, not ignored.** They are reserved by the
  schema language and reserved in the parser; setting either is reported as
  "unsupported in v0.1". They become real checks in M3, and this clause then
  disappears. This is policy 8 (§10).

Lean: `Column.wellFormedB` / `Column.WellFormed`.

## 6. Schemas

```
Schema ::= { name, version, fields, missingValues, primaryKey, trueValues, falseValues }

WellFormed s =
    (∀ c ∈ s.fields, WellFormed c)
  ∧ distinct (map name s.fields)
  ∧ s.primaryKey ⊆ map name s.fields
  ∧ distinct s.primaryKey
  ∧ (∀ n ∈ s.primaryKey, ∃ c ∈ s.fields, c.name = n ∧ c.required = true)
```

`primaryKey` outside `fields` is an error. A key column that is not required is
an error — the last clause is what makes "a key cell is never null" a
consequence of well-formedness rather than a separate runtime check.

The empty schema (`fields = []`) is well-formed and accepts any table of
zero-width rows. That keeps the predicate closed under the obvious constructors
and avoids a special case in the checker.

Lean: `Schema.WellFormed`.

## 7. Tables and satisfaction — *M2*

Declared here so the contract is visible; implemented next.

```
Row   = List Val          -- aligned with s.fields by position
Table = List Row

rowAccepts s r = |r| = |s.fields| ∧ ∀ i < |s.fields|, accepts s.fields[i] r[i]

uniqueOK s t  = ∀ c ∈ s.fields with c.unique,
                  no two distinct rows have the same non-null value at c
                  (nulls are distinct, policy 2)

primaryKeyOK s t = s.primaryKey = [] ∨
                   no two distinct rows agree on every primary-key column

Satisfies s t = WellFormed s
              ∧ (∀ r ∈ t, rowAccepts s r)
              ∧ uniqueOK s t
              ∧ primaryKeyOK s t
```

`uniqueOK` ignores nulls: two rows that are both null at a unique column do not
collide. This is PostgreSQL's reading. The opposite convention (at most one
null) is a policy flag, not a redesign.

A row whose length differs from the schema's field count is **not** silently
padded or truncated: `rowAccepts` is false, and the checker reports
`tooFewFields` / `tooManyFields` with the row's line number.

## 8. Casting — *M3, normative for that milestone*

The physical layer. Its only job is to turn text into values, and to say exactly
why when it cannot.

```
castVal : Column → String → Result Val
```

| Type | Accepted lexical forms | Becomes | Rejected |
|---|---|---|---|
| `str` | anything | `str s` | — |
| `int` | `[+-]?[0-9]+` | `int n` | `"1.0"`, `"1,000"`, `"1e3"`, `""` (unless a missing value) |
| `num` | `[+-]?[0-9]+(\.[0-9]+)?([eE][+-]?[0-9]+)?` | `num q` exactly | `"NaN"`, `"Inf"`, `"1,5"` |
| `bool` | a member of `trueValues` / `falseValues` | `bool b` | everything else |

Rules that resolve the ambiguities named in the problem statement:

1. **Missing values first.** If the raw text is in `s.missingValues`, the value
   is `⊥` — before any type is considered. So `""` is a null, not an empty
   string, and `""` in a required column is a `missingRequired` error, not a
   cast error.
2. **No thousands separators, no locale decimals.** `"1,234"` is rejected.
   Supporting them requires a per-column `groupChar`/`decimalChar`, which is a
   future feature, not a heuristic.
3. **Leading zeros are value-preserving, not text-preserving.** `"007"` casts to
   `7`. A leading-zero *identifier* must be declared `str`. The diagnostic says
   so explicitly, because this is the single most common silent-corruption case.
4. **Exactness.** `num` keeps `ℚ`. `"0.1"` is 1/10, and `"0.30000000000000004"`
   does not become `0.3`.
5. **Round-trip is semantic, not lexical.** `render (cast "1.0") = "1"`.
   Validation preserves *meaning*, not bytes; the tool is not a formatter.

## 9. Diagnostics — *M3*

Every failure carries a location and a code, so that a rejection is actionable:

```
Diagnostic = { file, line, column?, code, detail }
code ∈ { missingRequired, castFailed, belowMinimum, aboveMaximum,
         notInEnum, badLength, badFormat, duplicateKey, nullKey,
         tooFewFields, tooManyFields, schemaInvalid }
```

Rendered as `file:line: column: expected <type>, got "<text>"`. Errors are
aggregated with a cap (`--max-errors`), never only the first.

## 10. The policies, restated

These were approved as part of the design; they are normative.

1. **Nulls.** `⊥` arises only from a physical string in `missingValues`.
   `required` plus a missing value is an error, never a silent null.
2. **`unique` and nulls.** Nulls are distinct. Two nulls do not collide.
3. **Primary key.** Composite, over required columns only (§6), so key cells are
   never null. Duplicates are `duplicateKey`.
4. **Column identity and order.** Identity is the name; position is the order in
   `fields`. Matching is by header name by default, positional with `--positional`.
5. **Missing values.** Default `[""]`, applied before casting.
6. **Lexical rules.** §8.
7. **Round-trip.** Semantic, not lexical. §8 rule 5.
8. **Unsupported in v0.1, reported not ignored.** `pattern`, `format`,
   `decimalChar`, `groupChar`, date/time types, foreign keys.

## 11. Worked examples

Every row below is a case in [`Tests/Model.lean`](../Tests/Model.lean), which
evaluates it at build time. Column `age` means `{ ty := num, min := 0, max := 150 }`.

| # | Case | Expected | Why |
|---|---|---|---|
| 1 | `inhabits int (int 3)` | true | matching constructor |
| 2 | `inhabits str (int 3)` | false | width mismatch |
| 3 | `inhabits bool (str "true")` | false | text is not a boolean; casting is §8 |
| 4 | `inhabits int ⊥` | true | null is typed by its column |
| 5 | `le (int 1) (int 2)` | true | |
| 6 | `le (int 3) (int 2)` | false | |
| 7 | `le (num 1/2) (num 2/3)` | true | exact rationals |
| 8 | `le (int 1) (str "1")` | false | unordered pair, never arises from a WF schema |
| 9 | `accepts {required} ⊥` | false | null in a required column |
| 10 | `accepts {not required} ⊥` | true | |
| 11 | `accepts {not required, min 0} ⊥` | true | bounds do not apply to nulls |
| 12 | `accepts {int} (int 7)` | true | |
| 13 | `accepts {int} (str "7")` | false | logical layer never coerces |
| 14 | `accepts age (num 200)` | false | above maximum |
| 15 | `accepts age (num 0)` | true | boundary is inclusive |
| 16 | `accepts {str, minLength 2} (str "a")` | false | too short |
| 17 | `accepts {str, minLength 2} (int 5)` | false | length declared but value is not a string |
| 18 | `accepts {enum [1,2]} (int 3)` | false | not in enumeration |
| 19 | `accepts {enum []} …` | schema error | empty enumeration is not well-formed |
| 20 | `wellFormed {str, minimum 0}` | false | bounds are numeric-only |
| 21 | `wellFormed {int, minLength 1}` | false | length is string-only |
| 22 | `wellFormed {min 5, max 2}` | false | inverted bounds |
| 23 | `wellFormed {pattern "x"}` | false | reserved, reported not ignored |
| 24 | `wellFormed {format email}` | false | reserved, reported not ignored |
| 25 | `wellFormed {enum [⊥]}` | false | null in an enumeration |
| 26 | schema with two columns named `a` | not well-formed | names must be distinct |
| 27 | schema with `primaryKey ["id"]`, `id` optional | not well-formed | key columns must be required |
| 28 | schema with `primaryKey ["ghost"]` | not well-formed | key must name a field |
| 29 | schema with `primaryKey ["id","id"]` | not well-formed | key entries must be distinct |
| 30 | schema with no fields | well-formed | closed under the obvious constructors |

## 12. What is proved, and what is not

**Proved (M1).**

| Name | Statement |
|---|---|
| `Val.compatible_null` | `⊥` inhabits every type |
| `Column.accepts_null_iff` | a column accepts `⊥` iff it is not required |

**Checked by evaluation, not proof (M1).** All of §11. `#guard` evaluates the
checkers at build time, so a broken checker fails the build; it is evidence of
correct behaviour on the listed cases, not a theorem about all inputs.

**Not yet proved (M2+).**

* `validate_sound` / `validate_complete` / `validate_iff` — the checker agrees
  with §7 for *all* schemas and tables.
* cast correctness (§8) against this document.
* CSV round-trip.

**Explicitly not guaranteed, in any version yet.**

* That a schema's `missingValues` are sensible for its types.
* That `enum` values satisfy the column's own bounds (an enum value outside
  `[minimum, maximum]` is currently well-formed, and simply unreachable by
  `accepts`; tightening this is an M6 decision).
* Anything about locale, encoding, or CSV dialect beyond §8 and the parser in M3.

The point of listing these is policy: an unlisted guarantee is not a guarantee.
When one of these becomes a claim, it gets a theorem and a line in this section.
