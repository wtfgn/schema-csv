# SchemaCsv — roadmap

Target: v0.1 as defined in [DESIGN.md](DESIGN.md) §1. Each milestone is an
approval gate: the next one does not start until the previous one is accepted.

Legend: `[x]` done · `[~]` in progress · `[ ]` not started

## M0 — Foundation reset · `[x]` accepted

- [x] Zero-dependency `lakefile.toml` (Mathlib removed — decision D8)
- [x] Stable toolchain `leanprover/lean4:v4.35.0`
- [x] `lake build` fails on warnings; library, example and `tests` are default targets
- [x] `lake test` wired to a real driver (`Tests/Main.lean`)
- [x] Axiom audit file (`Tests/Axioms.lean`) + CI gate
- [x] CI rewritten: `--wfail`, forbidden-construct grep, axiom audit, `lake test`
- [x] `.gitignore` fixed (no longer hides `.plan/` or `Test*.lean`)
- [x] `docs/DESIGN.md` (architecture + decision log D1–D14) committed
- [x] `docs/ROADMAP.md` committed
- [x] Scratch file `SchemaCsv/Test.lean` deleted
- [x] `README.md` replaced with an accurate short version

**Acceptance:** cold `lake build` under 15 s; CI green; design doc merged.

## M1 — Abstract model · `[x]` accepted

- [x] `docs/SEMANTICS.md` — the abstract model in notation, the eight policies,
      the cast rule table, and 30 worked cases
- [x] `Core/Val.lean` — `Val`, `Ty`, `compatible`, `le`, `render`
- [x] `Core/Column.lean` — `Column`, `Column.WellFormed`, `Column.accepts`
- [x] `Core/Schema.lean` — `Schema`, `Schema.WellFormed`, `fieldOf?`, `isMissingValue`
- [x] Delete `HList`, `HasCol`, `Table/*`, `Field`, `Constraints`, `Format`,
      `Basic`, the old `Schema`, and `Example` (decision D12)
- [x] `Tests/Model.lean` — 30 `#guard` cases + 2 theorems

**Acceptance:** every hand-computed case in `SEMANTICS.md` appears as an
`example`/`#guard` in `Tests/`; a reader who has never seen the code can decide a
case by reading SEMANTICS.md alone.

**Two findings during M1 that changed the plan:**

1. *Encoding.* Every predicate is now `abbrev P := checkerB … = true`. The
   original design had hand-written `Decidable` instances per predicate
   (decision D6); those could not be written robustly against a 13-field record,
   and `abbrev` over a `Bool` checker makes `Decidable` automatic while keeping
   one definition. `docs/DESIGN.md` §6 and decision D13 were updated to match.
2. *Axiom audit.* Requiring the absence of `Classical.choice` is not achievable:
   core definitions (`String.length`, `List.contains`) carry it inside their own
   termination proofs. It is erased at runtime. The gate now forbids `sorryAx`
   only, and executability is gated by `#guard` evaluation in `Tests/Model.lean`.

## M2 — Validator and proofs · `[x]` accepted

- [x] `Core/Table.lean` — `Row`, `Table`, `cellOf`, `columnValues`
- [x] `Core/Report.lean` — `Loc`, `Code`, `Diagnostic`, `Result`
- [x] `Core/Satisfies.lean` — `rowAccepts`, `uniqueOK`, `primaryKeyOK`, `Satisfies`
- [x] `Core/Check.lean` — `validate` collecting diagnostics
- [x] `Core/Certified.lean` — `Certified`, `certify`, `certifyOfValidate`
- [x] `Core/Check.lean` — `validate_sound`, `validate_complete`, **`validate_iff`**
- [x] `Tests/Check.lean` — 25 behavioural + golden-message checks
- [x] `Tests/Axioms.lean` — all 11 claimed theorems audited

**Acceptance:** `validate_iff` proved with no `sorryAx`; positive and negative
tables both behave; diagnostics collect rather than short-circuit.

**Scope note.** `Report.lean` was pulled forward from M3 because `validate` has to
return something. It now holds the diagnostic *data types*; rendering, locations,
and grouping stay in M3. Two things are deliberately not proved: diagnostic
message accuracy (§7.1 of SEMANTICS) and the table-level *cause* of a duplicate
key — v0.1 reports one summary `duplicateKey`.

## M3 — CSV and casting · `[ ]`

- [ ] `Csv/Parse.lean` — RFC 4180-ish parser, `RawRecord` carries a line number,
      CRLF + quoted newlines + `""` escapes + BOM, proven round-trip
- [ ] `Core/Cast.lean` — `castVal`, `castRow`, `castVal_spec`
- [ ] `Report.lean` — `Loc`, `Code`, `Diagnostic`, `render`
- [ ] `examples/people.{schema.json,csv}`, `examples/people-bad.csv` with one row
      per diagnostic kind

**Acceptance:** running the pipeline on `examples/people-bad.csv` yields exactly
the documented diagnostics, line numbers included.

## M4 — Schema syntax · `[ ]`

- [ ] `Syntax/Json.lean` — decode/encode the Frictionless subset, with `Loc`-less
      but field-named decode errors
- [ ] `docs/SCHEMA.md` — field-by-field reference + compatibility matrix
- [ ] `info` subcommand

**Acceptance:** every `examples/*.schema.json` decodes to the hand-written
schema; a malformed schema yields `field "age": minimum must be a number`, not a
crash.

## M5 — CLI and documentation · `[ ]`

- [ ] `Cli.lean` — `check`, exit codes 0/1/2, `--json`, `--max-errors`, `--positional`
- [ ] `README.md` — 15-minute quickstart
- [ ] CI runs the quickstart verbatim and asserts exit codes and message text

**Acceptance:** a newcomer validates a real CSV in under 15 minutes using only
README.md.

## M6 — Hardening · `[ ]`

- [ ] Fuzz the CSV parser (random bytes must not crash)
- [ ] Unique/primary-key on 10⁵ rows; `Std.HashMap` implementation with an
      equivalence proof against the O(n²) spec
- [ ] Benchmarks and documented throughput
- [ ] Run against two real-world public datasets

## M7 — Differentiators · `[ ]`

- [ ] `Schema.Compatible` (relaxation) with sound + complete
      `isCompatible` proof: `s₁ ⊑ s₂ → ∀ t, Satisfies s₁ t → Satisfies s₂ t`
- [ ] Public `Certified` API documented as the "proof-carrying table" story

## M8 — Polish · `[ ]`

- [ ] `infer` (schema suggestion), `clean` (canonical output)
- [ ] Docs site, release tagging, install instructions

## Deferred (documented, not improvised)

Regex `pattern`; date/time types; foreign keys; YAML parser; streaming; Arrow /
Parquet interop; Python bindings; schema inference beyond `infer`.

## Pre-rewrite code

Removed at M1: `SchemaCsv/{Basic,Constraints,Format,Field,Schema,HList,HasCol,Table,Example}.lean`
and `SchemaCsv/Table/`. The old model (validity encoded in per-cell dependent
types) is preserved in git history at `a528489` and earlier. The library is now
`SchemaCsv/Core/{Val,Column,Schema}.lean` only.
