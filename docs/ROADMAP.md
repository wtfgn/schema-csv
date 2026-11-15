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

## M1 — Abstract model · `[ ]`

- [ ] `docs/SEMANTICS.md` — the abstract model in notation, the eight policies,
      the cast rule table, and a set of 20 hand-computed positive/negative cases
- [ ] `Core/Val.lean` — `Val`, `Ty`, `compatible`, `le`, `render`
- [ ] `Core/Column.lean` — `Column`, `Column.WellFormed` (decidable), `Column.accepts`
- [ ] `Core/Schema.lean` — `Schema`, `Schema.WellFormed` (decidable), `fieldOf?`
- [ ] Delete `HList.lean`, `HasCol.lean`, `refinedType`, `cellType` (decision D12)

**Acceptance:** every hand-computed case in `SEMANTICS.md` appears as an
`example`/`#guard` in `Tests/`; a reader who has never seen the code can decide
a table by reading SEMANTICS.md alone.

## M2 — Validator and proofs · `[ ]`

- [ ] `Core/Table.lean`, `Core/Satisfies.lean`
- [ ] `Core/Check.lean` — `validate` with diagnostics, then `validate_sound`,
      `validate_complete`, `validate_iff`
- [ ] `Core/Certified.lean` — `Certified`, `toSatisfies`
- [ ] `Tests/Check.lean` — positive/negative suite; replace `Tests/Axioms.lean`
      contents with the real theorem list
- [ ] Real test driver in `Tests/Main.lean` (returns 1 on any failure)

**Acceptance:** `validate_iff` proved; `#print axioms` clean; both suites green;
`lake test` fails when a known-bad case is made to pass.

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

## Known pre-rewrite code still present

Until M1/M2 these files are still the old model and are scheduled for deletion:
`SchemaCsv/HList.lean`, `SchemaCsv/HasCol.lean`, `SchemaCsv/Table/{Basic,PrimaryKey}.lean`,
`SchemaCsv/Example.lean`, and the `refinedType` / `cellType` machinery in
`SchemaCsv/Field.lean`. They build today and are useful only as a reference while
M1 lands.
