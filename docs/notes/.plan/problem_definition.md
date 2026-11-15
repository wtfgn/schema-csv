**Stage 0 Brainstorm: Problems, Gap, Objectives, and Product Vision**

### 1. What is wrong with current CSV (and similar ad-hoc tabular formats)?

CSV is deceptively simple and extremely widely used, but it has fundamental weaknesses:

- **No reliable type or schema information**  
  Everything is text. A column that looks like numbers can contain “N/A”, “”, “1,234”, “1.2e3”, or mixed types. Downstream tools silently coerce or fail in unpredictable ways.

- **Ambiguous parsing rules**  
  Quoting, escaping, newlines inside fields, different delimiters, encodings, and header presence are handled inconsistently across tools and languages.

- **Silent data corruption / loss of meaning**  
  Leading zeros disappear, large integers become floats, dates are interpreted differently by locale, empty string vs null is confused, etc.

- **Schema is tribal knowledge**  
  The “real” meaning of columns (units, allowed ranges, uniqueness, relationships, null policies) lives in people’s heads, README files, or brittle validation scripts that are rarely kept in sync with the data.

- **Evolution and interoperability pain**  
  When a column is added, a type changes, or a new constraint appears, there is no standard way to express the change or to check that old and new data still make sense together.

- **Validation is usually after-the-fact and incomplete**  
  Tools like Pandera, Great Expectations, or Frictionless exist, but they are often bolted on, not foundational, and rarely come with strong formal guarantees.

**Result:** CSV is excellent for quick interchange and human inspection, but terrible as a *reliable* data contract.

### 2. What is the real gap?

Existing solutions occupy different points on a spectrum:

| Approach | Strength | Weakness |
|----------|----------|----------|
| Plain CSV | Ubiquitous, simple | No schema, no guarantees |
| Frictionless / Table Schema / CSVW | Good practical schemas | Limited formal semantics, weak guarantees |
| Pandera / Great Expectations / Pydantic | Convenient validation | Runtime-only, Python-centric, no deep proofs |
| Apache Arrow / Parquet | Strong physical types & performance | Schema is more about storage than rich logical constraints |
| Database schemas / SQL | Strong constraints | Heavyweight, not designed for file interchange |
| Full formal methods | Highest assurance | Almost never applied to everyday tabular data |

**The gap:** There is no lightweight, formally grounded way to treat a tabular schema as a *precise, checkable, evolvable contract* that sits between “just a CSV” and “full database or proof assistant”.

Most tools either:
- stay informal and pragmatic, or
- are heavyweight formal systems that almost no data practitioner will use.

### 3. Our objective

Build a **schema-first tabular data system** whose core is mathematically precise and (partially) machine-checked, while still being usable by ordinary data workers.

More concretely:

- Give schemas a clear mathematical meaning.
- Make validation a sound decision procedure with respect to that meaning.
- Keep the surface simple enough that people will actually write and share schemas.
- Produce both a formal artifact (Lean) and a practical tool that people can run on real files.
- Provide stronger guarantees than existing schema + validation libraries, without requiring users to become theorem-proving experts.

### 4. How do we tackle the problems?

**Core strategy (hybrid):**

1. Design a clean abstract model of schemas and tables + a precise satisfaction relation.
2. Formalize that model in Lean4 and prove the key properties we care about (soundness of validation, basic invariants, etc.).
3. Extract or re-implement a practical checker and tooling layer (most likely Rust or a Lean-extracted core + thin wrappers).
4. Offer a concrete, human-friendly schema language that maps cleanly onto the formal model.
5. Make the tool useful for the common case (validate, clean, report errors) while leaving the door open for stronger formal uses.

We deliberately do *not* try to replace CSV for every use. We make it possible to attach a reliable contract to CSV-like data.

### 5. What are we going to produce?

A layered system:

- **Formal core (Lean4)**  
  Definitions of schemas, tables, satisfaction, validators, and proofs of the main correctness properties.

- **Practical engine**  
  Fast validation, error reporting with locations, basic CSV reading that respects the schema’s missing-value and type rules.

- **Schema language**  
  A concrete syntax (probably YAML/JSON-based initially, possibly with a nicer DSL later) that people can write and version-control next to their data.

- **Tooling**  
  CLI + library interface. Later possible: language bindings, notebook integration, schema inference helpers, emission of Arrow/Parquet with attached metadata, etc.

- **Documentation & examples**  
  Clear explanation of the formal guarantees, plus many real-world style examples.

### 6. How does the product mitigate the problems?

| Problem | Mitigation |
|---------|------------|
| No types / schema | Schema is first-class and required for “validated” data |
| Ambiguous parsing | Schema + explicit missing-value rules + type casting policy |
| Silent corruption | Validation rejects or flags bad values before they propagate |
| Tribal knowledge | Schema lives with the data and can be checked automatically |
| Weak validation | Validator is proven sound w.r.t. a formal semantics |
| Evolution pain | (Later stages) support for schema versions and migration checks |

The formal core gives confidence that the checker is not lying. The practical layer makes that confidence usable.

### 7. What should the final product look like? How do users use it?

**Vision of a polished v1 (or v0.9):**

```bash
# Validate a file
tabular check data.csv --schema people.schema.yaml

# Output example
data.csv: OK (1,024 rows, schema people v1.2)

# Or with errors
data.csv:3: age: value "-5" does not satisfy constraint minimum = 0
data.csv:17: email: value "not-an-email" does not match pattern ...
2 errors found.
```

Other common commands:

```bash
tabular describe data.csv          # suggest a schema
tabular clean data.csv -o clean.csv --schema ...
tabular info people.schema.yaml    # show human-readable schema summary
```

**Typical user workflows**

1. **Data publisher**  
   Writes a schema once, puts it next to the CSV (or in a Data Package), and ships both. Consumers can automatically validate.

2. **Data consumer / analyst**  
   Receives CSV + schema, runs `tabular check`, and only proceeds if it passes. Can trust types and constraints more than with raw CSV.

3. **Pipeline author**  
   Uses the library in a larger workflow: read → validate against schema → transform → re-validate or emit new schema.

4. **Power user / researcher**  
   Can inspect or extend the Lean formalization, prove additional properties, or use the core as a reference implementation.

**What the “product” feels like**

- To ordinary users: a better-behaved CSV tool with schemas (familiar, low friction).
- To careful users: a tool whose validation results come with mathematical backing.
- To formal-methods people: a realistic case study of applying Lean to everyday data problems.

### 8. My own additional ideas / provocations

- Start *extremely* small. A tiny verified core (basic types + nullability + a few constraints) that is fully proven is more valuable than a large language with many unproven features.
- Make the schema language deliberately close to Frictionless Table Schema at first. This gives immediate interop and a large set of existing examples to test against, while still allowing a cleaner formal semantics underneath.
- Treat “error messages with provenance” as a first-class design goal. Formal soundness is useless if users cannot understand *why* a row was rejected.
- Consider a “schema + data → certified table” story: successful validation produces not just a boolean but a dependent-typed or proof-carrying table that downstream verified code can rely on.
- Later differentiator: support for *schema evolution* with formal migration guarantees (“this old table can be safely viewed under the new schema” or “here is a proven translation”).
- Resist the temptation to boil the ocean (full dependent types on every cell, arbitrary cross-row predicates, etc.) until the basic contract story is solid and usable.

---

**Summary of Stage 0 position**

- **Problem**: CSV is ubiquitous but unreliable as a data contract.  
- **Gap**: No lightweight, formally grounded schema layer for tabular files.  
- **Objective**: Precise schemas + sound validation + practical tooling.  
- **Approach**: Formal model in Lean → proven core → usable tool.  
- **Product**: Schema language + validator + CLI/library that makes “this CSV satisfies its schema” a trustworthy statement.  
- **User experience**: Feels like a better CSV tool; underneath it has real guarantees.

Would you like to refine any of these points further (e.g. narrow the initial scope more aggressively, prioritize particular user personas, or sketch the very first “hello world” schema + validation story)?