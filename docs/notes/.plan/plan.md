**Project roadmap: Schema-aware tabular data tool (Lean4 core)**

Here is a practical, sequential staging plan. Each stage has a clear goal, concrete deliverables, and explicit “done when…” criteria. The plan assumes the hybrid approach we discussed earlier: a rigorously defined and (partially) verified core in Lean4, with a usable tool built around it.

---

### Stage 0 – Problem framing & requirements (short, optional but recommended)
**Goal:** Make the scope explicit so later design decisions are grounded.

**Deliverables**
- Short requirements document (1–3 pages): target users, main use-cases, must-have vs nice-to-have features, non-goals.
- List of representative example datasets + the problems they currently suffer from (type ambiguity, missing values, constraint violations, etc.).
- Decision on initial scope (e.g. “flat tables only, basic types + simple constraints, no schema evolution yet”).

**Done when**
You can answer “What does success look like for v0.1?” in one paragraph.

---

### Stage 1 – Abstract model & semantics
**Goal:** Define the mathematical objects and the meaning of “a table satisfies a schema.”

**Deliverables**
- Written specification of the abstract model:
  - Types (or sorts) of values
  - Column descriptors
  - Schema structure
  - Table / row representation
  - The satisfaction relation `table ⊨ schema` (or equivalent)
- A collection of positive and negative examples (schemas + tables that should / should not satisfy them).
- Explicit policy decisions (null handling, extra/missing columns, column order significance, etc.).

**Done when**
- The model is small, consistent, and covers the examples you care about.
- An independent reader can look at a schema + table and decide (using only the written rules) whether the table satisfies the schema.

This is the foundation everything else rests on.

---

### Stage 2 – Concrete syntax (surface language)
**Goal:** Give people (and tools) a way to write schemas.

**Deliverables**
- Concrete syntax design (YAML, JSON, custom DSL, or a combination).
- Mapping from concrete syntax → abstract model (i.e. a parsing / desugaring specification).
- A set of example schema files written in the chosen syntax.
- (Optional) A JSON Schema or similar that describes the concrete format.

**Done when**
- You can write the Stage-1 examples in the concrete syntax and recover the abstract schemas unambiguously.
- The syntax is readable by humans and reasonably easy to generate by tools.

---

### Stage 3 – Lean4 formalization of the core model
**Goal:** Turn the abstract model into precise Lean definitions.

**Deliverables**
- Lean4 library containing:
  - Inductive / structure definitions for `Value`, `Type`, `Column`, `Schema`, `Row`, `Table`, …
  - The satisfaction predicate (or equivalent decidable checker + correctness proof).
  - Basic lemmas about the model.
- A small suite of Lean examples / unit tests that mirror the Stage-1 positive/negative examples.

**Done when**
- The Lean definitions faithfully reflect the written abstract model.
- You can state (and ideally prove simple cases of) “this concrete table satisfies / does not satisfy this schema” inside Lean.

---

### Stage 4 – Core algorithms & decidable checking
**Goal:** Implement the executable parts that make the formal model useful.

**Deliverables**
- Decidable (or practical) validation function: `validate : Schema → Table → Bool` (or a richer result type with error locations).
- Proof that the validator is sound (and preferably complete) with respect to the satisfaction predicate.
- Optional: parsers from strings / simple CSV-like input into the Lean `Table` type (still inside Lean for now).
- Basic schema well-formedness checks (duplicate column names, etc.).

**Done when**
- You can run validation on the example tables inside Lean (or via `#eval`) and get the expected answers.
- Soundness (and ideally completeness) is proved for the core checker.

---

### Stage 5 – Key correctness properties
**Goal:** Prove the properties that justify trusting the system.

**Deliverables**
- A short list of the properties you actually care about (start small), for example:
  - Soundness of validation
  - Round-tripping (schema + data → serialization → data recovers a table that still satisfies the schema)
  - Invariants preserved by simple transformations
- Lean proofs of those properties (or clear statements + partial proofs + assumptions).
- Documentation of any remaining axioms or unfinished proofs.

**Done when**
- The most important properties are either fully proved or have a clear, documented proof obligation list.
- You can explain to someone else what is formally guaranteed and what is not.

---

### Stage 6 – Extraction / practical core
**Goal:** Turn the verified Lean core into something that can be used from ordinary code.

**Deliverables**
- Extracted code (or a re-implementation guided by the Lean model) in a systems language (Rust is the most natural today) or via Lean’s code extraction.
- A minimal library API: load schema, load table, validate, report errors.
- Basic CSV (or other) reader that produces the internal table representation while respecting the schema’s missing-value rules, etc.
- Tests that the extracted / re-implemented checker agrees with the Lean version on the example suite.

**Done when**
- You have a command-line or library interface that can validate real files against schemas and produce useful error messages.
- The implementation is recognizably based on the formal model.

---

### Stage 7 – Usable tool & interop
**Goal:** Make something people can actually run on their data.

**Deliverables**
- CLI tool (or library + simple CLI) with the main workflows:
  - Validate a file against a schema
  - Infer a candidate schema from data (optional but useful)
  - Emit a typed / cleaned version of the data
- Documentation, installation instructions, and a few end-to-end tutorials.
- Interop points (e.g. ability to emit / consume Arrow, or produce a Frictionless-compatible descriptor, or a simple Python binding).
- Packaging so others can install and try it.

**Done when**
- A newcomer can install the tool, write a small schema, and successfully validate / reject a real CSV in under 15 minutes.
- Error messages are good enough to be useful.

---

### Stage 8 – Hardening, extensions & evaluation
**Goal:** Turn the prototype into a robust research or production-quality artifact.

**Deliverables**
- Expanded test suite (real-world datasets, edge cases, fuzzing).
- Performance measurements and any necessary optimizations.
- Chosen extensions (richer constraints, foreign keys, schema evolution, dependent/refined types, etc.) with updated formal model + proofs.
- Comparison with existing tools (Frictionless, Pandera, Arrow, etc.) and a clear statement of what is gained by the formal approach.
- Public repository, paper / technical report, or detailed README that tells the whole story.

**Done when**
- The tool is reliable on the datasets you care about.
- You can articulate the formal guarantees and the practical trade-offs.

---

### Suggested ordering & prioritization notes

- Stages 1 → 3 are the intellectual core and should be done carefully; everything else builds on them.
- Stage 4 and 5 can be interleaved (implement a checker, prove the easy properties, improve the checker, prove more).
- Stage 6 is the point at which the project becomes usable outside Lean; many people stop or slow down after a solid Stage 4–5.
- Stage 7 is what turns a research prototype into something others will try.
- Keep the first versions of Stages 1–4 deliberately small. It is far better to have a tiny verified core than a large underspecified language.

Would you like a more detailed breakdown of any particular stage (especially Stage 1 or Stage 3), or a suggested timeline / milestone checklist you can put in a repository?