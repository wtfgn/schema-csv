module

public import SchemaCsv.Core.Val
public import SchemaCsv.Core.Column
public import SchemaCsv.Core.Schema
public import SchemaCsv.Core.Report
public import SchemaCsv.Core.Table
public import SchemaCsv.Core.Satisfies
public import SchemaCsv.Core.Check
public import SchemaCsv.Core.Certified

/-!
# SchemaCsv

Schema-aware tabular data. The public API is the verified core:

* `SchemaCsv.Ty`, `SchemaCsv.Val` — logical values
* `SchemaCsv.Column` — fields and their constraints
* `SchemaCsv.Schema` — schemas and schema well-formedness
* `SchemaCsv.Row`, `SchemaCsv.Table` — data
* `SchemaCsv.Satisfies` — what conformance means

See `docs/DESIGN.md` for the architecture and `docs/SEMANTICS.md` for the
contract these definitions implement.
-/
