# CI audit performance

The largest measured delay was the negative audit test. Each sample imports
the full library. The old auditor collected axioms independently for every
declaration. Shared dependencies were visited many times. Invalid imports
also produced the complete semantic report before rejection.

The auditor now builds one dependency graph from all audited definitions
and theorems. It follows types and values, including private definitions,
axiom types and inductive constructors. Forbidden axioms propagate along
reverse edges until no new dependencies remain. Building the graph before
propagation handles cycles without treating a partially visited node as clean.
The allowed axioms and reviewed compiler exceptions are unchanged.

A rejected declaration still fails the run. It does not need a complete
semantic report. Every successful run still emits all semantic records,
registered theorem types and goal results. Fixture tests compare the new
collector with Lean's original collector for every audited root. They also
cover private dependencies, axiom types and mutually recursive inductives.

The same source compiles to the `zlibf-audit` executable. The verification
driver builds it in the invoking auditor checkout. It loads the candidate's
compiled declarations without executing their initializers. Negative tests
build the executable once in the immutable positive snapshot and use that
exact executable for every isolated mutation. Candidate changes cannot
select a replacement auditor.

One full-library measurement covered 36,106 declarations and 406 registered
theorems. Compiling the original auditor alone took 788 seconds to run.
The shared traversal took 62 seconds. Both produced the same 481,854,479-byte
report, byte for byte, as the earlier completed interpreter audit. This
measures the declaration audit, not fresh kernel replay, source compilation,
proof mutants or an entire remote CI run.

All negative samples remain present. Each retains its real unmodified
baseline, isolated build and required rejection. Per-sample elapsed times
make subsequent bottlenecks visible. Fresh kernel replay and full semantic
locks remain independent checks.
