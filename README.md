# zlib-f

Formal verification of zlib in Lean 4: safety, termination, resource ownership
and functional correctness of a faithful C translation.

**Work in progress. Full verification is not complete.**
The first target is the default LP64 Linux static build with the default allocator.

## Documentation

**[Open the documentation](docs/README.md)**

| Start here | What it answers |
| --- | --- |
| [Proof overview](docs/overview.md) | What is the claim, its assumptions and the proof framework? |
| [Current status](docs/progress.md) | What is established and what remains? |
| [All-target proof graph](docs/progress.md#proof-progress-graph) | How do targets depend on each other, and which input ranges are covered? |
| [Proof evidence](docs/progress.md) | Where are the exact statements, proofs and independent relationship tables? |
| [Specifications](docs/spec/README.md) | What safety, input, API, helper and format requirements must be proved? |
| [API](docs/spec/api/README.md) | What does each function require and guarantee? |
| [Data format](docs/spec/format/README.md) | What do DEFLATE, zlib and gzip bytes mean? |
| [Design](docs/design/README.md) | How do the translation and memory model work? |
| [Proofs](docs/proof/README.md) | How are the arguments composed? |
| [Checking](docs/checking/README.md) | What counts as an accepted proof? |

## Repository

- `zlib/`: pinned upstream source, never edited in place; fixes are in `patches/`.
- `ZlibF/Zlib/`: statement-by-statement C translation.
- `ZlibF/Spec/`: format models and concrete verification targets.
- `ZlibF/Proof/` and `ZlibF/Math/`: implementation proofs and heap-free reasoning.
- `ZlibF/Runtime/`: memory, pointer, arithmetic and execution semantics.
- `tests/`: differential, mutation and proof-audit checks.

## Local checks

```bash
lake build ZlibF
scripts/check-sorry.sh
```

See [checking](docs/checking/README.md) for each check's scope and final acceptance.
Differential tests are evidence of translation fidelity, not proof.
[Source findings](docs/findings.md) state their confidence and scope.
