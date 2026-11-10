# zlib-f

Formal verification of zlib in Lean 4: safety, termination, resource ownership
and functional correctness of a faithful C translation.

**Work in progress. Full verification is not complete.**
The first target is the default LP64 Linux static build with the default allocator.

## Documentation

**[Read the documentation website](https://www.dataisland.org/zlib-f/)** · [Website content sources](docs/README.md)

| Start here | What it answers |
| --- | --- |
| [Proof overview](https://www.dataisland.org/zlib-f/reference/docs/overview.html) | What is the claim, its assumptions and the proof framework? |
| [Current status](https://www.dataisland.org/zlib-f/reference/docs/progress.html) | What is established and what remains? |
| [All-target proof graph](https://www.dataisland.org/zlib-f/reference/docs/progress.html#proof-progress-graph) | How do targets depend on each other, and which input ranges are covered? |
| [Proof evidence](https://www.dataisland.org/zlib-f/reference/docs/progress.html) | Where are the exact statements, proofs and independent relationship tables? |
| [Specifications](https://www.dataisland.org/zlib-f/reference/docs/spec/README.html) | What safety, input, API, helper and format requirements must be proved? |
| [API](https://www.dataisland.org/zlib-f/reference/api.html) | What does each function require and guarantee? |
| [Data format](https://www.dataisland.org/zlib-f/reference/docs/spec/format/README.html) | What do DEFLATE, zlib and gzip bytes mean? |
| [Design](https://www.dataisland.org/zlib-f/reference/docs/design/README.html) | How do the translation and memory model work? |
| [Proofs](https://www.dataisland.org/zlib-f/reference/docs/proof/README.html) | How are the arguments composed? |
| [Checking](https://www.dataisland.org/zlib-f/reference/docs/checking/README.html) | What counts as an accepted proof? |
| [Contributing](docs/checking/contributing.md) | How do I prove, register and check a target, step by step? |
| [Glossary](docs/glossary.md) | What do `Good`, `DGood`, data epoch, scoped admission and `C1`–`C7` mean? |

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

See [checking](https://www.dataisland.org/zlib-f/reference/docs/checking/README.html) for each check's scope and final acceptance.
Differential tests are evidence of translation fidelity, not proof.
[Source findings](docs/findings.md) state their confidence and scope.

## Source fix

`inflateCopy` compares a static fixed table with a separately allocated state
table after a default-initialized stream pauses inside a fixed block.
The [retained reproduction](docs/findings/inflate-copy-fixed/README.md) diagnoses
the pinned unmodified C. The verified source now includes the exact fix from
[upstream PR #1369](https://github.com/madler/zlib/pull/1369) through
[the temporary patch](patches/README.md). The translation uses the same equality
check. Confidence is high for the diagnosed LP64 issue; the full public copy
proof remains open.
