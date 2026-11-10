# zlib-f

Formal verification of zlib in Lean 4: safety, termination, resource ownership
and functional correctness of a faithful C translation.

**Work in progress. Full verification is not complete.**
The first target is the default LP64 Linux static build with the default allocator.

## Documentation

**[Open the documentation](docs/README.md)**

| Start here | What it answers |
| --- | --- |
| [Current status](docs/overview.md) | What is established and what remains? |
| [Public API proof graph](docs/progress.md) | Which final API targets have checked or registered proofs? |
| [Supporting proofs](docs/supporting-proofs.md) | Which internal targets and models support the API proofs? |
| [API](docs/api/README.md) | What does each function require and guarantee? |
| [Data format](docs/format/README.md) | What do DEFLATE, zlib and gzip bytes mean? |
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

## Source fix

`inflateCopy` compares a static fixed table with a separately allocated state
table after a default-initialized stream pauses inside a fixed block.
The [retained reproduction](docs/findings/inflate-copy-fixed/README.md) diagnoses
the pinned unmodified C. The verified source now includes the exact fix from
[upstream PR #1369](https://github.com/madler/zlib/pull/1369) through
[the temporary patch](patches/README.md). The translation uses the same equality
check. Confidence is high for the diagnosed LP64 issue; the full public copy
proof remains open.
