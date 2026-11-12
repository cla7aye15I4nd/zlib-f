# zlib-f

Formal verification of zlib in Lean 4: safety, termination and resource ownership of a
faithful C translation. Functional correctness is not planned since 2026-11-11, except a
functional fact that a planned safety proof depends on; what is already proved of it stays.

**Work in progress. The project is not finished.**
It is finished when two results are accepted, in this order: `inflate` is safe on every
input; `deflate` is safe on every input, both with their call sequences. The safety of
`compress` and `uncompress` follows as compositions. The target is
the default x86_64 Linux build. The gzip file interface, the callback decoder and other
build configurations are not planned. The [status page](https://www.dataisland.org/zlib-f/status.html)
shows each result as open, checked or registered, from the proof records.

## Documentation

**[Read the documentation website](https://www.dataisland.org/zlib-f/)** · [Website content sources](docs/README.md)

| Start here | What it answers |
| --- | --- |
| [Proof overview](https://www.dataisland.org/zlib-f/reference/docs/overview.html) | What is the claim, its assumptions and the proof framework? |
| [Results and status](https://www.dataisland.org/zlib-f/status.html) | What is established, what is planned and what is not? |
| [All-target proof graph](https://www.dataisland.org/zlib-f/reference/docs/progress.html#proof-progress-graph) | How do targets depend on each other, and which input ranges are covered? |
| [Evidence index](https://www.dataisland.org/zlib-f/reference/docs/progress.html) | Where are the exact statements, proofs and dependencies of every target? |
| [Specifications](https://www.dataisland.org/zlib-f/reference/docs/spec/README.html) | What safety, input, API, helper and format requirements must be proved? |
| [API](https://www.dataisland.org/zlib-f/reference/api.html) | What does each function require and guarantee? |
| [Data format](https://www.dataisland.org/zlib-f/reference/docs/spec/format/README.html) | What do DEFLATE, zlib and gzip bytes mean? |
| [Design](https://www.dataisland.org/zlib-f/reference/docs/design/README.html) | How do the translation and memory model work? |
| [Proofs](https://www.dataisland.org/zlib-f/reference/docs/proof/README.html) | How are the arguments composed? |
| [Checking](https://www.dataisland.org/zlib-f/reference/docs/checking/README.html) | What counts as checked and as accepted? |
| [Contributing](https://www.dataisland.org/zlib-f/reference/docs/checking/contributing.html) | Which commands do I run, in which order? |
| [Glossary](https://www.dataisland.org/zlib-f/reference/docs/glossary.html) | What do the terms mean? |

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

[Contributing](docs/checking/contributing.md) lists every step. See [checking](https://www.dataisland.org/zlib-f/reference/docs/checking/README.html) for each check's scope and final acceptance.
Differential tests are evidence of translation fidelity, not proof.
[Source findings](docs/findings.md) state their confidence and scope.

## Source finding: deflateCopy after deflateResetKeep

After a direct `deflateResetKeep` and a `deflate(Z_BLOCK)`, two chain heads wait for insertion;
`deflateCopy` does not copy their `prev` slots, and a `Z_RLE` or `Z_HUFFMAN_ONLY` flush on the copy
ends with `insert = 0`, so they are never re-inserted. A later default-strategy `deflate` then
follows an uninitialised `prev` slot, and `longest_match` reads outside the window. The
[retained reproduction](docs/findings/deflate-copy-pending-prev/README.md) diagnoses the pinned
unmodified C on x86_64 Linux: AddressSanitizer reports the read outside the window, and valgrind
the use of the uninitialised slot. Confidence is high for the diagnosed sequence. Scope: it needs `deflateResetKeep`, which zlib.h lists among the
undocumented functions and which the proved deflate stream domain excludes
([deviations](docs/deviations.md)). Not reported upstream.

## Source fix

`inflateCopy` compares a static fixed table with a separately allocated state
table after a default-initialized stream pauses inside a fixed block.
The [retained reproduction](docs/findings/inflate-copy-fixed/README.md) diagnoses
the pinned unmodified C. The verified source now includes the exact fix from
[upstream PR #1369](https://github.com/madler/zlib/pull/1369) through
[the temporary patch](patches/README.md). The translation uses the same equality
check. Confidence is high for the diagnosed LP64 issue; the full public copy
proof is open and is planned: `inflateCopy` is a stream call that `inflate_sequence` ranges over.
