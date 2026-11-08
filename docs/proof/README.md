# Implementation proof reference

For the first reading, follow the [illustrated guide](../overview.md). Its chapters
explain the algorithms and API uses together with their proof obligations.
This section supplies the detailed arguments by C component.

This guide explains the arguments that connect the translated C to zlib's contracts.
It separates mathematical lemmas, memory reasoning and composition across calls.
The pages are proof plans and explanations. An argument in prose is not a
kernel-checked theorem, and a theorem about a model is not yet a theorem about the
translated function.

Read [progress](../progress.md) for the current checkpoint and the single list
of remaining work. Read [safety](../spec/safety.md) for the properties being claimed and
[checking](../checking/README.md) for the evidence needed to accept a result.
Historical proof names below help locate earlier arguments. They do not certify
the present source, runtime or caller domain.

## Choose a reading path

For the overall method, start with [proving one function](method.md). It explains
contracts, invariants, framing, ownership and the diagnosis of a stuck proof.
Then read the [API contracts](../spec/api/README.md), the
[format specification](../spec/format/README.md) and the
[design guide](../design/README.md) as the function requires.

For decompression, read the checksum and allocator pages, then table construction,
the fast decoder and the main decoder. The main decoder must establish the fast
path's entry conditions. Table construction must establish the predicates that
both decoders use.

For compression, read the checksum and allocator pages, then window and hash-chain
reasoning in `deflate.c`. Read `trees.c` for tree construction, bit emission and
the shared output/symbol buffer. The overlay bound is part of memory safety.

| Source | Guide | Main argument |
| --- | --- | --- |
| `adler32.c` | [Adler-32](adler32.md) | Modular sums, bounded batches and exact start-value scope |
| `crc32.c` | [CRC-32](crc32.md) | Braided reads, address semantics and polynomial refinement |
| `zutil.c` | [Utilities and allocation](zutil.md) | Allocation sizes, failure, ownership and constant queries |
| `inftrees.c` | [Decode tables](inftrees.md) | Canonical codes, table capacity, coverage and entry meanings |
| `inffast.c` | [Fast decoding](inffast.md) | Input/output margins, copies, rollback and source bits |
| `inflate.c` | [Stream decoding](inflate.md) | Modes, history, dictionaries and composition across calls |
| `deflate.c` | [Stream compression](deflate.md) | Window bounds, initialized chains, strategies and lifecycle |
| `trees.c` | [Trees and block emission](trees.md) | Heap construction, length repair, codes and overlay prefixes |
| `infback.c` | [Callback decoder](callbacks.md) | Window ownership, input finiteness and callback effects |
| `gz*.c` | [Gzip files](gzip.md) | Lazy allocation, I/O pipelines, positions and cleanup |
| `compress.c`, `uncompr.c` | [Buffer utilities](buffers.md) | Automatic locals, scalar outputs, bounds and error mapping |

The single [target graph](../progress.md#proof-progress-graph) shows actual
proof references as solid arrows and C calls as dotted arrows. [The evidence index](../progress.md) separates those references
from C calls and specification dependencies. A caller establishes each actual
callee precondition; it need not assume a complete general-parameter API goal.
The [input-range guide](../spec/input-configurations.md) also distinguishes strategy
selection from the decoder's buffer-driven fast/slow dispatch.

## Read a component page

Each page identifies its source and contract vocabulary, then explains the
invariants and lemmas the function needs. A stated bound is conditional on the
premises written beside it. The public theorem must obtain those premises from
initialization, preceding calls and the documented caller requirements. It cannot
assume a callee contract or discard a legal API case.

A source reading that still needs proof is marked **to confirm**. The identifiers
`U1`–`U12`, `F1`–`F9` and `I-*` link the reasoning to the safety document, method
and internal contracts. They describe obligations, not acceptance status.

Intervals `[a, b)` include `a` and exclude `b`. An array pointer may be formed at
its one-past position; that position may not be read. Unsigned operations wrap as
in C. A proof that needs ordinary arithmetic must establish that wrapping does
not change the relevant value.

The guide follows the default x86_64 Linux build first. A bound derived from that
build's widths, tables or allocator branch must be revisited for another
configuration. The [trust boundary](../trusted-base.md) and
[deviations](../deviations.md) remain part of every claimed result.

## Source correspondence and earlier arguments

Each component owns its file-specific C correspondence checks. Shared integer,
object and control-flow rules stay in [translation semantics](../design/translation.md).
The gzip world has one [external-I/O definition guide](../design/external-io.md).
The [reference appendix](references.md) retains earlier theorem-family mappings
and historical experiments with their evidence limits. None supplies missing
proofs or a second current-status list.
