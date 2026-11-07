# Proof migration records

These records explain how earlier proof arguments map to this repository. They are working
technical references, not a second progress tracker. [Overview](../overview.md) owns the current
checkpoint, blockers and remaining work. [Proof guide](../proof/README.md) describes the present
proof structure. [Acceptance checks](../checking/README.md) define when a result counts here.

| Record | Scope |
| --- | --- |
| [Inflate](inflate.md) | Main decoder modes, bit macros, loop and history refinement |
| [Inflate tables and trailer](inflate-table-check.md) | Dynamic-header loops, table-content boundary and checksum epilogue |
| [Deflate engine](deflate-engine.md) | Hash chains, window movement, match search and pending bytes |
| [Deflate lifecycle](deflate-lifecycle.md) | State invariant, allocation, reset, copy, priming and queries |
| [Callback decoder](infback.md) | Callback ownership, finite-input measure and window output |
| [Gzip file management](gzlib.md) | File-state records, seeking, errors, opening and close dispatch |

The source reference is pinned in [reference material](../history/references.md). The old heap
used tagged cells and byte blocks. The present heap uses records and tables for each object kind.
Pure arithmetic and bitstream arguments can retain their mathematical meaning. Heap-level
statements require new proofs about the actual translation and runtime.

```mermaid
flowchart LR
    S[Earlier argument] --> P[Separate pure facts from memory reasoning]
    P --> T[Restate against the present translation]
    T --> K[Kernel check, audit and function mutants]
    K --> A[Acceptance on a named commit]
```

A theorem name or source module below is a navigation aid. It does not certify that a current
public goal has been accepted. Historical line counts describe the old effort or a recorded
experiment; they are not new measurements. No migrated proof may assume a library callee's
contract. The callee must have a theorem about its translated implementation. Init must establish
the shared invariant before conditional preservation results support API-sequence safety.
