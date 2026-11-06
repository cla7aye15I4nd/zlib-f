# Safety claims and caller obligations

The goal is that every call permitted by `zlib.h` avoids undefined behaviour, returns,
and preserves memory ownership. This is a target, not a claim that all functions are proved.
[Overview](overview.md) records checked status and remaining work. The [proof method](proof/method.md)
explains how these obligations become Lean theorems. [Trusted base](trusted-base.md) describes
where the model needs a separate argument before a model result applies to C.

## 1. What a function theorem must say

For every admitted caller state and argument, the translated function returns without a fault.
It preserves the shared representation invariant, changes only its permitted memory, and
accounts for every allocation and free. Error returns are included.

| Clause | Required conclusion |
| --- | --- |
| No fault | The run has a result, rather than `Fault.ub` or `Fault.outOfFuel`. |
| Preservation | The next legal call can use the same representation invariant. |
| Frame | Memory outside the call's footprint is unchanged. |
| Ownership | The live blocks owned by the stream change exactly as allocation and freeing require. |

Initialisation must establish the invariant from the admitted caller state. A callee contract
is a proved theorem about that callee; it cannot be assumed to discharge a caller's proof.
A top-level theorem also needs a concrete witness. Neither a witness nor an unsatisfiable
invariant can substitute for coverage of all admitted arguments.

```mermaid
flowchart LR
    I[Init] -->|establishes| V[Shared invariant]
    V --> A[Legal API call]
    A -->|preserves| V
    V --> E[End]
    E --> Z[No stream-owned live blocks]
    I -->|allocation failure cleanup| Z
```

Leak freedom concerns the whole lifetime. Successful init leaves its allocations owned by
the stream. End frees each owned block exactly once. Failed init frees everything it allocated.
The live-block set after end or failed init equals the set before init. Copy and partial-failure
paths need the same accounting. A failed operation must leave a state in which the documented
recovery or end operation is safe.

## 2. Calls and sequences

Sequence safety is part of the goal. It follows by induction only after init establishes the
invariant and every permitted transition preserves it. This includes reset, dictionaries,
priming, copy, recovery and end. A collection of isolated function lemmas is insufficient.

Termination means that every loop completes before its fuel limit. The runtime uses `2^64`
iterations; exhausting it is a separate fault. Termination and leaks are safety obligations here,
even though neither is itself an instance of C undefined behaviour.

## 3. Faults, undefined behaviour and model gaps

The identifiers below name the safety obligations. Runtime faults detect many violations.
They do not alone establish C safety: the exceptions in this section and
[trusted-base.md, item 2](trusted-base.md#2-runtime-and-object-schema) remain part of the argument.

| ID | Obligation | Main reason it matters |
| --- | --- | --- |
| U1 | No read or write outside an object | Buffer indices and table accesses need bounds. |
| U2 | Pointer arithmetic stays within an object or one past it | Offset updates and back-reference copies need live, bounded pointers. |
| U3 | No null dereference | Stream, state, window and header accesses need the appropriate live pointer. |
| U4 | No use after free or double free | Ownership must persist through copy, failure and end. |
| U5 | No invalid use of uninitialised data | Garbage must not become an unchecked index or address; pointer fields need a write-before-read argument. |
| U6 | No signed overflow | Counters, positions and conversions need explicit range checks. |
| U7 | No invalid shift | Counts must be nonnegative and below the promoted operand's width. |
| U8 | No write to a read-only object | Static data and immutable byte blocks must remain unchanged. |
| U9 | No overlapping `memcpy` | Copies need disjoint ranges; overlapping copies use `memmove`. |
| U10 | Accesses respect C type and alignment requirements | The object heap has no general byte view of records, type tags or complete ABI layout. CRC word reads need separate review. |
| U11 | Every call terminates | Loop measures must rule out fuel exhaustion. |
| U12 | No memory leak | Every exit must preserve ownership or perform exact cleanup. |

Unsigned arithmetic wraps in the translation. Signed arithmetic and shifts are checked by
the translation's operations, rather than automatically by the computation monad.
`Ptr.add` permits `NULL + 0`. `Ptr.diff` rejects null operands, while the compressor's
`ptrDiff` helper returns zero for two null pointers. These are model choices, not evidence
that the corresponding C expressions have defined semantics.

### Uninitialised memory

Fresh integer cells contain arbitrary values from `Heap.garbage`. A theorem must hold for
every garbage function. The model assigns one fixed value to each cell for the run; repeated
reads agree. It does not model a fresh unspecified value at every read. A proof must not use
that agreement to justify C behaviour. Copying bytes copies these values, including garbage.

This matters in `slide_hash`, which visits uncleared `prev` entries, and `longest_match`,
which compares bytes beyond the real input data. Their source comments explain the intended
independence from those contents. That reading is **to confirm** by the relevant execution
proofs. Arbitrary-value quantification alone does not prove output independence or that a
hash-chain walk reaches only entries written with real positions.

Fresh pointer fields are NULL in the model. This is weaker than tracking an uninitialised
pointer: comparison with NULL, copying and `free(NULL)` succeed without detecting a missing
write. Every pointer field read therefore needs evidence of an earlier write. The two state
init translations explicitly zero their allocated state records. This does not initialise
all caller or automatic stream records. The compressor's automatic stream starts with
arbitrary integer fields and model-null pointers; its field writes must follow the C.

### Object representation

Declared record-array lengths require `WellFormed` and `Heap.RecordsWellFormed` hypotheses.
Static lengths require `Statics.WellFormed`, and values must match the translated C tables.
A Lean `Array` type does not enforce its C extent. Allocation requires `Fresh` and a valid
cross-table block identity discipline. No initialisation bits or allocation-origin tags are
present. Read-only flags cover byte blocks and represented statics, not all typed objects.

Pointer equality uses object identity and offset. Different objects compare unequal, and
comparing a dangling pointer does not fault. A proof must not depend on those outcomes where
C does not guarantee them. The CRC address helper represents only heap byte blocks, using
their offsets as addresses. Static and embedded objects, alignment and scalar-cell aliases
need the limits recorded in [deviations](deviations.md).

## 4. Caller obligations

A public theorem must state these obligations explicitly and distinguish invalid arguments
that require a clean error return from inputs outside the C API's domain.

| ID | Obligation or scope |
| --- | --- |
| A1 | A non-null stream argument denotes a live `z_stream`; allocator fields are set as required before init. Null cases documented as refusals remain covered. |
| A2 | The caller provides the readable input and writable output ranges required by the operation. |
| A3 | Buffer separation follows the entry's explicit precondition. A universal separation requirement attributed to `zlib.h` is **to confirm**; stronger restrictions belong in [deviations](deviations.md). |
| A4 | Calls on the same stream are not concurrent. |
| A5 | The initial target uses the default allocator. Its allocation failures remain in scope. |
| A6 | Use after end or close is excluded; documented reinitialisation starts a new lifetime. |
| A7 | Every scalar value is classified: documented normal use, documented refusal, or an explicit caller restriction. Invalid values cannot be silently omitted to avoid checking error paths. |

## 5. Other properties

Functional correctness is also required: see the [format](format/README.md) and
[API contracts](api/README.md). Malformed input remains in the safety domain; an error return
must not hide a fault. Custom allocators and other upstream configurations follow the initial
default x86_64 Linux/LP64 static build target. Compiler and operating-system correctness,
performance, stack bounds and resource limits against decompression bombs are outside the
model. The [trusted base](trusted-base.md) records these boundaries.
