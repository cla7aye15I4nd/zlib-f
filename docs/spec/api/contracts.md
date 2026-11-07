# How to read a contract

[API manual](README.md) · [Shared stream rules](streams.md)

A contract answers three questions: what must the caller supply, what can the caller
rely on at return, and what can change during the call? Read the page's common rules
before an individual entry. They supply memory, lifetime and build assumptions that
would otherwise repeat under every function.

## Entry structure

| Part | Meaning |
| --- | --- |
| C signature | The function's C name and parameter types, with declaration macros retained. |
| Purpose | The operation the caller is trying to perform. |
| Domain | Which values, objects and call histories this contract covers. |
| Pre | Conditions required before the call, including any checked rejection cases. |
| Post | The result and guarantees on each stated return path. |
| Effects | Reads, writes, allocations, frees, file operations and borrowed storage. |
| Edges or errors | Cases such as empty input, partial output and refusal that change how to use the result. |

An error return does not generally undo work. Output, pointer advances, length cells or file
position can already have changed. Follow the stated return path and effects. In particular,
a decoding allocation failure can follow partial output.

## Domain and effects are independent

A **Restricted domain** requires more than values of the parameter types. A pointer must
usually name live storage; a handle needs a legal call history; a checksum combination
may require an operator produced for the correct length.

A **Full type domain** covers every value of the parameter types in the selected build,
including specified refusals. A function covering every scalar value can still have a
restricted overall domain because its pointers must refer to valid storage. Finite versus
infinite, or bounded versus unbounded, is not the distinction.

| Effect | Meaning |
| --- | --- |
| Pure computation | Computes a result without reading caller memory or changing state. It may use fixed library constants or tables. |
| Read-only | Reads caller memory or stream state and preserves it. A borrowed result remains library-owned. |
| Stateful | May write caller destinations or library state, allocate or free storage, invoke callbacks, or perform file I/O. |

These labels describe different properties. A pure computation can have a restricted domain.
A query that writes an optional scalar result has a write effect even if its stream is unchanged.

## Example: combine two CRCs

`crc32_combine_op` avoids reading the original strings again:

```text
Domain: Restricted domain.
Pre: crc1 is the CRC of A; crc2 is the CRC of B;
     op was generated for the representable nonnegative length of B.
Post: the result is the CRC of A followed by B.
Effects: pure computation.
```

The CRC of A means `crc32` on A, started at zero. A and B are ordinary byte sequences;
no special CRC type is required. The generated operator and correct length matter even
though the call reads no caller memory. See the [checksum entries](checksums.md) for
zero and negative-length cases, and the [format model](../format/README.md) for agreement
with the standard.

## Shared reading rules

Unless an entry states otherwise, use the default LP64 Linux static build and default
allocator. Readable and writable ranges contain the stated number of bytes for the full
call. Lengths fit their parameter types. A live handle was initialized, has not been
closed, and is used sequentially without caller modification of its owned state.

Under Pre, the contract requires execution to terminate without undefined behaviour,
satisfy Post, and change only the stated footprint. Allocation failure, partial results and
cleanup are part of that requirement. [Shared stream rules](streams.md) explain the
common ownership and frame obligations; [safety](../safety.md) defines the modeled faults.

These are focused documentary contracts. A narrower Pre neither changes the registered
Lean goals nor makes excluded calls undefined. See [scope deviations](../../deviations.md) and
[registered public goals](../../checking/goals.md). Source readings are **to confirm** by proof.
Proof status and remaining work are recorded only in [overview](../../overview.md).
