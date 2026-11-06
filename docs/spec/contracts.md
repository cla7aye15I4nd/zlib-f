# Function contracts

A function entry keeps its C signature, purpose, **Pre**, **Post** and **Effects**.
Add only edge cases that change the result or allowed use.

## Domain

| Term | Meaning |
| --- | --- |
| Restricted domain | Inputs satisfy conditions beyond their C types, such as a live handle or a generated operator. |
| Full type domain | Every value of the parameter types is covered in the selected build, including specified error returns. |

These describe contracts. One function can have contracts with different domains.
An exported API is not automatically a full type domain. A full 32-bit domain
is finite, so bounded versus unbounded is not this distinction.

## Effects

| Kind | What to describe |
| --- | --- |
| Pure computation | The result; no caller-memory reads or state changes. Fixed library constants may be used. |
| Read-only | The result and readable memory or state; nothing changes. |
| Stateful | The result, permitted memory/state changes, and resource or file effects. |

Effects and domain are independent. A pure computation can have a restricted domain.

## Example

`crc32_combine_op` combines two CRCs without reading the strings again:

```text
Domain: restricted domain
Pre: crc1 is the CRC of A; crc2 is the CRC of B;
     op was generated for the representable nonnegative length of B.
Post: result is the CRC of A followed by B.
Effects: pure computation.
```

The CRC of A means `crc32` on A, started at zero. No special CRC type is needed.
The format specification separately defines agreement with the standard.

## Shared rules

- Use the default LP64 Linux static build and default allocator unless stated otherwise.
- Ranges contain the stated readable or writable bytes; lengths fit their parameter types.
- Live handles were initialized, not closed, and used sequentially without caller changes to owned state.
- Under Pre, the required execution returns without undefined behaviour and changes only its stated effects.
- Keep allocation failure, partial results and cleanup explicit; an error does not imply unchanged output.

The short manuals intentionally describe focused uses. Their Pre conditions may be
narrower than `zlib.h`; outside Pre is outside this contract, not automatically undefined C.
See [deviations.md](../deviations.md). Broader registered targets stay unchanged:
[public-goals.md](public-goals.md). These are obligations, not completed proofs.
Source readings awaiting proof are **to confirm**. Algorithm explanations stay with
source or proof notes; remaining work is listed only in [overview.md](../overview.md).
