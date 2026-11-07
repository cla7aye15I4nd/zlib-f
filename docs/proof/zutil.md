# Utilities: allocation and constant queries

Sources: `zlib/zutil.c` and `zlib/zutil.h`; translation:
`ZlibF/Zlib/zutil.c.lean`. These functions support both stream implementations.
Their public contracts are in the [API guide](../api/README.md), and their
ownership role is defined in [safety](../safety.md).

The default LP64 allocator branch uses `malloc`, despite the name `zcalloc`.
It does not zero the block. Initialization proofs must establish the field
writes they need, including pointer writes that the model does not track.

## Size arithmetic at callers

`zcalloc(opaque, items, size)` computes `items * size` in 32-bit `unsigned`
arithmetic in this branch. Its wrapper theorem must describe that product
faithfully. A caller expecting the ordinary product must prove it is below
`2^32` before relying on the allocated capacity.

| Default stream allocation | Largest product in bytes |
| --- | --- |
| `deflateInit2_` state | LP64 `sizeof(deflate_state)` |
| Compressor window: `w_size * 2` | 65536 |
| Compressor `prev`: `w_size * sizeof(Pos)` | 65536 |
| Compressor `head`: `hash_size * sizeof(Pos)` | 131072 |
| Compressor pending buffer: `lit_bufsize * 4` | 131072 |
| `inflateInit2_` state | LP64 `sizeof(inflate_state)` |
| Decoder window: `(1U << wbits) * 1` | 32768 |
| `deflateCopy`, `inflateCopy` | Corresponding state and buffer sizes above |

The state sizes must come from the selected ABI layout and agree with the C
layout checks. They are not mathematical constants across configurations. The
buffer bounds derive from validated parameters and the size equations retained
in the stream invariant. This table concerns the stream allocations shown; it
does not assert a maximum allocation for every gz or other API path.

## Success and failure effects

On success, allocation adds a fresh live block of the modeled size. On failure,
it returns null and adds no live block. Neither case makes a new pointer field
safe to read before it has been written. Uninitialized integers have arbitrary
values under [the runtime rules](../safety.md#uninitialised-memory).

`zcfree` accepts null or a block permitted by the allocator interface. A non-null
free requires the corresponding live ownership claim. End and failure-cleanup
proofs must supply it exactly once. The heap stores liveness and allocation
history; the proof's `Owns` relation assigns the live blocks to a stream.

`deflateInit2_` allocates a state and four buffers. Its combined buffer-failure
check comes after the buffer allocations, so a failed earlier allocation does
not imply that later ones were never attempted. Cleanup must free all successful
allocations of that attempt, clear or preserve fields as the source specifies
and restore the previous live-block set. `inflateInit2_`, delayed decoder-window
allocation and both copy functions need their own failure-case compositions.
The allocator wrapper alone proves none of that lifecycle cleanup.

## Constant and error queries

| Function | Required result and frame |
| --- | --- |
| `zError(err)` | The out-of-range branch selects entry 9. Otherwise `-6 ≤ err ≤ 2`, so `2 - err` is in `[0, 8]` without signed overflow. Return the exact entry of the ten-element message table; preserve the heap. |
| `zlibVersion` | Return the selected version string pointer with the static contents required by the contract; preserve the heap. |
| `zlibCompileFlags` | Derive the exact numeric flags from the selected type widths and enabled source branches; preserve the heap. |

A constant return is still an exact contract: a wrong version pointer or changed
flag bit must fail the function's proof mutant. Earlier documentation classified
these wrappers as complete in a prior model. Present results require the exact
goal, registration, mutation evidence and reviewed CI described in
[checking](../checking/README.md). See [the overview](../overview.md) for that
current checkpoint.

## C correspondence checks

`zError` checks the error range before evaluating `2 - err`. Hoisting subtraction
could overflow for an arbitrary `int`. `zlibCompileFlags` yields 169 for the
reviewed configuration; retain its source decisions rather than treat that
number as universal. Returned version and error strings are read-only statics.
