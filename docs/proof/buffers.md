# Buffer utilities and output bounds

Source: `compress.c`, `uncompr.c` and the bound entries in `deflate.c`.
Read the [API contracts](../spec/api/utility.md) for caller obligations and
[overview](../overview.md) for accepted scope and remaining work.
This guide records source correspondence and composition obligations, not
complete buffer-utility proofs.

## Bounds and buffer utility wrappers

`compressBound_z` uses wrapped additions and a saturation test. A proof of the
formula alone does not show that every compressor output fits it.
`deflateBound_z` also reads wrapper state and optional header strings. Each
scan includes the terminating null. It normalizes a negative `wrap` after
finishing and retains every overflow guard.

The historical `deflateBound_z` header issue concerns correctness, not signed
overflow: `2 + extra_len` is evaluated as 32-bit unsigned before addition to the
64-bit wrapper cost. For `extra_len >= 0xfffffffe` it wraps, whereas emission
uses only `extra_len & 0xffff`. The earlier proposed correction used
`2 + (z_size_t)(extra_len & 0xffff)`
([upstream discussion](https://github.com/madler/zlib/pull/1360)). This history
does not authorize an unlisted patch. **to confirm**: the output bound follows
for its stated source and header domain.

`compress2_z` and `uncompress2_z` have automatic local streams. Creating them
must not fail, consume an allocator-oracle call or shift the failure index of
library allocations. Address-taken scalar locals also have automatic lifetime.
Model storage is released on every source return without adding a C allocation.
The [allocation regression](../../tests/regression/compress-allocation/README.md)
records the corrected distinction and error-ordering observations.

The utility loops refill 32-bit availability fields from wider remaining
lengths. They continue only on `Z_OK`, call `End` after successful initialization,
and retain result mapping and final scalar writes. Late decoder memory failure
can follow emitted output; it does not imply an empty destination.

Two named decisions from the original review remain relevant:

- **R-2, wrapper null reads.** `compress2` reads `*destLen` before its `_z` call;
  `uncompress2` reads both scalar cells. The `_z` null tests cannot protect those
  reads. Separate execution witnesses diagnosed them. They are not valid-call
  comparison rows.
- **D-4, null subtraction.** `compress2_z` computes `next_out - dest` after a
  zero-capacity null destination. Its translation explicitly allows null minus
  null to be zero. Whether that matches the selected C language semantics is
  **to confirm**. Equal results and silent sanitizers cannot settle it.

The compressor adapter represents its length pointer as an optional input and a
returned value. It cannot express aliases with byte buffers. Counted
decompressor adapters also have scalar separation limits. See
[deviations](../deviations.md); these limits do not settle the full C domain.

`uncompress2_z` uses the address of its local stream's `reserved` field as a
non-null dummy output at zero capacity. A separate represented byte can model
that use only if it is never dereferenced and its lifetime and aliasing are
accounted for. **to confirm**: zero capacity excludes a write through it during
the actual decoder call.

