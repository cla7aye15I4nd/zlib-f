# External I/O: files, formatting and local storage

The gzip translations need file operations, `errno`, strings and formatted output in addition
to the object heap. Their implemented model is
[`gzfs.lean`](../../ZlibF/Zlib/gzfs.lean), beside the translated C files. It belongs to the
trusted base. [Gzip source notes](../proof/gzip.md) explain the library control flow;
[API contracts](../spec/api/README.md) define the intended public behavior.
[Progress](../progress.md) is the status and remaining-work record.

## Files and heap effects

A computation has type `G α = StateT Fs C.M α`. `Fs` is separate from `Heap`; a computation
returns both updated states or a runtime fault. Paths are flat byte strings. Nodes hold byte
arrays or a directory marker. Each open descriptor stores a node, position and read/write/
append flags. The regular-file `open` starts at descriptor 3 and chooses the lowest free
represented slot; the OS-call oracle may choose any other free number. A descriptor is a C `int`:
when no descriptor below `2^31` is free, `open` fails with `EMFILE`.

| Operation | Implemented behavior |
| --- | --- |
| `open` | Regular: read or write mode; creation, exclusion, truncation and append are represented. Invalid modes and modeled path failures set `errno` and return `-1`. When no descriptor below `2^31` is free, `-1` with `EMFILE`, before anything is created or truncated. Oracle: `-1` with any nonzero errno before anything is created, or the new descriptor moved to any free number below `2^31`. |
| `read` | Regular: copies the requested regular-file bytes up to EOF, cut to the read budget. Invalid descriptors, wrong access mode and directory reads fail. Oracle: `-1` with any nonzero errno, or any `k ∈ [0, n]` bytes of arbitrary data within the budget, whatever the descriptor's state. |
| `write` | Regular: writes at the position or end in append mode. Seeking past EOF makes a later write fill the gap with zeros. Crossing `fsizeLimit` gives a short write; writing at the limit fails with `EFBIG`. Oracle: `-1` with any nonzero errno, or any count in `[1, n]` (0 for an empty buffer) without changing the file. |
| `lseek` | Regular: supports set/current/end offsets, rejects negative results and results above `2^63 - 1`. Oracle: `-1` with any nonzero errno, or any value in `[0, 2^63 - 1]` without moving the descriptor. |
| `close` | Regular: releases the represented descriptor; invalid descriptors fail. Oracle: `-1` with any nonzero errno, the descriptor released anyway. |
| `fcntl` | No effect in this model. |
| `errno` and `strerror` | An explicit integer plus a table of represented error texts. A successful call may leave any errno the oracle chooses (`okErrno`); the library's explicit resets are separate effects. |

The OS-call oracle fields of `Fs` (`nos`, `readChoice`, `writeChoice`, `lseekChoice`,
`closeFail`, `openFail`, `openFd`, `okErrno`, `readBudget`) choose each call's result within
that contract; the defaults reproduce the regular-file model and serve the executable drivers
only. Every oracle value is mapped into the contract (cut or clamp, never reject), so every
world is legal and `FileSystem` constrains only the regular-file part. The oracle covers the
behaviours of pipes, sockets, devices, signals (`EINTR`), nonblocking descriptors (`EAGAIN`),
transient failures and concurrent file changes on each call, without representing those objects.
It is deliberately wider than any real system ([trusted base](../trusted-base.md)). The
regular-file part still does not represent permissions, directory traversal, links or descriptor
sharing through duplication; `O_NONBLOCK`, `O_CLOEXEC` and `O_LARGEFILE` have no regular-file
effect.

C string literals keep their original closed table and indices. `strerror` text uses a
separate borrowed read-only view in the static-string suffix. It creates no malloc object
and does not change the live-allocation ledger or allocation oracle. The fixed Linux errno
text includes the same fallback for every Int32 value.

Each call advances an external borrow epoch. Only the current borrowed pointer is readable;
a later call invalidates the earlier pointer, even for the same errno. This models sequential
invalidation. Thread exit, concurrent calls and locale changes are not represented. The four
translated call sites pass the borrowed pointer directly to `gz_error`, which synchronously
copies into its own message allocation and never stores or frees the borrowed pointer.

A malloc-object frame alone does not preserve volatile external views. Internal proof rules
must establish borrow stability from the actual operation, or use a persistent source view.
Public caller domains and exact no-new-live close requirements are unchanged.

`storeBytes`, used for read and formatting results, copies via a temporary byte block and
frees that block. Its result is a block copy rather than a sequence of byte stores.
`memchrB` stops at the first matching byte. Memory operations still check object bounds,
read-only destinations and overlap where relevant. Invalid user buffers raise a model fault;
this is not a complete model of the operating system's `EFAULT` behavior.

## Formatted output

Variadic arguments are represented values in `VaArg`, with signed/unsigned 32- and 64-bit
integers and byte-string pointers. `gzprintf` receives that list and delegates to `gzvprintf`.
The ABI storage of a C `va_list` is not represented.

The formatter supports `%%`, `%c`, `%s`, `%d`, `%i`, `%u`, `%x`, `%X` and `%o`, flags
`-0+ #`, decimal width and precision, and length modifiers `l`, `ll`, `z`, `j` and `t`.
Unsupported conversions include floating point, `%p`, `%n`, `%*d`, `%hd` and `%ls`.
Unsupported syntax or mismatched/missing argument kinds faults. Unsigned conversions also
accept the corresponding signed argument kind and reinterpret its bits. There is no implemented
fallback that returns arbitrary formatting bytes. The older proposal's `h`/`hh`, dynamic
width and demonic fallback must not be read as supported behavior.

The model has two operations, as the C has two functions. `snprintf` serves the fixed formats
of `gz_error`, `gz_open` and `gzdopen`: it is deterministic, writes at most `capacity - 1` text
bytes plus NUL, and returns the untruncated length, or -1 when that length exceeds `INT_MAX`.
`vsnprintf` serves `gzvprintf`'s caller format: it behaves the same, except that any call may
fail through a world oracle (`printfOk`). A failed call returns -1, sets a nonzero `errno` and
leaves arbitrary bytes and a NUL inside the buffer. [Trusted base](../trusted-base.md) gives the
glibc evidence. The gzip wrapper still
performs its own length and sentinel tests, then its own buffer-vacate and error handling.
A formatting model is not a callee contract that may replace those effects. See
[deviations](../deviations.md) for the public representation limit.

## Pointer and local-storage choices

`GzFilePtr` identifies the `x` prefix of its owner; `castState` recovers that owner.
`strmOf` identifies the embedded stream. Field writes load and update that same record.
This preserves identity for codec backlinks and shared public fields.

Caller scalar pointers such as `gzerror`'s optional `int *errnum` and `uncompress2`'s length
outputs are little-endian byte blocks, accessed with four- or eight-byte loads and stores.
`gz_load`'s internal `unsigned *have` instead becomes a returned value, stored by each caller
on success and failure. The C callee does not observe that target through another alias;
**to confirm** the same effect order for every represented call site.

Address-taken local bytes, local streams and scalar output storage use local allocators that
do not consume the caller allocation-failure oracle. They must be released on every return.
This applies to `gzgetc`/`gzputc`'s one-byte buffers and the convenience decompressor's local
stream and length cells. Signed file-position arithmetic uses checked 64-bit operations.
The modeled allowance for null-plus-zero arithmetic does not justify using a dangling pointer.

The translated files preserve the source's missing `x.next` initialization, partial-read
assignment order, direct-buffer pointer retention and seek arithmetic. Historical reports and
proposed fixes are separated in [gzip proof guide](../proof/gzip.md). No gzip patch is applied here.

## Differential evidence

The gzip differential cases are defined by [`tests/gen/gz.py`](../../tests/gen/gz.py),
[`tests/c/gz.c`](../../tests/c/gz.c) and
[`tests/lean/Driver/Gz.lean`](../../tests/lean/Driver/Gz.lean).
They compare operation observations on temporary real files with runs over `Fs`.
The same family compares `uncompress2` bytes and lengths.

Agreement checks the translation and its external model together against selected C
executions. It is evidence of fidelity, not proof of codec correctness, all error paths,
all POSIX behaviors or leak freedom. The restricted file model cannot generate the
partial-success/read-failure counterexample described in [gzip proof guide](../proof/gzip.md).
Run results and acceptance requirements belong in [checking](../checking/README.md)
and [progress](../progress.md), rather than a second test-history list here.
