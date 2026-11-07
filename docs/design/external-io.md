# External I/O: files, formatting and local storage

The gzip translations need file operations, `errno`, strings and formatted output in addition
to the object heap. Their implemented model is
[`gzfs.lean`](../../ZlibF/Zlib/gzfs.lean), beside the translated C files. It belongs to the
trusted base. [Gzip source notes](../proof/gzip.md) explain the library control flow;
[API contracts](../api/README.md) define the intended public behavior.
[Overview](../overview.md) is the status and remaining-work record.

## Files and heap effects

A computation has type `G α = StateT Fs C.M α`. `Fs` is separate from `Heap`; a computation
returns both updated states or a runtime fault. Paths are flat byte strings. Nodes hold byte
arrays or a directory marker. Each open descriptor stores a node, position and read/write/
append flags. Allocation starts at descriptor 3 and chooses the lowest free represented slot.

| Operation | Implemented behavior |
| --- | --- |
| `open` | Read or write mode; creation, exclusion, truncation and append are represented. Invalid modes and modeled path failures set `errno` and return `-1`. |
| `read` | Copies the requested regular-file bytes up to EOF. Invalid descriptors, wrong access mode and directory reads fail. There is no independent short-read or failure oracle. |
| `write` | Writes at the position or end in append mode. Seeking past EOF makes a later write fill the gap with zeros. Crossing `fsizeLimit` gives a short write; writing at the limit fails with `EFBIG`. |
| `lseek` | Supports set/current/end offsets, rejects negative results and results above `2^63 - 1`. |
| `close` | Releases the represented descriptor; invalid descriptors fail. |
| `fcntl` | No effect in this model. |
| `errno` and `strerror` | An explicit integer plus a table of represented error texts. Successful calls preserve `errno`; the library's explicit resets are separate effects. |

The world does not represent pipes, sockets, terminals, signals, concurrent file changes,
permissions, directory traversal, links or descriptor sharing through duplication.
`O_NONBLOCK`, `O_CLOEXEC` and `O_LARGEFILE` have no modeled effect. In particular, regular
reads cannot set `again` through `EAGAIN`, fail after a positive partial read, or expose all
cleanup paths of a broader I/O oracle. Write failures chiefly model the file-size limit;
they do not cover arbitrary `EIO`, `EINTR` or `ENOSPC` behavior.

These are limits of the external-world representation. The older design for an arbitrary
POSIX-result oracle, shared open-file descriptions and progress assumptions was a proposal.
It is not implemented by `Fs`. A theorem over this model alone does not establish safety
for every external behavior allowed by the C API.

C string literals use the runtime's static read-only blocks. `strerror` text instead uses
`libcStr`, which creates a fresh read-only allocation and does not free it. This represents
external-library storage, but an exact live-block claim must account for those allocations;
it cannot silently count them as owned gzip buffers or assume they do not exist.

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

For represented valid formatting, `vsnprintf` writes at most `capacity - 1` text bytes plus
NUL and returns the untruncated length, as in the selected C99 path. A result longer than
`INT_MAX` faults in the model. The gzip wrapper still
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
and [overview](../overview.md), rather than a second test-history list here.
