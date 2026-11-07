# Checksums

[API manual](README.md) · [Contract conventions](contracts.md) · [Buffer utilities](utility.md)

Compute a checksum a buffer at a time, or combine the checksums of independently processed
byte sequences without rereading them. The byte sequences A and B below are ordinary data;
the contracts use the Adler-32 or CRC-32 of those sequences.

| Task | Entries |
| --- | --- |
| Update Adler-32 | [Size-type length](#adler32_z), [32-bit length](#adler32) |
| Combine Adler-32 | [Ordinary offset](#adler32_combine), [explicit 64-bit offset](#adler32_combine64) |
| Update CRC-32 | [Size-type length](#crc32_z), [32-bit length](#crc32) |
| Combine CRC-32 | [Ordinary offset](#crc32_combine), [explicit 64-bit offset](#crc32_combine64) |
| Reuse a CRC combination operator | [Generate](#crc32_combine_gen), [generate with 64-bit length](#crc32_combine_gen64), [apply](#crc32_combine_op) |
| Inspect the byte table | [get_crc_table](#get_crc_table) |

These focused contracts follow `adler32.c`, `crc32.c` and `zlib.h` in the default LP64 Linux
static build, with the pinned source and listed patches. Source readings are **to confirm**
by proof. No checksum entry writes state, allocates, frees or performs I/O. Exceptional
numeric results are ordinary values, rather than error codes. Domain and effects remain
independent as explained in [contract conventions](contracts.md).

The practical checksum contracts use actual byte sequences A and B. Each
checksum is computed independently, starting at 1 for Adler-32 or 0 for CRC-32.
These contracts deliberately omit functional promises for forged checksums.
The [Lean targets](../../../ZlibF/Spec/Public/Checksums.lean) also describe arbitrary
seeds and exact scalar results. Both the Adler entries and their Lean targets
require zero length for NULL initialization queries.
See [scope deviations](../../deviations.md) and [public goals](../../checking/goals.md).

In this build, `uLong` and `z_size_t` are unsigned 64-bit types; `uInt` is
unsigned 32-bit. `z_off_t` and `z_off64_t` are signed 64-bit. Input checksum bits
above bit 31 are ignored; returned checksums fit in 32 bits. The explicit
`*64` declarations depend on the header's large-file feature macros.

## adler32_z

```c
uLong ZEXPORT adler32_z(uLong adler, const Bytef *buf, z_size_t len);
```

Update an Adler-32 checksum with a byte range, or obtain its initial value.

**Domain.** Restricted domain. Effects: **read-only** when `buf` is non-NULL.

**Pre:** Either `buf` is NULL and `len == 0`, or it points to `len` readable
bytes. For the checksum postcondition, the low 32 bits of `adler` are the Adler-32 of A.
There is no setup or cleanup requirement.

**Post:** A NULL, zero-length query returns 1 for every `adler`, without reading
bytes. Otherwise return the Adler-32 of A followed by `buf[0..len-1]`.
A non-NULL zero-length range returns the incoming checksum's low 32 bits.

**Effects:** Preserve all memory and ownership. Read only the given range.
A one-past pointer is allowed for a zero-length range.

NULL with nonzero length is outside this contract. Forged seeds remain outside this
practical functional contract: the one-byte path need not agree with first
reducing both seed halves modulo 65521. See the
[Adler seed note](../../proof/adler32.md).

## adler32

```c
uLong ZEXPORT adler32(uLong adler, const Bytef *buf, uInt len);
```

Update an Adler-32 checksum using a 32-bit byte count.

**Domain.** Restricted domain. Effects: **read-only** when `buf` is non-NULL.

**Pre:** Either `buf` is NULL and `len == 0`, or it points to `len` readable
bytes. For the checksum postcondition, the low 32 bits of `adler` are the Adler-32 of A.

**Post:** Return exactly the result of `adler32_z(adler, buf, len)`.
A NULL, zero-length query returns 1. A non-NULL empty range preserves
the checksum's low 32 bits.

**Effects:** Preserve all memory and ownership. Read only the given range.
A one-past pointer is allowed for a zero-length range.

The length is at most `2^32 - 1`. Converting a larger length to `uInt` discards
high bits before the call; use `adler32_z` or several calls for larger ranges.
The zero-length NULL query and forged-seed scope of `adler32_z` apply here too.

## adler32_combine

```c
uLong ZEXPORT adler32_combine(uLong adler1, uLong adler2, z_off_t len2);
```

Compute the Adler-32 of A followed by B without reading either sequence.

**Domain.** Restricted domain. Effects: **pure computation**.

**Pre:** For the concatenation result, the low 32 bits of `adler1` and `adler2`
are the Adler-32 checksums of A and B, and `len2` is the length of B.
In particular, B's checksum starts at 1, independently of A.
Negative lengths are included only for the rejection result below.

**Post:** If `len2 < 0`, return `0xFFFFFFFF`. Otherwise return the Adler-32
of A followed by B. An empty B has checksum 1 and leaves A's checksum unchanged.

**Effects:** Preserve all memory and ownership. Read no buffers or stream state.

The sentinel is not a valid Adler-32. Arbitrary scalar arguments do not create
memory accesses; their exact non-checksum results belong to the broader Lean
contract. No concatenation promise is made for an incorrect B length.

## adler32_combine64

```c
uLong ZEXPORT adler32_combine64(uLong adler1, uLong adler2, z_off64_t len2);
```

Compute the Adler-32 of A followed by B with an explicit 64-bit length.

**Domain.** Restricted domain. Effects: **pure computation**.

**Pre:** For the concatenation result, the low 32 bits of `adler1` and `adler2`
are the independently computed Adler-32 checksums of A and B, and `len2` is the
length of B. Negative lengths are included for rejection.

**Post:** Return `0xFFFFFFFF` for a negative length. Otherwise return the
Adler-32 of A followed by B. Empty B leaves A's checksum unchanged.

**Effects:** Preserve all memory and ownership. Read no buffers or stream state.

This has the same contract and length range as `adler32_combine` in LP64.
The explicit width matters on other builds; this page does not cover them.

## get_crc_table

```c
const z_crc_t FAR * ZEXPORT get_crc_table(void);
```

Return the library's byte-at-a-time CRC table.

**Domain.** Full type domain; there are no arguments. Effects: **pure computation**
returning a pointer to library memory; it does not read the entries.

**Pre:** The library's fixed CRC tables are present, as in the selected build.
No setup call is required.

**Post:** Return a non-NULL pointer to a read-only array of 256 `z_crc_t`
entries. Entry `i` is the reflected CRC register update for byte `i`, starting
with register zero and without the public checksum complements.
Repeated calls return the same pointer.

**Effects:** Preserve all memory and ownership. The library retains the table;
it lives for the program's lifetime. The caller may read the 256 entries,
and must neither write through the pointer nor free it.

`zlib.h` places this among functions outside the documented API. It exposes
only the byte table, not adjacent or braided tables. `z_crc_t` is unsigned
32-bit here. Dynamic table generation is outside this build's scope.

## crc32_z

```c
uLong ZEXPORT crc32_z(uLong crc, const unsigned char FAR *buf, z_size_t len);
```

Update a CRC-32 checksum with a byte range, or obtain its initial value.

**Domain.** Restricted domain. Effects: **read-only** when `buf` is non-NULL,
and reads the fixed library CRC tables.

**Pre:** Either `buf` is NULL, or it points to `len` readable bytes, at any
alignment. For the checksum postcondition, the low 32 bits of `crc` are the
CRC-32 of A. The selected build's fixed CRC tables are present.

**Post:** A NULL `buf` returns 0 for every `crc` and `len`, without reading the
buffer. Otherwise return the CRC-32 of A followed by `buf[0..len-1]`.
A non-NULL empty range returns the low 32 bits of `crc`.

**Effects:** Preserve all memory and ownership. Read only the given byte range
and fixed library tables. A one-past pointer is allowed for an empty range.

Start a new checksum at 0. The function performs the CRC complements itself;
the caller must not complement the running value. Alignment does not change
the contract. The word-access model's limits are recorded in
[the safety model](../safety.md) and [trusted base](../../trusted-base.md).

## crc32

```c
uLong ZEXPORT crc32(uLong crc, const unsigned char FAR *buf, uInt len);
```

Update a CRC-32 checksum using a 32-bit byte count.

**Domain.** Restricted domain. Effects: **read-only** when `buf` is non-NULL,
and reads fixed library tables.

**Pre:** Either `buf` is NULL, or it points to `len` readable bytes, at any
alignment. For the checksum postcondition, the low 32 bits of `crc` are the
CRC-32 of A. The fixed CRC tables are present.

**Post:** Return exactly the result of `crc32_z(crc, buf, len)`.
NULL returns 0 even with a nonzero length. A non-NULL empty range preserves
the incoming checksum's low 32 bits. Complement handling is internal.

**Effects:** Preserve all memory and ownership. Read only the given byte range
and fixed library tables. A one-past pointer is allowed for an empty range.

The length is at most `2^32 - 1`. Converting a larger count to `uInt` truncates
it before the call; use `crc32_z` or multiple updates for larger ranges.

## crc32_combine_gen64

```c
uLong ZEXPORT crc32_combine_gen64(z_off64_t len2);
```

Generate an operator for repeated CRC combinations with the same B length.

**Domain.** Full type domain. Effects: **pure computation**, reading only fixed
library tables.

**Pre:** No argument restriction. The selected build's fixed CRC tables are
present. `len2` may be any signed 64-bit value.

**Post:** A negative length returns 0. A nonnegative length returns a nonzero
32-bit operator suitable for `crc32_combine_op` when B has length `len2`.
For length zero, return `0x80000000`.

**Effects:** Preserve all memory and ownership. Read no buffers or stream state.

The operator depends only on the length. Keep it unchanged and reuse it for
any A and B with that B length. It is an operator, not a checksum.

## crc32_combine_gen

```c
uLong ZEXPORT crc32_combine_gen(z_off_t len2);
```

Generate a CRC combination operator using the ordinary offset type.

**Domain.** Full type domain. Effects: **pure computation**, reading only fixed
library tables.

**Pre:** No argument restriction. The selected build's fixed CRC tables are
present. `len2` may be any representable signed value.

**Post:** Return the same operator as `crc32_combine_gen64(len2)`.
Negative lengths return 0; zero returns `0x80000000`; positive lengths return
a nonzero 32-bit operator for that B length.

**Effects:** Preserve all memory and ownership. Read no buffers or stream state.

The ordinary and explicit 64-bit length ranges coincide in LP64.

## crc32_combine_op

```c
uLong ZEXPORT crc32_combine_op(uLong crc1, uLong crc2, uLong op);
```

Compute the CRC-32 of A followed by B using a previously generated operator.

**Domain.** Restricted domain. Effects: **pure computation**.

**Pre:** For the concatenation result, the low 32 bits of `crc1` and `crc2`
are the CRC-32 checksums of A and B, each started at 0. `op` is the unchanged
result of `crc32_combine_gen` or `crc32_combine_gen64` for the length of B.
The separate rejection case permits `op == 0` with any checksum arguments.

**Post:** Return the CRC-32 of A followed by B. If `op == 0`, return 0.
An operator for an empty B leaves A's checksum unchanged.

**Effects:** Preserve all memory and ownership. Read no buffers or stream state.
The operator can be reused for any pairs with the same B length.

There is no guarantee for a forged operator or one for the wrong B length.
In particular, a nonzero LP64 `op` with zero low 32 bits can fail to terminate;
this is outside the generated-operator contract. Zero is a rejection value,
not an unambiguous error code, since a valid CRC can also be zero.

## crc32_combine64

```c
uLong ZEXPORT crc32_combine64(uLong crc1, uLong crc2, z_off64_t len2);
```

Compute the CRC-32 of A followed by B without reading either sequence.

**Domain.** Restricted domain. Effects: **pure computation**, reading only fixed
library tables.

**Pre:** For the concatenation result, the low 32 bits of `crc1` and `crc2`
are the independently computed CRC-32 checksums of A and B, and `len2` is the
length of B. The fixed CRC tables are present. Negative lengths are included
for rejection, with no checksum restriction.

**Post:** A negative length returns 0. Otherwise return the CRC-32 of A
followed by B. Empty B has CRC 0 and leaves A's checksum unchanged.

**Effects:** Preserve all memory and ownership. Read no buffers or stream state.
The generated operator satisfies `crc32_combine_op`'s input requirement.

For arbitrary checksums at length zero, the implementation returns the XOR of
the low 32 bits. A wrong length has no concatenation guarantee. Zero is also
a possible valid CRC, so negative-length rejection has no distinct error code.

## crc32_combine

```c
uLong ZEXPORT crc32_combine(uLong crc1, uLong crc2, z_off_t len2);
```

Compute the CRC-32 of A followed by B using the ordinary offset type.

**Domain.** Restricted domain. Effects: **pure computation**, reading only fixed
library tables.

**Pre:** For the concatenation result, the low 32 bits of `crc1` and `crc2`
are the CRC-32 checksums of A and B, each started at 0, and `len2` is the length
of B. The fixed CRC tables are present. Negative lengths are included for
rejection, with no checksum restriction.

**Post:** Return the same result as `crc32_combine64(crc1, crc2, len2)`.
Negative lengths return 0. A genuine empty B preserves A's checksum.

**Effects:** Preserve all memory and ownership. Read no buffers or stream state.

The ordinary and explicit 64-bit length ranges coincide in LP64.
This page excludes dynamic table generation, hardware CRC hooks and generated
table executables. See [build and model scope](../../deviations.md).

[Back to the API manual](README.md) · [Contract conventions](contracts.md)
