# Translating C without changing its behaviour

The translation preserves the selected C program statement by statement. A difficult proof is
not a reason to reorder checks, cache a read, merge statements or replace an algorithm. A
mismatch is a translation bug: correct it against the C and add a differential regression.
Differential tests give evidence of fidelity; they do not prove it.

The [architecture](architecture.md) explains the object heap. The [trusted base](../trusted-base.md)
records its semantic limits. Use the generated [runtime schema](../runtime-schema.md) for exact
record fields and pointer kinds.

## Fix the source before translating

Translate the default x86_64 Linux static build, with LP64 widths. Resolve preprocessor choices
against `zlib/` plus the ordered patches, rather than against an unpatched checkout or a different
configuration. A source file maps to the same name with `.lean` appended:
`zlib/X.c` becomes `ZlibF/Zlib/X.c.lean`; the same rule applies to headers.

Keep the C function name. Begin its docstring with the exact C signature, including `static`
where present. Give each helper its own definition. Lean definition order may follow dependency
order, but the statements inside a function retain C order. Comment the translated blocks with
the C they implement. For a state machine, also document which states correspond to C labels.

## Preserve evaluation and arithmetic

Expand macros in source order. Preserve reads, writes, branch conditions, early returns and
short-circuit evaluation. Apply integer promotions and usual arithmetic conversions explicitly.
For example, `unsigned short + int` is computed as `int` on this target.

| C type | Lean type on LP64 |
| --- | --- |
| `unsigned char` | `UInt8` |
| `unsigned short` | `UInt16` |
| `unsigned`, `unsigned int` | `UInt32` |
| `unsigned long`, `size_t`, `z_size_t` | `UInt64` |
| `int` | `Int32` |
| `long`, `z_off_t`, `z_off64_t` | `Int64` |

Unsigned operations wrap at their width. Signed operations must check representability. Shifts
must check the C operand width and count, including negative counts. Lean's total arithmetic
does not itself justify a C operation.

Enumerators have a `UInt32` name for unsigned state fields and an `Int32` name with suffix `_i`
for uses at C type `int`. A macro colliding with an enumerator uses `GZ_<name>` where needed:
`GZ_COPY` names the `gzguts.h` macro, while `COPY` names the `inflate.h` enumerator.

## Represent each object once

| C object or operation | Representation |
| --- | --- |
| Struct | A record in its kind's heap table, referenced by block identity |
| `p->f` / `p->f = v` | Record-field read / update, without ABI offset arithmetic |
| Embedded array | An array field; copying the record copies it |
| Pointer into an embedded array | A reference constructor naming the record, field and index |
| Byte buffer | A heap byte block and offset |
| `head` / `prev` word array | A heap word block and element offset |
| Static table | A static reference or checked constant table; stores fault |
| Addressed local | Represented storage at its declaration, with automatic lifetime and cleanup before each return |
| String literal | `strLitRef` into the closed, read-only source literal table; no allocation |
| `ZALLOC` / `ZFREE` | Default-allocator operations, including its failure oracle; custom allocators are outside the selected model |

The schema is generated from the C headers. A translator requests schema additions through the
reviewed runtime workflow; it does not invent a second record layout. Generated array fields
still need their declared-length facts. An allocating theorem also carries `Fresh`, so an
allocation cannot overwrite an existing object.

Automatic local storage must not consume an allocator-failure index. Giving it the semantics
of `ZALLOC` changes which real allocation fails. Likewise, an addressed local must not remain
live after its C lifetime ends.

## Handle fresh memory explicitly

Fresh integer contents are arbitrary. Theorems must hold for every value, including values read
or copied beyond the initialized portion of `prev` or the match lookahead. Do not replace those
contents with zero.

Fresh pointer fields are NULL in this model. That is weaker than an indeterminate C pointer.
For every pointer field read from a newly allocated record, name the earlier writing statement
in a translation comment and establish that order in the proof. NULL comparison, copying and
freeing NULL do not detect an unwritten field. Do not assume repeated reads of an uninitialised
cell agree merely because `Heap.garbage` gives the cell a stable value.

`X.zeroed` represents an actual whole-record zeroing statement. `X.garbage` represents fresh
contents. They are not interchangeable. See [safety, section 3](../spec/safety.md#3-faults-undefined-behaviour-and-model-gaps).

## Use the matching library operation

| C operation | Translation rule |
| --- | --- |
| Byte `memcpy` / `zmemcpy` | `memcpyB`; preserve range and non-overlap checks |
| Whole-record `memcpy` | `copyK dst src`; it checks overlap, unlike a bare load followed by store |
| `memmove` | The corresponding move operation, permitting overlap |
| Byte `memset` | `memsetB` |
| Zero a wider array | `Ptr.fill p 0 n`, with the correct element count |
| Fill a wider array with byte `c` | `Ptr.memset p c n`, replicating `c` in each element |
| Whole-record zeroing | `stK p X.zeroed` |

`memcpy` copies arbitrary values as well as initialized values. The runtime faults on NULL even
for a zero-length copy. Modelled library operations count elements; a C byte count must be
converted correctly. `Libc.lean` and generated `LibcTables.lean` define these operations;
[trusted base](../trusted-base.md) lists their differences from C.

## Keep control flow visible

A loop carries its locals in explicit state, through a runtime loop or bounded recursion.
A `do … while` executes the body before testing the condition. `break`, `continue` and a return
inside a loop use control tags that preserve their distinct destinations. `goto` and switch
fall-through use an explicit program counter when necessary.

The loop bound is not permission to terminate early. Exhaustion raises `Fault.outOfFuel`; a
termination proof must exclude that outcome. Keep every reachable undefined operation visible
as `Fault.ub`, subject to the documented model differences. This includes pointer bounds,
liveness, read-only stores, invalid comparisons, signed arithmetic and overlapping copies.

## Make the change reviewable

Deliver the mirrored source module, a function-level differential test, and a record of the
translation decisions with the corresponding C lines. Report the checks actually run in the
pull request. Follow the [checking guide](../checking/README.md) for audit and mutation evidence.
A runtime change needs independent review because all function proofs depend on its semantics.

If a proof exposes a possible upstream bug, preserve the public domain. Distinguish a proof
technique problem, a wrong specification, a translation mismatch and a real C defect. The last
requires a concrete input and a sanitizer reproduction before it is called a confirmed finding.

[Design guide](README.md) · [Documentation home](../README.md)

## Selected source branches

The input-configuration colour scheme fixes this default x86_64 Linux LP64
build. Input parameter variation does not enable a different compiled algorithm.

| Source family | Selected branches |
| --- | --- |
| Compression | Gzip enabled; FASTEST, LIT_MEM, UNALIGNED_OK and debug checks disabled; default MAX_WBITS 15 and MAX_MEM_LEVEL 9. |
| Decode tables and inflate | Gzip and fast decoding enabled; BUILDFIXED, MAKEFIXED, PKZIP_BUG_WORKAROUND, INFLATE_STRICT and invalid-distance recovery disabled. Fixed entries come from inffixed.h. |
| CRC | Static tables; N=5 and W=8 braid parameters. Default little-endian execution does not exercise the big-endian branch. |
| Gzip files | LP64 large-file entries and C99 formatting; Windows/wide-character and Z_SOLO paths are not selected. Individual I/O requests are bounded by 2^30. |

File-specific statement-order and aliasing checks are beside their
[component proof guides](../proof/README.md). The [external-I/O model](external-io.md)
records the separate system-call and formatting limits. These source readings
remain **to confirm** by the corresponding representation and execution arguments.
