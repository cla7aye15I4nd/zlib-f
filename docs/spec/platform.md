# Accepted platform assumptions

The initial scope is the default x86_64 Linux/LP64 static build with the default
allocator. This page states its environment assumptions. It does not ask zlib
to prove properties of the operating system, compiler or hardware.

## Byte-object size

Every represented byte object has fewer than `2^63` bytes. This bound is accepted
as part of the system environment. It is the LP64 `PTRDIFF_MAX` object-size limit: no allocator
returns a larger object. It holds on every heap of a call history (`StreamReachable`). It covers caller-provided storage, raw byte
blocks, static arrays and embedded byte-array views.

The exact predicate is `ZlibF.PlatformMemory.ByteObjectsFit` in
[PlatformMemory.lean](../../ZlibF/Spec/PlatformMemory.lean):

```text
for every represented byte reference ref and array a:
    Space.get h ref = some a  implies  a.size < 2^63
```

It bounds each object separately. It does not bound the sum of allocations or
the total length processed across repeated calls. It is shared by the default,
common and all-supported [input ranges](input-configurations.md); it is not an
extra colour or a compression parameter.

## Use in execution proofs

A theorem may take this predicate as an explicit environment premise.
`Goal.inflate` states it directly. Internal fast-decoder entry proofs derive
their whole-input/output object-size facts from it. The bound gives a signed
64-bit range for differences of valid offsets in the same object.

The zlib proofs must establish that their actual initialization, allocation and
updates preserve the premise. A caller replacing buffers must supply storage
within the accepted environment. The predicate is not derived from an arbitrary
mathematical heap or from the unrestricted runtime allocator.

Each exact statement retains its written domain. Statements that do not need
the bound may quantify over a larger mathematical domain. This page does not
silently insert a new hypothesis into those statements.

## Other pointer obligations

The size bound does not establish that a pointer is live, initialized, in the
same object as another pointer, or within valid offsets. Those are separate
[safety obligations](safety.md). The runtime's null-arithmetic choices remain
recorded in the [model comparison](safety.md#null-pointers-and-pointer-differences)
and [trusted base](../trusted-base.md).
