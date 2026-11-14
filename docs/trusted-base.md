# What the kernel does not establish

The kernel checks a proof against its Lean statement. Applying that result to the selected C
source also depends on the items below. These dependencies are reviewed and tested;
they are not discharged merely by compiling the proofs. See [safety](spec/safety.md),
[verification policy](anti-cheating.md) and [progress](progress.md) for the claim, acceptance
rules and current status.

## 1. Kernel and permitted axioms

The Lean kernel and `propext`, `Classical.choice` and `Quot.sound` are trusted.
The declaration audit permits only those axioms. Fresh kernel replay checks the compiled
proof closure; execution tests do not replace it.

## 2. Runtime and object schema

`ZlibF/Runtime/` defines what a translated run means. `Space.lean` supplies object references
and updates. `Monad.lean` supplies faults, sequencing and loops. `Ptr.lean` supplies pointer
arithmetic, loads, stores and comparisons. `Libc.lean` models the required library operations;
`Alloc.lean` imports it. `Schema.lean`, `Tables.lean` and `LibcTables.lean` supply generated
records, constants, heap tables and operations for each struct kind. Their generator and
[runtime schema](runtime-schema.md) are part of this dependency.

A no-fault theorem concerns these definitions. The intended correspondence is that reachable
C undefined behaviour becomes `Fault.ub`, subject to the limits below. Unsigned arithmetic is
modular. Each translation must check signed arithmetic, shifts and conversions. Loops have
fuel `2^64`; exhausting it is `Fault.outOfFuel`, which termination proofs must exclude. A
no-fault statement that allows `outOfFuel` (the first half of the gz safety goal) is partial
correctness up to `2^64` iterations of each loop, which no real execution reaches. Undefined
behaviour that grows with iterations (a signed 64-bit counter advancing by at least 1 per
iteration) would occur within `2^63` iterations, inside the fuel, so it is not hidden behind
`outOfFuel`.

### Memory and library operations

The heap has separate tables for object kinds. Freed block numbers are never reused. Allocators
write at `nextBlk` only if that identity is unused there; otherwise they fault. `Fresh` protects
future identities. The initial heap must also have unique block identities across tables below
`nextBlk`; `Fresh` alone does not express that condition.

| Operation | Model behaviour requiring review |
| --- | --- |
| `memcpy`, `zmemcpy` | Reject null pointers even for zero length, overlapping ranges and read-only destinations. Whole-record copies use `copyK`, which rejects copying an object onto itself. A bare load/store record pair does not check overlap. |
| `memmove` | Checks the same ranges and writability, but permits overlap and copies from the original source. |
| `memset`, `zmemzero` | `Ptr.fill` counts elements and assigns a value; it represents byte `memset` or zero filling only in the stated uses. `Ptr.memset` replicates a byte. Whole-record zeroing stores the explicit zero record. |
| `strlen` | Requires a NUL inside the represented block. |
| Allocation | Fresh integers come from the arbitrary garbage function; fresh pointer fields are NULL. A `malloc` request above `PTRDIFF_MAX` bytes returns NULL. Otherwise the `allocOk` oracle determines failure. Every `malloc` call consumes one oracle number. Automatic local objects bypass that oracle and do not consume an allocator attempt. |
| `free` | NULL is a no-op. Otherwise the argument must be the start of a live writable allocation of the represented kind. There is no allocation-origin tag. |
| String literals | `strLitRef` denotes a static read-only NUL-terminated entry in the generated closed `strTable`. It is always live, has stable identity and is never freed. Unknown literal text faults. Borrowed external error text has a separate read-only view and lifetime. |

The runtime and translations provide particular models of the external operations they use,
not general libc models. Runtime error text and the gzip external helper implement the
fixed-locale, sequential borrowed-view behaviour recorded in [deviations](deviations.md).
Allocation, formatting, `errno` and `abs` also require their stated correspondence review;
placement outside `Runtime/` does not reduce their semantic role.

### Representation gaps and proof obligations

| Choice or gap | Consequence for a C claim |
| --- | --- |
| Uninitialised pointers become NULL | Equality, copying and freeing NULL can succeed without a prior write. Every pointer read needs a write-before-read argument. The init translations explicitly zero the two allocated stream-state records; this is not a general property of fresh records or automatic `z_stream` storage. Closing the gap requires initialisation tracking or a distinct uninitialised value for all pointer forms, with checked operations and corresponding translation changes. |
| One garbage value per cell | Integer theorems quantify over every `Heap.garbage`, indexed by allocation attempt and cell position. Repeated reads of a cell nevertheless agree. Proofs must not rely on that agreement where C permits unstable unspecified values. |
| Array extents are predicates | `WellFormed`, `Heap.RecordsWellFormed` and `Statics.WellFormed` must establish C lengths. Generated preservation lemmas retain them. Static contents must match the defining C translation; the runtime does not compare them with C. |
| Pointer equality is structural | Different objects compare unequal; equality of dangling pointers does not fault. Proofs must not rely on outcomes that C does not guarantee, including equality at adjacent object boundaries. Relational comparison requires the same live array. |
| Null arithmetic is partly permitted | `Ptr.add NULL 0` returns NULL. `Ptr.diff` rejects null arguments, but `Compress.ptrDiff` returns zero for two nulls. These choices require a separate definedness argument for the corresponding C calls. The `Ptr.diff` comment's C23 attribution is inaccurate; see the [operation and language comparison](spec/safety.md#null-pointers-and-pointer-differences). |
| Address and layout model is partial | There is no general ABI address, effective-type or record-byte-view model. CRC observes low address bits: heap byte blocks retain aligned origins; static and embedded byte origins have arbitrary stable residues. The metadata can be configured without changing any existing storage. Byte-assembled word loads do not settle the C cast's aliasing semantics. Scalar-cell adapters may omit aliases. See [deviations](deviations.md). |
| Read-only marking is partial | Byte blocks, named static tables and instances can be read-only. Word blocks and records in tables cannot represent that qualifier. |
| Pointer construction checks are partial | `Ptr.add` checks its result, not whether a manually constructed starting offset was valid. Translation review must exclude invalid uses of the public `Ptr.ref` constructor. |
| Object origin is not tracked | A caller block created by `allocBytes` can be freed by translated code. Frame and ownership clauses must prevent this where the API forbids it. A wrong-kind state cast faults earlier than the corresponding C access. |

These are limits of the model, not permission to narrow a public theorem silently. The
[runtime review](checking/runtime-review.md) is historical evidence about these choices,
not independent approval of the current definitions.

### Table updates

`Tbl` wraps an array and reads as a total function of block identity. Missing entries return
the default (`none` or `false`). `upd` has proved same-key, different-key and repeated-update
rules from `Tbl.get_set`.

Writing primitives use `Space.modify` to remove, modify and replace an array without retaining
a chain of previous arrays. `Space.modify_eq` states equality with the simpler functional
`put` operation. The trusted review must cover `Tbl.get_set`, `Tbl.modify_eq` and every generated
`Space` instance's `modify` and `modify_eq`. The operation lemmas reason with `put`; execution
performance does not establish their correspondence. See the
[table-update review](checking/runtime-tables-review.md).

## 3. Manual translation

The translation in `ZlibF/Zlib/` is written statement by statement. The kernel does not check
its correspondence to C. Review must check evaluation order, checks, arithmetic, storage
lifetime and effects. A mismatch is a translation bug; it must be corrected with a differential
regression, never hidden by changing a theorem. The [translation rules](design/translation.md)
require evidence for each function. The test inventory is `tests/list.txt`.

Differential tests compare finite executions against the real C. They are evidence of fidelity,
not proof. In particular, agreement and a silent sanitizer do not establish that a C expression
has defined semantics.

## 4. Selected source

The verified source is the pinned `zlib/` submodule plus `patches/*.patch` in name order.
The submodule is never edited. A patch is permitted only for a confirmed upstream bug blocking
a proof; it must be minimal and match a submitted upstream fix. It is removed after the fix is
merged and the pin moves past it.

Each patch is for a confirmed zlib bug that blocks a proof. [The patch register](../patches/README.md) records the
selected-source policy. Historical proposals are not part of the verified source merely
because notes mention them.

## 5. Configuration and external world

The first target is the default x86_64 Linux/LP64 static build with the default allocator.
The accepted [platform scope](spec/platform.md) requires each represented byte
object to have fewer than `2^63` bytes. This is an environment premise; zlib
proofs establish that their operations preserve it. It is the LP64 `PTRDIFF_MAX` object-size
limit, and it holds on every heap of a call history.
Allocation failure remains in scope. Other upstream configurations and custom allocators
require their own correspondence arguments; the full project goal includes them.

**Allocation size.** `malloc` returns NULL for a request above `PTRDIFF_MAX` (`2^63 − 1` bytes),
whatever the allocation oracle says. The call still consumes one oracle number, and the heap
after it is the same as after an oracle failure: the two are indistinguishable to the caller
except through the size. Below the limit the oracle decides, as before. This is glibc 2.43's
behaviour (`malloc/malloc.c`: `_int_malloc` and `__libc_realloc` test `bytes > PTRDIFF_MAX` and
return NULL with `ENOMEM`; `__libc_calloc` first refuses a product that overflows `size_t`).
`errno` is not modelled for `malloc`; no zlib path reads it after an allocation. Only two call
sites can make such a request (`gz_open`'s path copy and `gz_error`'s message); the other
allocations have `unsigned` or fixed sizes. So every library allocation keeps each byte object
below `2^63` bytes (`ByteObjectsFit.allocB`), and the platform premise is needed only for
caller storage.

**Formatting.** `GzFs.snprintf` models the three fixed-format calls of `gzlib.c` (`"%s%s%s"`,
`"%s"`, `"<fd:%d>"`). It writes at most `size - 1` bytes of the full output and a NUL inside
`[dst, dst + size)`, and returns the full length, or -1 past `INT_MAX`. In glibc 2.43 that is
the only failure for `%s` with a `char *` and for `%d` (`stdio-common/vfprintf-process-arg.c`,
`form_string` and `form_integer`; `stdio-common/Xprintf_buffer_done.c`, `EOVERFLOW` past
`INT_MAX`). Its `errno` is not modelled. That is a stated limitation. No caller reads `errno`
before a system call sets it again: the model reads `errno` only in `zstrerror` and `getErrno`,
in `gzwrite.c.lean` (`gz_comp`, after a failed `fsWrite` in an iteration that starts with
`setErrno 0`) and in `gzread.c.lean` (`gz_load`, after a failed `fsRead`; `gzread`, when
`again` was set by `gz_load` in the same call).

`GzFs.vsnprintf` models `gzvprintf`'s call with the caller's format. Any call may fail, through
the world oracle `printfOk`. A failed call returns -1, sets a nonzero `errno` (`printfErrno`;
`EOVERFLOW` past `INT_MAX`) and leaves arbitrary bytes (`printfJunk`) and a NUL inside
`[dst, dst + size)`. glibc writes the terminator on every path (`libio/vsnprintf.c`,
`__printf_buffer_snprintf_init` and `__printf_buffer_snprintf_done`) and writes nothing outside
the buffer. The oracle works in both directions. It may fail where glibc deterministically
succeeds; that widening does no harm to safety. It may succeed where glibc deterministically
fails, for example `%lc` with an invalid wide character, but `%lc` is not represented and faults.
So a goal clause conditioned on `printfOk` describes the model branch, not a claim that glibc
succeeds on that format. The formatter runs before the oracle is consulted, so an unrepresented
conversion faults: conservative. The defaults of the oracle fields (all calls succeed, empty
junk, `EOVERFLOW`) exist for the executable drivers only and carry no meaning for the proofs.
Every goal quantifies over all worlds.

**The gz file world.** `ZlibF/Zlib/gzfs.lean` has two parts. The regular-file part represents
flat paths, regular files, directory markers, descriptor positions and a file-size limit. The
OS-call oracle (fields of `Fs`, numbered by the call counter `nos`) decides for each `read`,
`write`, `lseek`, `close` and `open` call whether it behaves as the regular file, fails with a
chosen errno, or returns a chosen result. Every oracle value is mapped into the POSIX contract of
the call: `read` returns -1 or at most the requested count; a nonempty `write` returns -1 or
between 1 and the count; `lseek` returns -1 or a value in `[0, 2^63 - 1]`, possibly unrelated to
later reads; `close` returns 0 or -1 and releases the descriptor in both cases; `open` returns -1
or any descriptor number below `2^31` that was not open, and fails with `EMFILE` when no
descriptor below `2^31` is free. A failure sets a nonzero errno, and a success may
change errno. The safety goals quantify over every world, hence over every oracle.

The oracle is deliberately wider than any real system: an oracle read or write succeeds whatever
the descriptor's state (closed, wrong access mode); an oracle write does not change the file; an
oracle `lseek` does not move the descriptor; read data is arbitrary; a regular read is still cut
by the read budget. These choices only add behaviours, and must not be narrowed. No proof may
depend on the number `open` returns: the model's descriptor table is not the whole process.

Two OS facts are assumed and not checked: a nonempty `write` never returns 0, and `close`
releases the descriptor even when it reports an error. Both hold on Linux. The first is needed
for termination of `gz_comp`; the real C spins forever on a `write` that returns 0 forever
([progress](progress.md), observation).

`strerror` (`C.libcErrnoText`) is total over every `Int32`. For a number outside its table it
returns glibc's `"Unknown error N"` (glibc `string/strerror_l.c`, checked on glibc 2.43; glibc's
out-of-memory fallback `"Unknown error"` without the number is not modelled). Its text is at most
37 bytes plus a NUL, read-only, and valid until the next call. For a Linux number that glibc
knows and the table does not, the text differs from glibc's; no safety argument depends on the
text or its length, because `gz_error` sizes its copy from `strlen`.

The read budget (`readBudget`) bounds the bytes a non-negative descriptor number may still
deliver; a negative descriptor is unbudgeted. It is a premise of the termination half of the gz
safety goal only ([deviations](deviations.md)). Functional gz contracts are stated for the
regular-file instance (`RegularOs`). `fcntl` has no effect; its results are ignored by the C.

The gz file world and formatting model are additional trusted semantics. Their supported file
kinds, errors, conversions and external string allocation do not represent every operating-system
or library behaviour. Callback correctness relies on the explicit returning protocol, finite
input bound and window-preservation assumptions. [Deviations](deviations.md) records the
consequences for the public adapters. Compiler, operating-system and hardware correctness are
outside the proof.

## 6. Statements and authority

A proof can establish an incomplete or wrong specification. Reviewers must compare the target,
its preconditions and named specification identifiers with the [API](spec/api/README.md),
[format](spec/format/README.md) and selected C. They must also confirm that init establishes the
invariant and that the caller domain has not been reduced.

Nothing in the tooling fixes definitions and theorem types: git tracks them, and review decides
whether their meaning is right. The [verification policy](anti-cheating.md) says what the
acceptance suite still defends against. Current checked results and unresolved
obligations belong in [progress](progress.md).
