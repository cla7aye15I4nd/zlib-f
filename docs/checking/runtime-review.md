# Trusted-runtime review record

This is a historical source review. Findings describe the definitions and documents read at
review time. They are not a current defect list or independent baseline approval. Some
observations were later addressed; others describe deliberate semantic limits. Consult
[progress](../progress.md) for current work and [the trusted base](../trusted-base.md) for
the current account of assumptions.

## Scope and evidence

The review read `ZlibF/Runtime/` modules `Space`, `Monad`, `Ptr`, `Alloc`, `Tables` and `Schema`,
the schema generator, runtime-schema documentation, safety documentation and translation rules.
It compared them with the pinned `zlib.h`, `deflate.h`, `inflate.h`, `inftrees.h`, `gzguts.h`,
`zutil.h`, `zconf.h`, `deflate.c`, `inflate.c`, `trees.c` and `uncompr.c`.
An adversarial rereading followed the first pass. No build or differential run was performed.
“Confirmed” below means supported by those definitions and source readings, not a compiled
proof or sanitizer reproduction. No source was changed by the review.

Severity measures the risk to the claim that a successful model run excludes C undefined
behaviour. High permits a materially false safety argument; Medium needs another translation
or theorem error, or gives different C semantics; Low concerns completeness or documentation.
These ratings are historical and do not rate upstream vulnerabilities.

The review found that faults propagate through the monad and that loop rules do not hide
fuel exhaustion. Its concerns were representation boundaries, missing initialization history,
schema constants and overstatements in documentation.

## Findings R1–R13

### R1. Fresh pointer fields model null rather than indeterminate pointers

Historical severity: High for the general claim, Medium for the reviewed zlib paths.
`Schema.lean` garbage constructors used default pointers; `Space.lean` defined that default
as null; `Tables.lean` allocated those records. Thus allocating a record, loading an unwritten
pointer and comparing it with null or passing it to `freeB` could succeed. Integer-garbage
quantification did not cover indeterminate pointers.

The review used this C example to expose the gap:

```c
z_stream *s = malloc(sizeof *s);
if (s) { free(s->next_in); free(s); }
```

The reviewed inflate and deflate init paths zeroed their states immediately after allocation.
Other records, especially `gz_state`, required separate inspection. Suggested remedies were
pointer-field initialization marks or an explicit uninitialized pointer value. The essential
proof obligation is temporal: every pointer field must be written before it is read.
The old safety and translation documents claimed a fault while the schema document described
null; that contradiction was part of R1.

### R2. Null pointer arithmetic is a semantic decision

Historical severity: Low. `Ptr.add` and `Ptr.add_null_zero` accepted `NULL + 0`.
The review treated this as a deliberate model exception, not a newly discovered
zlib defect. Its historical date labels do not establish C23 definedness; see
the [current operation/language comparison](../spec/safety.md#null-pointers-and-pointer-differences).
It also recorded that `Ptr.diff null null` faulted.
Any supported C dialect and null-arithmetic exception must be stated in the trusted base;
proofs must not silently turn a model decision into a claim about all C builds.

### R3. One schema name represented two different `COPY` constants

Historical severity: High if used, Medium by reviewed reach. `Schema.COPY` was the inflate
mode value 16195, while `gzguts.h` defined `COPY` as 1 for `state->how`. The generator skipped
macros that collided with enumerator names. A gz translation using the shared name could
therefore verify the wrong state machine. `GZIP` had a related name collision, though its
numeric value matched the gz use. Suggested remedy: distinct names or constants scoped to
translation units.

### R4. Enumerator constants were typed as unsigned

Historical severity: Medium. The enumerator values matched C, but the schema gave constants
such as `HEAD` and `CODES` type `UInt32`. C enumeration constants have type `int` on the
reviewed target. For example, comparing `int x = -1` with `HEAD` differs if the constant forces
an unsigned comparison. Correct field storage types do not fix constant-expression types.
The proposed remedy separated signed constants from casts into enum storage.

### R5. Fixed array extents and static contents required invariants

Historical severity: Medium. Record fields were Lean arrays with C extents in comments.
`stK` accepted arbitrary records, while only garbage constructors imposed the extents.
An inflate state with `lens.size = 321` allowed index 320 in the model although C has 320 cells.
Static arrays defaulted to empty; arbitrary assumed contents could also satisfy a weak theorem.
The review proposed generated shape predicates preserved by stores and canonical static data
checked against C. Internal shape requirements must be established by init and preserved,
not silently imposed as narrower public caller domains.

### R6. Allocation relied on freshness instead of checking it

Historical severity: Medium, conditional. The reviewed allocators wrote at `nextBlk` without
checking that it was unused. With a live byte block at 0 and `nextBlk = 0`, allocation could
overwrite it and clear its read-only status. Runs from the intended empty heap preserved
freshness, but arbitrary-heap theorems needed it explicitly, together with cross-table block
uniqueness below `nextBlk`. This records the old implementation; it must not be read as a
claim that current allocation still overwrites live blocks.

### R7. Read-only status did not cover every object kind

Historical severity: Medium, Low for reviewed zlib uses. Bytes and named statics supported
read-only marking. Word blocks and allocated records did not, and `freeW` did not check it.
The model could not express a general constant word-array object. The reviewed zlib source
did not require such an object; a future translation or witness must not assume this capability.

### R8. Pointer equality distinguished object identities unconditionally

Historical severity: Low to Medium. Derived pointer equality made references to distinct
objects unequal, including adjacent one-past/start addresses. C need not supply that result
for every such comparison. Equality involving dangling pointers also remained available.
The review suggested an explicit checked or nondeterministic equality boundary. Reachability
and reliance on these cases require translation evidence.

### R9. Uninitialized integers had one fixed value per cell

Historical severity: Medium, a semantic choice. `Alloc.lean` populated fresh cells using the
garbage oracle once. Repeated reads therefore agreed, unlike C interpretations that permit
unstable unspecified values. A proof relying on that agreement could exceed the model's
C justification. The reviewed `slide_hash` and `longest_match` uses did not do so. Old comments
about initialization bits were also incorrect; see R12.

### R10. Whole-record copying lacked an overlap check

Historical severity: Medium, a translation-rule issue. A record load followed by store permits
self-copy, whereas overlapping `memcpy` is undefined in C. The reviewed `deflateCopy` and
`inflateCopy` sites used distinct records. A future copy primitive or proof must check both
object identity and embedded-record overlap. Whole-record zeroing also requires review that
every C field was zeroed; a manually written zero record is not automatically faithful.

### R11. Smaller primitive boundaries

| Review-time observation | Risk or obligation |
| --- | --- |
| `Ptr.add` checked the result, allowing a manually forged invalid pointer to move back in range. | Low; translation reachability was unconfirmed. Checked pointer operations did not construct that initial pointer. |
| `Ptr.diff` converted through `Int64.ofInt` instead of rejecting overflow. | Low; the example required an array with `2^63` elements. |
| Zero-length fill/copy checked read-only status. | Low; a possible spurious fault despite no write. |
| Generic `Ptr.fill` accepted arbitrary element values. | Low; nonzero `memset` of a word needs repeated bytes, not the numeric byte value. The documented use was zeroing. |
| Dangling arithmetic and invalid record casts faulted early. | Conservative in the reviewed cases; C could fault later. |
| Loop fuel was `2^64`. | A separate termination obligation, not a C undefined-behaviour rule. |
| `freeB` had no allocation-origin tag. | A harness allocation could be freed as a library allocation; ownership proofs must exclude misuse. |
| Direct record-reference `put` inserted dead table slots. | Store primitives checked liveness first. Direct use needed scrutiny; its comment promised more. |

### R12. Documentation overstated or misstated the model

The old documents claimed initialization bits, type tags and faults for unwritten pointer
reads that the runtime did not provide. They disagreed about the location of fixed Huffman
tables: the selected source had `inffixed.h` included by `inftrees.c` in `inflate_fixed`.
The generator's “not an integer constant expression” explanation was wrong for the collided
`COPY` and for `GZ_OFF_MAX`; the latter's `sizeof` expression exceeded its evaluator.
The trusted-base document also incorrectly said that differential tests were absent.
These are historical mismatches, not assertions about today's documents.

### R13. Static-data generation omitted some source authority

Historical severity: Low. `bl_order` from `trees.c` was absent from `Statics`.
`StaticTreeDesc` was hard-coded rather than extracted, so source drift could be missed.
The reviewed descriptor triples `(extra_base, elems, max_length)` were `(257, 286, 15)`,
`(0, 30, 15)` and `(0, 19, 7)`. Default static values did not establish these facts.

## Schema comparison recorded by the review

The review found no missing, transposed or incorrectly sized fields in `ZStream`, `GzHeader`,
`CtData`, `TreeDesc`, default-build `DeflateState`, `Code`, `InflateState`, `GzFile`, `GzState`
and `StaticTreeDesc`. It checked array extents 573, 61, 39, 16, 573, 573, 320, 288 and 1444,
and disjoint garbage-index ranges. Macro and enumerator values matched the selected default
branch, subject to the name and type findings above. This did not cover `LIT_MEM` or
`ZLIB_DEBUG`. Plain `char` was signed on the target; byte-pointer representation still
required explicit sign extension at translated character reads.

## Questions U1–U5 left unconfirmed

| ID | Translation evidence required |
| --- | --- |
| U1 | Alignment, effective type and byte views of typed objects. `uncompr.c` takes `(Bytef *)&stream.reserved`; CRC performs aligned wide reads. A dummy byte block can hide aliasing, and the schema lacked alignment facts. |
| U2 | Checked signed arithmetic, shifts and division at each translated operation. `M` itself did not enforce them. |
| U3 | Faithful use of the transparent `M` function type. A hand-written translation could catch faults or edit arbitrary heap fields even though ordinary bind did not. |
| U4 | Whether an actual translation can construct an out-of-range `Ptr.ref`, as in R11. |
| U5 | Whether any allocated record besides the two zeroed states reads a pointer before writing it, as in R1. |

## Primitive behaviour found correct in scope

The reviewed load/store operations rejected null, dangling and out-of-range access; stores
also rejected read-only destinations. One-past pointers were not readable. Byte `memcpy`
rejected overlap, while move operations used the original source in both overlap directions.
`freeB` accepted null as a no-op and rejected nonzero offsets, statics, embedded arrays,
freed blocks and read-only blocks. Never-reused block numbers supported the reviewed
use-after-free and double-free rules. Parent removal invalidated embedded record references.

Bind propagated errors, `OkOn` required an actual successful result, and loop rules required
a bound below fuel. `strlenB` faulted if the block contained no terminator. These source
observations did not establish complete runtime/C equivalence or approve a baseline.
