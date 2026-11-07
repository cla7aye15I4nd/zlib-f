# Caller domains and representation limits

A theorem stronger than the model supports is not a C correctness result. This register records
restricted domains and gaps in the API adapters. Each stronger-than-`zlib.h` precondition must
also appear in its theorem's docstring. A focused manual's narrower example does not change the
fixed public goal or declare excluded calls undefined. See [contract conventions](api/contracts.md).

The full goal remains safety, termination, frame, ownership and functional correctness for all
calls the public API permits. This page does not certify completion. [Overview](overview.md)
is the only list of remaining work; [trusted base](trusted-base.md) records runtime choices.

## Build and memory representation

| Area | Present limit | Consequence |
| --- | --- | --- |
| Initial configuration | Default x86_64 Linux, LP64, static build and default allocator | Other upstream configurations and custom allocators need separate coverage. Default allocation failure remains in scope. |
| Adler initialization queries | `AdlerBufferBytes` admits NULL only with zero length; nonnull readable objects retain their existing domain | This explicit restriction is narrower than the pinned header's unqualified NULL wording. It applies to `Goal.adler32_z` and `Goal.adler32`; CRC contracts keep `BufferBytes` unchanged. |
| Focused function manuals | Entries may require valid handles, separated buffers, checksums of actual strings, generated operators or a stated call order | These are explicit prose scopes. They do not reduce the broader Lean public targets. |
| Compressor length cell | `Concrete.compress2_z` and `Concrete.compress2` use an optional scalar input and returned stored value | Aliasing the cell with input or output is absent. Full pointer-domain claims need that case resolved if the C API permits it. Null-cell effects remain different for `_z` and compatibility wrappers. |
| Counted decompression cells | Draft adapters keep input length, output length and data ranges separate | Aliasing the cells with data or each other is outside these adapters. Early and late memory failures retain distinct scalar effects. |
| Compressor data relation | `Compress2` describes data with a coarse rejection flag | `Compress2Z` and `Compress2Wrapper` express pointer shapes, error ordering and length stores. A data-model theorem alone is not an entry-point refinement. |
| Bound arithmetic | Both lengths are 64 bits on LP64 | `Goal.compress_bound_value` covers every `UInt64`, without a smaller numeric premise. Other ABIs need size-conversion statements. The numeric formula alone is not output adequacy. |
| CRC address and word access | `addrOf` observes only low address bits. Heap byte blocks retain the aligned-origin convention; static and embedded byte objects have arbitrary stable residues. Word loads assemble bytes | General ABI layout, arbitrary raw-block origins and the C cast's aliasing semantics remain outside this abstraction. The public checksum domain is unchanged. The [static-address regression](../tests/verification/regressions/crc-static-address.lean) retains the former model counterexample's input as a positive check. |
| Null pointer arithmetic | `Ptr.add` allows null plus zero; `Ptr.diff` faults on nulls, while the compressor helper permits null minus null | Matching execution observations do not establish C definedness. The [allocation regression](../tests/regression/compress-allocation/README.md) preserves that distinction for zero-capacity null destinations. |

## Stream and callback models

| Area | Present limit | Consequence |
| --- | --- | --- |
| Deflate dictionary order | The zlib branch of `DeflSetDict` rejects a dictionary after `started` | C can accept a dictionary after stream end. A refinement may use the rejection only within the documented ordering. `deflate_valid` is a model theorem, not a theorem about all such C executions. |
| Ordinary byte-format epochs | One initial preset dictionary interprets an ordinary stream | Raw dictionary replacement after decoding starts has a constructor-derived marker. Its exact window effect and unconditional sequence safety remain required. A single initial dictionary cannot describe the entire advanced history. |
| Advanced operation combinations | Priming, headers and recovery retain concrete per-entry targets | The target set is not a completed operational refinement of every combination. A proof may not choose or clear history eligibility markers to avoid obligations. |
| Fast decoder helpers | Local execution and bit-origin lemmas assume distinct raw byte blocks, six input bytes, 258 output bytes, entry bits below eight and sane mode | These are internal premises for construction and init invariants to establish. They do not restrict or prove the public inflate goal. |
| Symbol refinement | Canonical table meaning, suffix stability and compatible leaf flags are explicit premises; local copies use the actual chronological saved bytes | A local symbol lemma does not establish table installation, window history or whole-stream output. |
| Callbacks | Callbacks return, have a finite input bound and preserve the caller-window slice | Descriptor objects may share the window allocation outside that slice. The observation invariant ignores only window bytes and retains effects on all other bytes. These external assumptions must remain explicit. |

## Gz external world

The gz world is trusted semantics beside the heap. Its present range is smaller than the system
interfaces called by C. The [gz translation notes](translation-notes/gz-files.md) describe the
underlying representation; the public [gz contracts](api/gz-file.md) state operation domains.

| Area | Present limit | Consequence |
| --- | --- | --- |
| Files and reads | Flat paths, regular files and directory markers; ordinary reads are short only at end of file | Pipes, sockets, terminals, general short reads and transient failures are absent. Nonblocking and descriptor-control flags do not add those behaviours. |
| File-system errors | Permissions, parent directories, links, ownership and locking are absent. Write failure is modelled through a size limit | This is not coverage of arbitrary `EINTR`, `EIO`, `ENOSPC` or every open failure. Signed seek overflow is still an obligation of the translated code. |
| Formatting | Represented integer, character and string arguments with the supported flags, widths, precisions and length modifiers | Floating-point, pointer, write-count and other unrepresented conversions need a model extension. Draft contracts explicitly require a represented valid formatting result. |
| External error strings | `strerror` text is allocated as a fresh read-only block and is never freed | This differs from borrowing external static storage. Complete ownership claims must account for that choice rather than silently treating it as library-owned storage. |
| Loop fuel | Every translated loop uses the fixed runtime fuel limit | Arbitrary finite callback or external-world behaviour is not proved terminating merely because each external action returns. |

These limits do not justify suppressing a failing public case. If a target is wrong, report its
counterexample and correct it through independent review. If translation or runtime is wrong,
correct that layer with its required review and regression evidence. The
[verification policy](anti-cheating.md) keeps those changes separate from proof progress.

## Local open, close and priming milestones

The open entry lemmas cover NULL arguments, negative descriptors and initial allocation
failure. They do not cover the successful parser or establish the complete public open
contract. The reader-close execution milestone assumes the existing `GzGood` invariant,
read mode and `size = 0`. That domain excludes initialized readers and handles with
inactive dangling buffers admitted by the public representation. It does not establish
the invariant from actual public histories. Priming entry lemmas cover refused streams
and counts outside 0 through 16; accepted bit insertion remains open.

These are scoped internal theorems. None replaces or narrows a public target.
Current work is maintained in [overview](overview.md#public-api-proof-readiness).
