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
| Internal first public deflate path | Default level six, Z_NO_FLUSH, raw output with at least three bytes and the explicit before-block byte budget | The scoped composition covers initialization-compatible first calls, including empty input. It does not replace or narrow Goal.deflate. Header-fragment execution also includes a one-byte split header. |
| Internal fixed-block source branch | Default memLevel 8, base pending cursor, drained pending, at most seven entry bits, legal packed symbols and their logical trace; raw caller output has arbitrary capacity | Tag, payload, real reset, conditional alignment and publication compose. The complete raw-stream validity corollary starts with zero bits and uses sufficient capacity 63488. Earlier builders, branch selection and public deflate remain separate. |
| Internal computed fixed choice | Positive-level default shared-buffer geometry, drained pending at its base, at most seven entry bits, actual packed symbols and trace; the actual rounded costs select fixed coding and the earlier stored test is false | Complete _tr_flush_block includes actual hint detection and all constructors. Final complete raw validity also needs zero entry bits and sufficient raw output capacity 63488. Stored/dynamic choices and the public domain are unchanged. |
| Internal default zlib finish | FINISH_STATE, no input or lookahead, drained final-block pending and bits, base cursor, wrapper 1, last_flush in -2..5, positive raw caller output | The actual public call writes and publishes the checksum once. Finishing strategy establishment and the full public call history are separate. The internal trailer publisher also covers zero capacity. |
| Internal default FINISH protocol | Successful default initialization at level 6, memLevel 8, zlib wrapper, no custom header; accepted Z_FINISH calls with positive raw output, valid nonnull input when nonempty, and no new input in FINISH_STATE; legal rebuffering | The actual initialization establishes the invariant, and actual calls preserve it over arbitrary finite accepted histories. No byte budget is assumed. Refusals, other flags and advanced operations remain open. Full output-format history, total counters and heap frame remain open; Goal.deflate is unchanged. |
| Internal ordinary default compression protocol | The same default configuration and positive raw public output; NO_FLUSH requests have new nonempty input before FINISH_STATE, and FINISH requests add no input after FINISH_STATE; arbitrary legal rebuffering | Actual init establishes the same boundary used by both call kinds. Every finite accepted mixed history retains it and actual public reachability. Empty-input duplicate/refusal cases, other flags and advanced operations remain open. Output-format history, total counters and heap frame remain open; Goal.deflate is unchanged. |
| Internal total ordinary request protocol | Successful default initialization at level 6, memLevel 8, zlib wrapper and no custom header; NO_FLUSH/FINISH histories with null or raw-array output and legal caller rebuffering; the next-request extension also admits every out-of-range signed flush argument | Scoped contracts include zero output, empty input, retries, duplicates, invalid pointer arguments and new input after finishing. They state exact counters, the produced-byte slice, precise BufferFrame, no allocation/live-object changes, the exact STREAM_ERROR guard and STREAM_END conditions. Invalid flush arguments leave the heap unchanged. Other valid flags, embedded output references, advanced operations and encoded-output correctness are outside these scoped contracts; Goal.deflate is unchanged. |
| Internal fixed-table payload | Drained pending count, at most ten buffered entry bits, actual legal packed symbols and initialized tree storage; the default publication composition uses memLevel 8 and raw caller output | The complete literal/match payload derives read/write and publication room. Actual emission, publication and independent payload decoding are composed. Block selection, tag, padding, trailers and whole-stream composition still belong to the unchanged public deflate goal. |
| Internal pending-publication phase | The complete flush_pending result assumes pending_out = pending_buf, complete-bit room and raw caller output; all 0..16 buffered-bit counts and arbitrary output capacity are included | Actual default initialization and real bit sends supply witnesses. Whole block-output paths must establish these publishing conditions; the public deflate goal is unchanged. |
| Public deflate idle pending continuation | BUSY_STATE, Z_NO_FLUSH, no input or lookahead, positive pending bytes and strictly larger raw output capacity, with fewer than eight residual bits | This actual drain-and-continue result leaves data compression and finish/trailer composition as separate obligations in the unchanged public goal. |
| Public deflate pending-drain branch | Positive raw output capacity no greater than the existing pending count and fewer than eight residual bits; all accepted flags and the accepted FINISH_STATE entry are covered | This is the actual early-return path before new compression. It leaves Goal.deflate and the public caller-buffer domain unchanged. |
| Internal pending-output path | Low-bit flush_pending includes every cursor admitted by DGood and arbitrary raw output capacity; two-call composition across legal rebuffering requires no registered gzip header | These internal copying and rebuffering premises leave the public caller-buffer domain unchanged. Full publication separately needs its base cursor and bit room. |
| Internal slow-loop path | The complete Z_NO_FLUSH strategy theorem assumes `3 * (origin + fillEnd + avail_in - base + 1) < sym_end` and wrapper 1 | The real ledger derives tally room on each iteration. This scopes the before-block theorem; it does not narrow the public deflate target. |
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
