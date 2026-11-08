The [state-operation chapter](/sample/state-operations.html) distinguished forgetting progress from releasing memory. Now follow the objects behind those operations. A successful initialization acquires storage that later calls keep using; an unsuccessful attempt must account for everything it acquired before the failure.

These source mechanisms are **to confirm** through their corresponding execution proofs. The initial build uses the default allocator and includes allocation failure. Custom callbacks, other layouts and the accepted platform limits have their own explicit scope in the [configuration reference](/reference/docs/spec/input-configurations.html) and [safety requirements](/reference/docs/spec/safety.html).

## Compressor storage {#compressor}

Successful [deflateInit2_](/reference/functions/deflateInit2_.html) owns five allocations: a state record, window, predecessor array `prev`, hash-head array `head`, and pending storage. Tree arrays, heap/depth arrays and their descriptors belong to the state record. The caller's `z_stream`, input/output and optional gzip metadata remain borrowed objects, not extra allocations to release with End.

Let `W = 1 << w_bits` and `B = 1 << (memLevel + 6)`. The selected packed-symbol layout has:

| Allocation | Extent | Default dimensions |
| --- | --- | --- |
| State | One `deflate_state` record | Contains control fields and embedded trees |
| Window | `2W` bytes | 65536 bytes at window bits 15 |
| `prev` | `W` positions, two bytes each | 65536 bytes |
| `head` | `1 << (memLevel + 7)` positions | 32768 positions, 65536 bytes at memory level 8 |
| Pending | `4B` bytes | 65536 bytes with `B = 16384` |

Symbols begin at `pending_buf + B`; they are not a sixth allocation. Each record occupies three bytes. The [shared-storage chapter](/sample/storage.html) explains when consumed records make room for output. `memLevel` changes hash and symbol capacity; the compression level instead changes strategy/search settings. The zlib window request 8 is normalized to 9. Actual parameter acceptance, normalization and refusals belong to the full [initialization contract](/reference/functions/deflateInit2_.html).

Allocation acquires capacity, not meaningful content everywhere. The state record is explicitly zeroed. `lm_init` clears hash heads and establishes counters; it does not initialize every predecessor slot. `high_water` tracks established window bytes. Later searches need their own written-position argument rather than treating an allocated array as entirely initialized.

## A complete failed attempt {#failure}

After compatible version/structure checks, compressor initialization validates parameters before allocation. If the state allocation succeeds, it then attempts all four buffers **before testing their combined result**. An early buffer failure does not stop later requests.

Take this concrete allocation-oracle outcome:

| Attempt | Object | Outcome |
| --- | --- | --- |
| 1 | State | Success |
| 2 | Window | Success |
| 3 | `prev` | Failure |
| 4 | `head` | Success |
| 5 | Pending | Success |

The failure branch must release pending, head, window and state, skipping the NULL predecessor pointer. It cannot clean up only the allocations preceding attempt 3. The source sets a cleanup-compatible status, records the memory message, calls [deflateEnd](/reference/functions/deflateEnd.html), and returns `Z_MEM_ERROR` with no new live owned block and a NULL stream state.

If attempt 1 itself fails, there are no buffer attempts and the old `state` field is retained. Preparing default callbacks and clearing `msg` can already have changed the stream. Even complete cleanup does not restore the allocation-attempt counter or fresh-identity counter. “No new live allocation” and “the whole heap is unchanged” are different conclusions.

The following smaller, two-resource model isolates the lifetime pattern. It is not the exact five-request schedule above; select the second failure, then compare successful initialization followed by End.

<div class="zl-demo-mount"><zlib-demo kind="ownership"><p>A teaching initializer acquires state and then window. A failed second allocation releases state; successful initialization retains both until End. The real compressor attempts four buffers before checking them.</p></zlib-demo></div>

The ledger pattern also applies to [deflateCopy](/reference/functions/deflateCopy.html), but copying has its own path. It must release every newly acquired destination allocation on failure and preserve the source. It cannot call cleanup on the source merely because the destination attempt failed.

## Decoder storage and lazy history {#decoder}

[inflateInit2_](/reference/functions/inflateInit2_.html) initially allocates only an `inflate_state`. Its code-length/work/decoding arrays are embedded in that record. The window pointer starts NULL. Static fixed decoding tables are shared read-only objects, not per-stream owned allocations.

The decoder delays the history-window allocation until an operation needs to retain or install history. [inflateSetDictionary](/reference/functions/inflateSetDictionary.html) can require it; normal decoding can allocate while committing recent output for continuation. A one-call `Z_FINISH` completion can avoid a window entirely. Avoiding an unnecessary allocation and history copy is the practical benefit of this lazy design.

This moves failure into a surprising place. `inflate` can already have consumed input and written caller output when window allocation fails. Its I/O pointers and available counts can reflect those effects, while normal final totals/checksum accounting is skipped. `Z_MEM_ERROR` therefore does not mean unchanged output. The live decoder remains endable; see the complete [inflate contract](/reference/functions/inflate.html).

Decoder initialization has a different error order from the compressor. It attempts state allocation before validating the window argument. An invalid window request can therefore produce `Z_MEM_ERROR` if allocation fails first. If allocation succeeds but the request is invalid, the new state is freed and `state` becomes NULL before `Z_STREAM_ERROR`. Version/structure rejection happens earlier still. These distinctions matter to callers and to the exact failure proof.

## Reuse and release {#release}

[inflateReset](/reference/functions/inflateReset.html) can keep a compatible physical window while clearing its logical history. An incompatible window is freed; reset itself does not allocate its replacement. [deflateReset](/reference/functions/deflateReset.html) keeps its five allocations for another compression task. Reuse avoids repeated allocation work without implying that prior dictionary contents remain valid history.

[inflateEnd](/reference/functions/inflateEnd.html) frees the optional window and state, clears the state pointer, and returns `Z_OK` for a valid live decoder even if decoding was abandoned. [deflateEnd](/reference/functions/deflateEnd.html) frees all five allocations; `Z_DATA_ERROR` for busy unfinished compression is reported after release, not instead of release. A second End fails the stream check rather than freeing again.

[inflateBackInit_](/reference/functions/inflateBackInit_.html) is a useful ownership contrast: its history window is supplied by the caller. [inflateBackEnd](/reference/functions/inflateBackEnd.html) releases the callback decoder's state, not that caller window. The [ownership proof chapter](/sample/ownership-proof.html) turns these actual object transitions into establishment, frame and exact live-block obligations.
