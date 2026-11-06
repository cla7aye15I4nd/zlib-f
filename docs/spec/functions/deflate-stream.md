# Compression through a stream (deflate.c)

These are concise contracts for the default build of the verified source: the pinned
`deflate.c`, its applied patches and `zlib.h`. They describe focused use of the API.
The readings of the C below are **to confirm** by proof. They do not assert proof completion.
The existing `ZlibF.Spec.Public.Goal.*` statements retain their broader domains and error cases.
See [public-goals.md](../public-goals.md) for those targets and [overview.md](../../overview.md)
for remaining work.

## Shared conventions

Each stated Pre requires termination without runtime faults and the stated Post.
A call that retains a live stream preserves its representation invariant.

- **Live stream:** a writable `z_stream` with a compressor state established by successful
  init or copy, preserved by legal calls, and not ended. The caller does not alter its
  internal state or allocator fields. Calls on one stream are sequential.
- **Buffers:** input covers `avail_in` readable bytes; output covers `avail_out` writable
  bytes. They do not overlap each other, the stream or its owned state. A non-NULL scalar
  result points to a writable cell separate from other results and stream memory.
  These separation conditions are explicit focused assumptions; see [safety.md](../../safety.md).
- **Allocator:** the default allocator/free pair is used, or both fields are NULL before
  init. Allocation may fail on any attempt. Custom allocator callbacks are outside this page's scope.
- **Frame and ownership:** calls change only their stream, its owned state and stated
  output regions. Caller input is read-only. Caller buffers and header records remain caller-owned.
  Only init and copy allocate; only their failure cleanup and `deflateEnd` free memory.
  Other calls preserve the stream's allocation set.
- **Header lifetime:** a retained gzip header and its optional fields remain readable and
  unchanged while used. Non-NULL `name` and `comment` have a terminating zero; `extra`
  covers its stated length. Focused format contracts use `extra_len <= 65535`.
- **Checked refusals:** except for init and bounds, a failed stream check returns
  `Z_STREAM_ERROR` before normal operation, without writes. `deflateCopy` additionally
  clears a non-NULL destination state. Query output cells are untouched on this refusal.
- **Restricted domain** means these explicit memory, lifetime and call-order conditions,
  plus the entry's Pre. It does not mean every representable pointer or integer is accepted.
  Error summaries cover readable checked states, not arbitrary invalid addresses.

## deflateInit_

```c
int ZEXPORT deflateInit_(z_streamp strm, int level, const char *version, int stream_size);
```

Start a compressor with the default zlib wrapper and compression settings.

**Domain:** restricted domain. **Effect:** allocate and initialise.

**Pre:** `strm` is writable and owns no live compressor state. Its allocator fields are
initialised as above. `level` is -1 or 0..9. `version` has a readable first byte matching
`ZLIB_VERSION`, and `stream_size == sizeof(z_stream)`.

**Post:** the `deflateInit2_` contract holds with method `Z_DEFLATED`, window 15,
`memLevel` 8 and `Z_DEFAULT_STRATEGY`. Level -1 selects 6. No input is consumed and
no output is written. Return `Z_OK` on success or `Z_MEM_ERROR` with complete cleanup.

**Outside focused scope:** the same version and argument refusals as `deflateInit2_` apply.
The `deflateInit` macro supplies version and structure size.

## deflateInit2_

```c
int ZEXPORT deflateInit2_(z_streamp strm, int level, int method, int windowBits,
                           int memLevel, int strategy, const char *version, int stream_size);
```

Start a compressor with a chosen wrapper and compression settings.

**Domain:** restricted domain. **Effect:** allocate and initialise.

**Pre:** the stream and version conditions of `deflateInit_` hold. Parameters are:
`level` -1 or 0..9; `method == Z_DEFLATED`; `memLevel` 1..9; `strategy` 0..4;
`windowBits` 8..15 for zlib, -15..-9 for raw, or 25..31 for gzip.

**Post:** `Z_OK` establishes a live stream with five owned allocations and the selected
settings. A zlib window request of 8 becomes 9. Totals are zero, `msg` is NULL,
`data_type` is `Z_UNKNOWN`, and `adler` is 1 for raw/zlib or 0 for gzip.
I/O pointers and available counts are unchanged; no bytes are consumed or emitted.
The caller releases the state with `deflateEnd`.

`Z_MEM_ERROR` leaves no newly allocated block live. If the state allocation fails,
`state` retains its entry value. If a later allocation fails, `state` becomes NULL and
`msg` reports insufficient memory. Once the state allocation succeeds, all four buffer
allocations are attempted before failure cleanup.

**Outside focused scope:** a NULL/mismatched version first byte or wrong structure size
returns `Z_VERSION_ERROR` without changing the stream. With compatible version and NULL
`strm`, return `Z_STREAM_ERROR`. Other scalar parameters outside the accepted ranges
return `Z_STREAM_ERROR` before allocation, after clearing `msg` and installing default
allocator fields where needed. Installing the default allocator clears `opaque`.
These refusals are required by the unchanged public init goals.

## deflateSetDictionary

```c
int ZEXPORT deflateSetDictionary(z_streamp strm, const Bytef *dictionary, uInt dictLength);
```

Load preset bytes as compression history without emitting them as input data.

**Domain:** restricted domain. **Effect:** update history and dictionary checksum.

**Pre:** live raw or zlib stream, immediately after init or `deflateReset`, before its first
`deflate` and first dictionary call. `dictionary` is non-NULL, covers `dictLength`
readable bytes and is separate from the window.

**Post:** return `Z_OK`. History retains an available suffix of the dictionary, at most
one window. The dictionary checksum for zlib covers the entire supplied dictionary.
The original `next_in` and `avail_in` are restored; `total_in` increases by
`min(dictLength, window size)`. No compressed output is delivered and no allocation occurs.
The decoder must be given the same preset dictionary when required.

**Outside focused scope:** gzip, NULL dictionary, zlib after its initial state, nonzero
lookahead, or raw input not at a completed block boundary returns `Z_STREAM_ERROR`
without changes. Raw replacement at legal boundaries and repeated pre-start zlib calls
remain in the public goal. Repeated zlib calls accumulate Adler-32 rather than restarting it.

## deflateGetDictionary

```c
int ZEXPORT deflateGetDictionary(z_streamp strm, Bytef *dictionary, uInt *dictLength);
```

Read the current compression history, including accepted lookahead.

**Domain:** restricted domain. **Effect:** query with optional output buffers.

**Pre:** live stream. `dictionary` is NULL or writable for one window, separate from the
window; `dictLength` is NULL or a valid scalar output cell.

**Post:** return `Z_OK`. Let `n = min(strstart + lookahead, window size)` in the live state.
A non-NULL `dictionary` receives the last `n` bytes of that window region, in order;
a non-NULL `dictLength` receives `n`. Either result may be omitted independently.
The stream is unchanged. History need not contain a full window of all previously supplied input.

## deflateResetKeep

```c
int ZEXPORT deflateResetKeep(z_streamp strm);
```

Restart output and progress counters while retaining compression history.

**Domain:** restricted domain. **Effect:** reset, retaining history and allocations.

**Pre:** live stream in any phase. This is an undocumented entry; use `deflateReset`
when the next compressed stream must start with empty history.

**Post:** return `Z_OK`. Totals become zero, `msg` becomes NULL and `data_type` becomes
`Z_UNKNOWN`. Pending output, unfinished lookahead and bit/block progress are discarded;
wrapper emission restarts and `adler` becomes 1 for raw/zlib or 0 for gzip.
The custom gzip header pointer is cleared. Level, strategy, tuning, window and hash history
are retained. I/O pointers and available counts are unchanged. No allocation or free occurs.

A later compressor call can refer to pre-reset history. This reset alone therefore does
not promise a stream decodable with an empty dictionary.

## deflateReset

```c
int ZEXPORT deflateReset(z_streamp strm);
```

Reuse a stream for new compression with empty history.

**Domain:** restricted domain. **Effect:** reset, retaining allocations and configuration.

**Pre:** live stream in any phase, including after `Z_STREAM_END`.

**Post:** return `Z_OK`. The `deflateResetKeep` counter, wrapper and pending-output reset
holds, and history is logically empty. A previous dictionary is forgotten; tuning returns
to the defaults for the current level. The level and strategy last selected by
`deflateParams`, wrapper, window and memory settings are retained. The gzip header is
forgotten. I/O pointers and available counts are unchanged. No allocation or free occurs.
Unfinished input already accepted and undelivered output are discarded.

## deflateSetHeader

```c
int ZEXPORT deflateSetHeader(z_streamp strm, gz_headerp head);
```

Select the header for the next gzip stream.

**Domain:** restricted domain. **Effect:** retain a caller-owned header pointer.

**Pre:** live gzip stream, after init or reset and before its first `deflate`.
`head` is NULL for defaults, or satisfies the shared header conditions.

**Post:** return `Z_OK` and retain `head`; no header bytes are copied or output yet.
Subsequent `deflate` writes the requested text flag, time, OS, optional extra/name/comment,
and optional header CRC. Compression settings determine the extra flags byte.
The caller keeps the record and fields alive until header emission completes.
Either reset clears the pointer. No allocation or ownership transfer occurs.

**Outside focused scope:** non-gzip or a failed stream check returns `Z_STREAM_ERROR`
without changes. Late registration is accepted for gzip but does not rewrite header bytes
already emitted; the public pointer-storage goal includes that case.

## deflatePending

```c
int ZEXPORT deflatePending(z_streamp strm, unsigned *pending, int *bits);
```

Report output waiting inside the compressor.

**Domain:** restricted domain. **Effect:** query with optional scalar results.

**Pre:** live stream; each result is NULL or a valid separate output cell.

**Post:** return `Z_OK`. If requested, `pending` receives the undelivered whole-byte count
and `bits` the remaining bit count (0..7 for legal compression history).
The stream and its buffers are unchanged. Omitted results are not written.

If a represented pending count exceeds `unsigned`, the requested byte count saturates
and return is `Z_BUF_ERROR`; a requested bit result is still written. The public query
goal includes this numerical refusal even though normal default-build buffers are smaller.

## deflateUsed

```c
int ZEXPORT deflateUsed(z_streamp strm, int *bits);
```

Report the last byte's bit use at the most recent byte-boundary flush.

**Domain:** restricted domain. **Effect:** query with an optional scalar result.

**Pre:** live stream; `bits` is NULL or a valid output cell.

**Post:** return `Z_OK`. If requested, store the saved bit-use count: 1..8 after a
byte-boundary flush, or 0 since init/reset if none occurred. The stream is unchanged.
This saved count differs from the currently pending bits returned by `deflatePending`.

The public goal returns the stored value for every checked state, without assuming that
an arbitrary represented state satisfies the normal-history range.

## deflatePrime

```c
int ZEXPORT deflatePrime(z_streamp strm, int bits, int value);
```

Prefix raw compression output with a caller-supplied bit fragment.

**Domain:** restricted domain. **Effect:** append bits to pending output.

**Pre:** live raw stream before its first `deflate` after init or `deflateReset`;
`bits` is 0..16 and `value` is any `int`. The caller accounts for these prefix bits
when interpreting the later compressed stream.

**Post:** `Z_OK` appends the low `bits` bits of `value`, least significant first,
to the logical pending bit sequence. Complete bytes join pending output and fewer than
8 bits remain buffered. No bytes are delivered to `next_out`; no allocation occurs.
`Z_BUF_ERROR` inserts no bits when the pending buffer has insufficient space.
Existing pending bytes may be compacted within their owned buffer before that refusal.

**Outside focused scope:** counts outside 0..16 give `Z_BUF_ERROR` before compaction;
a failed stream check gives `Z_STREAM_ERROR`. The implementation does not check wrapper
or first-call timing. Its public goal covers exact pending-bit effects there, without
promising ordinary stream validity for arbitrary inserted fragments.

## deflateParams

```c
int ZEXPORT deflateParams(z_streamp strm, int level, int strategy);
```

Change level and strategy, finishing the old block when needed.

**Domain:** restricted domain. **Effect:** update settings; may consume input and emit output.

**Pre:** live stream before finishing, valid stream buffers and any active header;
`level` is -1 or 0..9 and `strategy` is 0..4. To choose an exact input boundary, complete
`deflate(Z_BLOCK)` until `avail_out` is nonzero and supply no new input before this call.

**Post:** `Z_OK` installs the requested settings (level -1 means 6). Changing level
restores that level's standard tuning values. A needed block flush uses the old settings
and can consume some input and deliver output. I/O pointers, available counts and totals
account for exactly those bytes; unconsumed input remains available.

`Z_BUF_ERROR` means the old block could not yet be completed; level and strategy remain
unchanged, but compression progress and emitted output are retained. Provide more output
room and retry. The live stream and its allocation set are preserved on either result.

**Outside focused scope:** invalid level/strategy gives `Z_STREAM_ERROR` without changes.
A needed block flush can also return `Z_STREAM_ERROR`, including after finishing has begun.

## deflateTune

```c
int ZEXPORT deflateTune(z_streamp strm, int good_length, int max_lazy, int nice_length, int max_chain);
```

Set the four expert match-search tuning values.

**Domain:** restricted domain (live stream); all `int` tuning arguments are covered.
**Effect:** update tuning fields.

**Pre:** live stream.

**Post:** return `Z_OK`. Store `good_length`, `max_lazy` and `max_chain` after conversion
to unsigned, and `nice_length` as signed. No input is consumed, no output is delivered and
no allocation occurs. A changed level in `deflateParams`, or `deflateReset`, restores
standard tuning. This setter contract alone does not establish later compression bounds
or safety for every tuning choice; the C recommends `max_lazy >= 3` and `max_chain >= 4`.

## deflateBound_z

```c
z_size_t ZEXPORT deflateBound_z(z_streamp strm, z_size_t sourceLen);
```

Compute a size bound using the stream's current configuration and wrapper.

**Domain:** restricted domain (live stream and readable retained header); every
`z_size_t sourceLen` is included. **Effect:** query.

**Pre:** live stream and shared header conditions. For the output-capacity guarantee below,
call after init and any dictionary/header setup, before compression. Keep configuration,
header and dictionary fixed; use standard tuning and no inserted prime bits.

**Post:** the heap is unchanged. The numerical target is the following mathematical value,
saturated at `SIZE_MAX`, where `n = sourceLen` and `w` is the full wrapper size:

- Window 15 and memory level 8: `n + floor(n/4096) + floor(n/16384) + floor(n/33554432) + 7 + w`.
- Otherwise, if window bits are at most hash bits and level is nonzero:
  `n + floor(n/8) + floor(n/256) + floor(n/512) + 4 + w`.
- Otherwise: `n + floor(n/32) + floor(n/128) + floor(n/2048) + 7 + w`.

`w` is 0 for raw, 6 for zlib plus 4 when preset history is present, or 18 for gzip plus
its optional extra field (including two length bytes), terminated name/comment and header CRC.

**Output capacity:** separately from the numerical formula, for a representable adequate
buffer, when the input and output sizes fit `avail_in` and `avail_out`, supplying all
`n` bytes to one `deflate(Z_FINISH)` with at least the bound of output room must return
`Z_STREAM_END`. A clean schedule using only `Z_NO_FLUSH` before
`Z_FINISH` has the total-output bound. Other flush schedules can exceed it.
A saturated result is not a promise that an addressable buffer of that size exists.

**Outside focused scope:** NULL or a safely checkable invalid stream receives the larger
of the fixed/stored formulas above, plus 18, with saturation. There is no error code.
The public numerical goal still includes every readable gzip header length, including
lengths outside the focused 16-bit extra-field range; this page does not remove that obligation.

## deflateBound

```c
uLong ZEXPORT deflateBound(z_streamp strm, uLong sourceLen);
```

Return the `uLong` form of the compression bound.

**Domain:** restricted domain, as `deflateBound_z`; every `uLong sourceLen` is included.
**Effect:** query.

**Pre:** the `deflateBound_z` conditions apply.

**Post:** return its numerical result if it fits `uLong`, otherwise `ULONG_MAX`.
On the default LP64 target both types have 64 bits and the results agree.
The stream is unchanged. Output adequacy requires the separate schedule and capacity
conditions of `deflateBound_z`, rather than following from the numerical equality alone.

## deflate

```c
int ZEXPORT deflate(z_streamp strm, int flush);
```

Accept input and deliver part or all of a valid compressed stream.

**Domain:** restricted domain. **Effect:** consume input, emit output and update progress.

**Pre:** live stream with valid buffers and any active header. `next_out` is non-NULL and
`avail_out > 0`; `next_in` may be NULL only with zero input. `flush` is `Z_NO_FLUSH`,
`Z_PARTIAL_FLUSH`, `Z_SYNC_FLUSH`, `Z_FULL_FLUSH`, `Z_FINISH` or `Z_BLOCK`.
If output fills during a flush, continue with the same flush and more room.
After finishing begins, supply no new input and continue only with `Z_FINISH`.
For ordinary format validity, begin from init/`deflateReset` (or a copy of that history),
use legal dictionary/header setup, standard tuning and no arbitrary priming.

**Post:** accept `used <= old avail_in` bytes and deliver `made <= old avail_out` bytes.
Pointers advance by those amounts, available counts fall by them, and totals increase by
them with unsigned wrapping. Input stays unchanged; output outside the delivered prefix
stays unchanged. Some input can remain when output fills. No allocation or free occurs.

Across calls, delivered bytes form a prefix of a valid encoding of accepted input, using
the chosen wrapper, settings and preset dictionary. Completed output decodes to that input.
This specifies valid output, not one unique compressed byte sequence. `adler` tracks accepted
input using Adler-32 for zlib and CRC-32 for gzip after header emission; raw has no input checksum.

`Z_OK` means continuation may be needed. `Z_STREAM_END` occurs only with `Z_FINISH`, after
all supplied input and all compressed output, including trailer, have been delivered.
The live state remains owned until `deflateEnd` or reusable via `deflateReset`.

When a requested flush is fully delivered, `Z_BLOCK` completes a block without byte padding;
`Z_PARTIAL_FLUSH` adds an empty fixed block; `Z_SYNC_FLUSH` makes all preceding input available
to a decoder and ends with an aligned empty stored block. `Z_FULL_FLUSH` also resets match
history: later blocks do not refer before that completed flush. Restarting a raw decoder there
requires retaining the exact boundary and delivering the entire flush marker first.
`Z_FINISH` closes the final block and writes the wrapper trailer.

**Errors:** `Z_BUF_ERROR` covers zero output room, no possible progress with no input and
no stronger flush, or input offered after final-block processing began. It preserves a
live stream; provide room/input as appropriate. `Z_STREAM_ERROR` covers the stream check,
invalid flush (including `Z_TREES`), invalid NULL I/O combinations, or non-finish flush after
finishing began. Initial argument refusals consume no input or output. A later
`Z_BUF_ERROR` for new input after finishing may first deliver old pending output; no new
input is accepted. `msg` and remembered flush can change. The unchanged public goal
includes all signed flush values and these refusals.

## deflateEnd

```c
int ZEXPORT deflateEnd(z_streamp strm);
```

Release the compressor, discarding any unfinished work.

**Domain:** restricted domain. **Effect:** free owned state.

**Pre:** live stream in any phase, with the default free routine intact.

**Post:** free all five owned allocations exactly once and set `state` to NULL.
Caller input/output and header storage are unchanged and remain caller-owned.
Return `Z_DATA_ERROR` if the saved status is busy, otherwise `Z_OK`.
Both results release everything: `Z_DATA_ERROR` reports unfinished compression, not failed cleanup.
No later compression call is valid until reinitialisation.

**Outside focused scope:** a failed stream check, including a second end, returns
`Z_STREAM_ERROR` without freeing anything. Return status depends on internal compression
phase, not merely whether every produced byte was delivered.

## deflateCopy

```c
int ZEXPORT deflateCopy(z_streamp dest, z_streamp source);
```

Create an independent compressor with the same compression progress.

**Domain:** restricted domain. **Effect:** allocate and copy owned state.

**Pre:** `source` is live. `dest` is a different writable `z_stream` with no owned state,
separate from the source's memory. Source buffers and any retained header satisfy their lifetimes.

**Post:** `Z_OK` gives `dest` five new owned allocations containing equivalent compression
state; the source is unchanged. The copied stream fields include totals, allocator fields,
I/O pointers and retained header pointer. Internal owned pointers are relocated to the new
allocations. Both streams require their own `deflateEnd` and can continue independently.
Their copied caller I/O pointers initially refer to the same buffers; assign separate output
room before continuing both. The header remains shared caller-owned storage.

`Z_MEM_ERROR` frees every new allocation, clears `dest->state` and leaves other destination
fields and the source unchanged. There is no new live state to release.

**Outside focused scope:** NULL destination gives `Z_STREAM_ERROR`; a failed source check
also clears a non-NULL destination's state. The public goal explicitly assumes distinct
streams. Self-copy and overwriting an already live destination are excluded here and do not
receive a leak-free contract.
