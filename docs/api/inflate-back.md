# Callback decompression

[API manual](README.md) · [Shared stream rules](streams.md) · [Stream decompression](inflate-stream.md)

The callback interface lets a caller supply input chunks and receive decoded output directly
from its window. Start with [inflateBackInit_](#inflatebackinit_), decode with
[inflateBack](#inflateback), and release state with [inflateBackEnd](#inflatebackend).
The caller's window remains caller-owned throughout.

These focused contracts follow the pinned [infback.c](../../zlib/infback.c) and
[zlib.h](../../zlib/zlib.h) in the default LP64 Linux build. Source readings are **to confirm**
by proof. Their restricted domains do not narrow the broader targets in
[Back.lean](../../ZlibF/Spec/Public/Back.lean) or
[Sequences.lean](../../ZlibF/Spec/Public/Sequences.lean). See
[contract conventions](contracts.md) for domain/effect labels and
[overview](../overview.md) for proof status and remaining work.

`inflateBack` decodes raw DEFLATE. The caller handles any zlib/gzip header, trailer and checksum.
The caller owns a writable window of at least `2^windowBits` bytes. It is also the output buffer.
Use 15 bits and 32768 bytes for general streams; smaller windows can reject valid long distances.

```mermaid
flowchart LR
    I["inflateBackInit_: allocate state"] --> B["inflateBack: decode one stream"]
    B -->|another stream| B
    B -->|success or decode error| E["inflateBackEnd: free state"]
    I -->|no decode needed| E
```

The callbacks have these types:

```c
typedef unsigned (*in_func)(void FAR *, z_const unsigned char FAR * FAR *);
typedef int (*out_func)(void FAR *, unsigned char FAR *, unsigned);
```

`in(in_desc, &buf)` returns a byte count and sets `buf`; zero means no input and ignores `buf`.
`out(out_desc, buf, len)` receives up to one window of bytes; zero means success.
Descriptors may be NULL if the callback supports that value.

## inflateBackInit_

```c
int ZEXPORT inflateBackInit_(z_streamp strm, int windowBits, unsigned char FAR *window,
                             const char *version, int stream_size);
```

**Purpose.** Allocate decoder state and attach the caller's window.
The `inflateBackInit` macro supplies `version` and `stream_size`.

**Domain.** Restricted domain: valid caller memory, an inactive stream and default allocation.

**Pre.** A non-NULL `strm` points to a writable `z_stream` with initialized `zalloc`, `zfree`
and `opaque`. Use NULL or the default allocator/free pair; do not overwrite live library state.
A non-NULL `version` has a readable first byte. On the initialization path, `window` provides
`2^windowBits` writable bytes separate from the stream. Keep that slice alive until end.

**Effects.** May initialize allocator fields and `opaque`, clear `msg` and allocate one state.
The window remains caller-owned and is not allocated, cleared or freed here.

**Post.** `Z_OK` attaches fresh state for `inflateBack` with `8 <= windowBits <= 15`.
Input/output pointers, availability counters, totals, `adler` and `data_type` are unchanged.
Only selected state fields are initialized; use this state with the callback API.

**Errors.** A NULL version, different major-version byte or wrong stream size gives
`Z_VERSION_ERROR` before stream access. NULL `strm`/`window`, or bits outside 8..15, gives
`Z_STREAM_ERROR`. Allocation failure gives `Z_MEM_ERROR`: `msg` and allocator defaults may
have changed, but the old `state` field is retained. No state was allocated, so no end call
is needed after failed init in this inactive-stream domain.

## inflateBack

```c
int ZEXPORT inflateBack(z_streamp strm, in_func in, void FAR *in_desc,
                        out_func out, void FAR *out_desc);
```

**Purpose.** Decode one complete raw stream through the input and output callbacks.

**Domain.** Restricted domain: a live callback decoder, valid separated slices and a finite,
returning callback protocol. Arbitrary malformed input bytes are included.

**Pre.** Init succeeded and end has not run. Keep the stream, state and window live.
Initialize `next_in`; NULL requests callback input immediately and ignores `avail_in`.
Otherwise initialize `avail_in` and provide that many readable bytes at `next_in`.
Initial and callback-provided input slices do not overlap the window, stream or private state.
Neither callback is NULL. Every callback returns safely and the total input supplied is bounded.

Callbacks may read only the input/output bytes supplied to them and their own valid objects.
They may update, allocate or free their own memory, but preserve the stream, private state and
window slice. An input chunk remains readable and unchanged until the next input callback or
return, including across output callbacks. Output callbacks read at most `len` window bytes.
Callback storage and the window may share an allocation when their used byte slices do not overlap.
No concurrent or re-entrant access to this stream is allowed.

**Effects.** Reset decoding for a new stream, consume input, write the window and invoke callbacks.
Full windows and a final nonempty partial window are delivered to `out`, including on error.
Callbacks may therefore observe output before a later format or input failure.
The library allocates and frees nothing; callback allocations remain the caller's responsibility.

**Post.** `Z_STREAM_END` means the complete raw stream was decoded and every output call succeeded.
The concatenated chunks are its uncompressed bytes, with no preset dictionary.
`next_in`/`avail_in` identify the unread suffix of the initial or last callback chunk.
After input exhaustion they are NULL/zero; otherwise the pointer advances by the consumed bytes.
Totals, `adler` and `data_type` are unchanged; `next_out`/`avail_out` are not the output interface.
The stream retains its state and window for another independent decode or end.

**Errors.** `Z_BUF_ERROR` means input exhaustion or a nonzero output result; it never returns `Z_OK`.
For `Z_BUF_ERROR`, NULL `next_in` identifies input exhaustion; non-NULL identifies output failure.
`Z_DATA_ERROR` means malformed DEFLATE and sets `msg`. A final output failure changes
`Z_STREAM_END` to `Z_BUF_ERROR`; it does not replace another error already selected.
NULL `strm` or NULL state gives `Z_STREAM_ERROR` without callbacks. Other invalid states are
outside this domain: a state from ordinary `inflateInit_` is not a callback decoder.
After a decode error, end still releases the state; another call starts a fresh stream.

## inflateBackEnd

```c
int ZEXPORT inflateBackEnd(z_streamp strm);
```

**Purpose.** Release the state allocated by callback init.

**Domain.** Restricted domain: a live callback decoder with valid default free, plus the checked
NULL-stream, NULL-state and NULL-free refusal cases.

**Pre.** For cleanup, init succeeded, end has not run and no decode or callback is active.
The stream and attached state remain valid; retain the matching `zfree` and `opaque`.
Cleanup is permitted after successful decoding and after any decode error.

**Effects.** Free exactly the internal state and clear `state`.

**Post.** `Z_OK` leaves `state` NULL. The caller's window and all other stream fields are unchanged.
The caller may now release or reuse its window; the library never frees it.

**Errors.** NULL `strm`, NULL state or NULL `zfree` gives `Z_STREAM_ERROR` and frees nothing.
These checks do not validate an arbitrary non-NULL state or detect ownership mistakes.

[Back to the API manual](README.md) · [Contract conventions](contracts.md)
