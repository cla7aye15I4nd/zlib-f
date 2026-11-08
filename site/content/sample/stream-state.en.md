Suppose an application needs to unpack a large file. It wants to hand recovered bytes to a consumer in small batches, using the same small output buffer again. It cannot reserve space for the entire recovered file, and the compressed input may also arrive in pieces. **Streaming** means calling the same decoder repeatedly, keeping its progress between calls.

For decompression, the direction is **compressed bytes in → original bytes out**. An output buffer is writable memory supplied by the application. Its capacity limits how many original bytes one call can write; it is unrelated to the total size of the file. The application handles the bytes just written before letting the next call reuse that memory.

## Decode eight bytes with five bytes of output space {#history}

Use the complete raw DEFLATE stream `73 74 82 40 00`. It describes two literal bytes, `A` and `B`, then a length-6, distance-2 match, followed by the end of the final block. Its recovered result is `ABABABAB`.

Here `inflate` is the decompression operation. Its `z_stream` argument is a persistent control record: it holds the current input/output bindings and a pointer to private decoder state. Keeping that record is how the next call resumes the task; the five-byte `output` array is only a temporary delivery area.

Give all five compressed bytes to `inflate`, but provide only five output slots. Keep the same `z_stream` for the next call and reuse those five slots. The [complete C program](../static/examples/inflate-chunks.c) initializes raw mode, runs this loop and releases the decoder. `next_in` initially points to the five compressed bytes and `avail_in` is 5. Those input fields are set once before the loop; each call keeps the remaining input position returned by the previous call. Here is the part that supplies output space and makes each call:

<!-- example:inflate-chunks#call -->

`next_out` points at the first writable slot; `avail_out` is the number of writable slots. `inflate` advances the pointer and reduces the count as it writes. `produced` is therefore the number of bytes that the application can read from `output` after this call. Rebinding the output buffer does not initialize a new decoder.

The program, run against the pinned C, gives this trace:

| Call | Compressed input consumed | Original bytes written | Return | What the application does next |
| --- | ---: | --- | --- | --- |
| 1 | 4 of the supplied 5 bytes | 5 bytes: `ABABA` | `Z_OK` | Handle these five bytes, then make the same buffer writable again. |
| 2 | The remaining 1 byte | 3 bytes: `BAB` | `Z_STREAM_END` | Handle these three bytes; this raw stream is complete. |

The application has received `ABABA` followed by `BAB`. The combined result is eight bytes; the physical output buffer has only five slots and is reused. It never contains eight bytes at once. These are concrete C execution results, not a universal proof of streaming correctness.

<div class="zl-demo-mount"><zlib-demo kind="stream"><p>A five-byte output buffer first receives ABABA, then is reused for BAB. The application combines the two batches into ABABABAB while the decoder preserves the unfinished match.</p></zlib-demo></div>

## Saved state between calls {#history-window}

The first two writes are the literals. Three further writes come from the match. At the first return, the decoder still owes the final three match bytes:

```text
received so far: A B A B A
match copies:       1 2 3       still to copy = 3, distance = 2
```

The saved stage is `MATCH`; its `length` is the remaining 3 and its `offset` is distance 2. It must resume copying, without decoding the same length/distance again. It also needs the bytes that the distance points to. Before returning, the decoder retains the necessary suffix in its own history window. The application may then deliver, overwrite or release its old output storage within the caller-storage contract.

| Next write in call 2 | Distance-two source | Byte |
| --- | --- | --- |
| 1 | `B` in retained history | `B` |
| 2 | Final `A` in retained history | `A` |
| 3 | First `B` just written in this call | `B` |

This is why retaining two integers is insufficient: the second call also needs valid byte storage. It must not read an invalid pointer into an old caller allocation. [Match copying](/sample/decode-copy.html) follows each source read.

The decoder needs a bounded store for old output that later calls can copy from. It uses a ring: writing past the last array slot continues at slot zero. The ring represents the newest suffix, which may be shorter than the full decoded result. `wsize` counts its capacity in bytes; `whave` counts valid history bytes; `wnext` is the zero-based array index for the next write. For example, appending `ABABA` to an empty eight-byte ring leaves five valid bytes and the next write at index 5. When full, chronological history starts at `wnext` and wraps around. `updatewindow` keeps the newest full window if enough bytes were produced; otherwise it appends new bytes, using two physical copies when it crosses the ring boundary.

## Where the C pauses {#c-pause}

`state->mode` selects the work to perform next. `MATCH` means expanding an already decoded length/distance pair; `LEN` means reading another literal/length symbol. The local variable `left` counts output bytes still writable in this call, so zero is a reason to pause the current match, not evidence that the match has ended.

The pinned [`MATCH` case](https://github.com/madler/zlib/blob/757f0527154291bcf6bfbd6396ecde6bedd2db95/inflate.c#L1027-L1032) starts with:

```c
state->mode = MATCH;
    /* fallthrough */
case MATCH:
    if (left == 0) goto inf_leave;
```

`left` is the writable space remaining in this call. In call 1 it becomes zero while three bytes remain in the match. The `goto` leaves `mode` as `MATCH`. Later in [the same case](https://github.com/madler/zlib/blob/757f0527154291bcf6bfbd6396ecde6bedd2db95/inflate.c#L1067-L1074), C reduces `state->length` by the amount copied and returns to `LEN` only when that remaining length reaches zero. This is the code-level explanation of “continue the same task.” Its universal preservation argument remains **to confirm** by execution proofs.

## Saved work {#suspension}

`inflate` is a state machine because almost every stage can need more input or output. It cannot assume that a call contains a whole header, a whole Huffman code, or enough space for a whole match. Its private `inflate_state` records which stage has reached a boundary and what that stage has already learned.

Two saved quantities recur in the table. `hold` is an integer containing bits fetched but not yet consumed; `bits` is the number of valid bits in that integer. The array `lens` holds code lengths, measured in bits, while the decoder builds a dynamic Huffman table. These are separate from the input byte count and from the lengths of output matches.

| Work in progress | Relevant modes and retained information |
| --- | --- |
| Wrapper header | `HEAD` and gzip header modes retain parsed flags, field lengths and metadata progress. |
| Block header or numeric field | `hold` and `bits` retain low-order bits already pulled from caller input. |
| Dynamic table description | `TABLE`, `LENLENS`, `CODELENS` retain counts, the initialized prefix of `lens`, and the description tables. |
| Symbol interpretation | `LEN`, `LENEXT`, `DIST`, `DISTEXT` retain the stage of length/distance decoding and required extra bits. |
| Stored bytes or match expansion | `COPY` or `MATCH` retains the number of bytes still to produce; a match also retains its distance. |
| Trailer | `CHECK`, then gzip `LENGTH`, retain the checksum and produced-length account while waiting for trailer bits. |

This table groups modes by their job; it does not merge the actual C cases. In particular, a pause before a distance is complete must not be resumed as though a match source had already been validated.

The bit buffer and caller input describe different places. Once a byte has been pulled, `next_in` has advanced past it, but some of its bits may still be in `hold`. Thus `avail_in == 0` means the caller's current range is exhausted. It does not mean the decoder has no bits left to interpret. Conversely, having buffered bits does not promise enough bits for the next field. [Input bits](/sample/input-bits.html) follows that boundary at individual bit positions.

The C loads several frequently used registers into local variables. A suspension normally reaches `inf_leave`, where `RESTORE` publishes the current pointers and bit registers. Those are the values after any reads or writes already performed. Leaving the loop does not undo a partially completed operation. This implementation reading is **to confirm** over the admitted public histories by the corresponding execution proofs.

## Caller-visible progress {#accounting}

Before a call, the application supplies readable bytes through `next_in/avail_in` and writable space through `next_out/avail_out`. Afterward, compute progress from the returned counts:

```text
used     = avail_in_before  - avail_in_after
produced = avail_out_before - avail_out_after
```

The new input pointer advances by `used`; the output pointer advances by `produced`. Unread input must be preserved. If the decoder consumed only part of a chunk, replacing that chunk with unrelated new data loses the rest of the compressed stream. The application can refill an exhausted range, or deliberately move/append data while maintaining the unread suffix and the correct binding.

`Z_OK` indicates progress without complete stream termination. `Z_BUF_ERROR` is not necessarily malformed data: the call may be unable to progress with the supplied input and room, or a `Z_FINISH` request may not yet complete. Retrying the same blocked configuration forever does not supply what is missing. `Z_NEED_DICT` asks for the required zlib dictionary. `Z_DATA_ERROR` reports a detected format or enabled integrity error, possibly after output. `Z_STREAM_END` identifies completion of this stream or gzip member, while trailing input can remain unread. The [exact inflate contract](/reference/functions/inflate.html) describes all cases and accepted flush values.

Counters need one further distinction. Normal return paths update totals and the enabled output checksum for the bytes produced. A delayed history-window allocation can fail after output has been written and pointers restored. That `Z_MEM_ERROR` path skips later total/checksum updates. It therefore cannot be interpreted as “nothing happened.” Use the returned pointers and counts to identify that call's effects; the proof chapter explains why one unconditional total-counter equation would be wrong.

## Compression and completion {#compression}

For compression, the direction is **original bytes in → compressed bytes out**. It has its own pipeline: accepted input enters the window; its unprocessed suffix is the lookahead used to compare possible matches. Matching commits symbols; [block output](/sample/blocks.html) encodes them; [pending storage](/sample/bits.html#delivery) later delivers bytes. These are distinct progress positions. An input byte can be accepted before any compressed byte representing it reaches the application. Conversely, a call with no new input can still deliver already pending output.

Ordinary use sends data with `Z_NO_FLUSH`, then requests `Z_FINISH`. Once finishing has started, continue with `Z_FINISH`, provide room as needed, and add no new input until `Z_STREAM_END`. A full output buffer does not by itself establish that the final block, padding and trailer have all been delivered. `deflateEnd` releases resources; it does not perform a missing finish operation.

`Z_SYNC_FLUSH` makes accepted data available through a completed, byte-aligned flush boundary while retaining compression history. `Z_FULL_FLUSH` adds a restart boundary and clears the matching history used for future compression. Both require enough calls and output space to finish the requested flush. `Z_BLOCK` stops at a block boundary without the same byte-alignment promise; `Z_PARTIAL_FLUSH` uses its documented partial-flush mechanism. These choices are not synonyms for finishing the stream. Their exact allowed sequences are in [deflate](/reference/functions/deflate.html).

The next chapter follows what must surround the DEFLATE body: [headers, dictionaries and trailers](/sample/wrappers.html). Then [the stream proof](/sample/stream-proof.html) connects input prefixes, retained history, actual return paths and completion.
