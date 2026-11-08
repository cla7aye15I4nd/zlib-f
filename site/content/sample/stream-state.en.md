The decoder in [the match-copy chapter](/sample/decode-copy.html) can turn a length and distance into bytes. An application adds another boundary: its writable buffer may end before the match does. The decoding task continues across that boundary, even when the application supplies a different allocation next time.

We will follow the same `ABABABAB` result through two output buffers. Then we will place that example inside the real input, output and return protocol. [The stream proof](/sample/stream-proof.html) follows the same saved state and byte history.

## Saved work {#suspension}

`inflate` is a state machine because almost every stage can need more input or output. It cannot assume that a call contains a whole header, a whole Huffman code, or enough space for a whole match. Its private `inflate_state` records which stage has reached a boundary and what that stage has already learned.

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

## Two buffers, one history {#history}

Start with two literal symbols, `A` and `B`, followed by a match of length 6 and distance 2. Give the first call five output slots. The literals use two slots; three match iterations fill the remaining three:

```text
logical output:  A B A B A
match progress:      1 2 3       remaining = 3, distance = 2
```

The saved mode is still `MATCH`. Parsing the length/distance again would duplicate the operation. Forgetting the remaining length would truncate it. Merely saving those two integers would also be insufficient if the bytes needed by the distance had disappeared.

<div class="zl-demo-mount"><zlib-demo kind="stream"><p>With output capacity 5, the first call produces ABABA and retains three match bytes. Supply a new buffer: the next call produces BAB, giving ABABABAB.</p></zlib-demo></div>

At return, the decoder retains the necessary suffix in its own history window. The application may then deliver, overwrite or release the first output buffer according to the caller-storage contract. The second call does not gain permission to read an invalid old pointer just because the logical output is unchanged.

For the three remaining bytes, the source changes as output grows:

| Next byte | Distance-two source | Byte written into the new buffer |
| --- | --- | --- |
| 1 | The `B` in retained history | `B` |
| 2 | The final `A` in retained history | `A` |
| 3 | The first `B` just written into this buffer | `B` |

The ring window represents a suffix, not necessarily the entire output. `wsize` is its capacity, `whave` the valid byte count, and `wnext` the next write position. When full, chronological history begins at `wnext` and wraps around. `updatewindow` keeps only the newest full window when enough bytes were produced; otherwise it appends the new suffix, possibly with two physical copies across the ring boundary.

The demonstration executes a chosen symbol sequence. It does not claim an exact compressed-input consumption count or simulate the real function's return codes. A real final stream also needs its end-of-block and wrapper completion steps. Those may occur after the last data byte has been written.

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

Compression has its own pipeline: accepted input enters the window and lookahead; matching commits symbols; [block output](/sample/blocks.html) encodes them; [pending storage](/sample/bits.html#delivery) later delivers bytes. These are distinct progress positions. An input byte can be accepted before any compressed byte representing it reaches the application. Conversely, a call with no new input can still deliver already pending output.

Ordinary use sends data with `Z_NO_FLUSH`, then requests `Z_FINISH`. Once finishing has started, continue with `Z_FINISH`, provide room as needed, and add no new input until `Z_STREAM_END`. A full output buffer does not by itself establish that the final block, padding and trailer have all been delivered. `deflateEnd` releases resources; it does not perform a missing finish operation.

`Z_SYNC_FLUSH` makes accepted data available through a completed, byte-aligned flush boundary while retaining compression history. `Z_FULL_FLUSH` adds a restart boundary and clears the matching history used for future compression. Both require enough calls and output space to finish the requested flush. `Z_BLOCK` stops at a block boundary without the same byte-alignment promise; `Z_PARTIAL_FLUSH` uses its documented partial-flush mechanism. These choices are not synonyms for finishing the stream. Their exact allowed sequences are in [deflate](/reference/functions/deflate.html).

The next chapter follows what must surround the DEFLATE body: [headers, dictionaries and trailers](/sample/wrappers.html). Then [the stream proof](/sample/stream-proof.html) connects input prefixes, retained history, actual return paths and completion.
