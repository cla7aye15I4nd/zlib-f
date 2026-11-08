## From recovered bytes to checked data {#connection}

The [decoding chapters](/sample/decode-copy.html) explain how to recover bytes from a compressed body. The [wrapper chapter](/sample/wrappers.html#completion) still has one step to complete: **once bytes have been recovered, how does the receiver check them against the sender’s data?** This is where checksums join the same processing path.

Keep the eight-byte example `ABABABAB`. While compressing, the sender computes a checksum of these eight **uncompressed bytes** and writes it in the wrapper trailer. The receiver recovers bytes, computes their checksum, and compares it with the trailer. Damage may leave a body that still decodes to another byte sequence; a checksum mismatch then reports a data error. A match rules out many corruption cases but does not authenticate the data.

<figure class="bk-checksum-flow" aria-label="Checksum flow at the compressor and decoder">
<div><span>Sender</span><p><b>Original bytes</b><code>ABABABAB</code></p><i aria-hidden="true">→</i><p><b>Compressed body</b><small>Produced by deflate</small></p><i aria-hidden="true">＋</i><p><b>Trailer checksum</b><code>Adler-32: 093c020d</code><small>A summary of the same original bytes</small></p></div>
<div><span>Receiver</span><p><b>Compressed body</b><small>Decoded by inflate</small></p><i aria-hidden="true">→</i><p><b>Recovered bytes</b><code>ABABABAB</code></p><i aria-hidden="true">→</i><p><b>Recompute and compare</b><code>093c020d = 093c020d</code><small>Compare with the received trailer</small></p></div>
<figcaption>This picture uses a zlib wrapper. Gzip uses CRC-32 in the same role; raw DEFLATE has no checksum trailer. The checksum covers original bytes, not the compressed body.</figcaption>
</figure>

“What bytes did decoding produce?” must therefore connect to “which bytes does this checksum describe?” The arithmetic helper does not know whether the decoder has already counted a buffer. Its caller supplies exactly the newly processed slice. [Wrapper byte ranges](/sample/wrappers.html#checksums) explain that handoff; the proof chapter later connects it to actual memory reads.

## Two algorithms for two wrappers {#formats}

Adler-32 and CRC-32 are not consecutive stages in compression. They perform the same job for different wrappers. Start with the branch needed for your format.

| Format | What is checked | Chapter in this topic |
| --- | --- | --- |
| zlib | Adler-32 of uncompressed data | [Two running sums produce a checksum](/sample/adler.html) |
| gzip | CRC-32 of uncompressed data; length is also stored | [Shifts and XOR produce a checksum](/sample/crc.html) |
| Raw DEFLATE | No checksum field in this format | Review [body versus wrapper](/sample/wrappers.html#layout) |

## Incremental updates and chunk combination {#combination}

The [streaming example](/sample/stream-state.html#history) retrieves eight bytes through a five-byte output buffer: first `ABABA`, then `BAB`. The buffer changes, but the data still forms one `ABABABAB`. Its checksum must continue across the calls rather than restart with each buffer.

Combination handles a different case. Two workers have independently processed two chunks and retained only their checksums. They want the checksum of those chunks concatenated in order. The operation combines **summaries**; it does not concatenate compressed streams or compose two proofs.

| How the data arrives | What is available | Operation |
| --- | --- | --- |
| `ABABA`, then `BAB` | A running checksum and the next original bytes | **Continue updating**: pass the first result into the next update |
| Both chunks have already been processed independently | Two checksums and the second chunk’s length, 3 bytes | **Combine chunks**: use the matching `combine` API without rereading bytes |

Both paths should produce the same checksum of `ABABABAB`. For Adler-32, the first chunk gives `03da0148`, the independent second chunk gives `018d00c6`, and their concatenation gives `093c020d`. The next chapter derives these values byte by byte before explaining why the second length lets the summaries be combined.

## Reading this topic {#reading-path}

1. **[Adler-32](/sample/adler.html)**: use addition to understand summaries, incremental updates and independent chunk combination, then see why delayed remainders reduce work.
2. **[CRC-32](/sample/crc.html)**: solve the same task with shifts and XOR, then examine tables, word reads and combination operators. This is an alternative algorithm branch and can be read directly.
3. **[The checksum proof argument](/sample/checksum-proof.html)**: connect “the right number” to “exactly the corresponding bytes,” including optimized execution paths, memory bounds and combination lengths.

For the checksum’s place in zlib, return to [wrapper completion and trailer comparison](/sample/wrappers.html#completion). For exact calls, open the [checksum API](/reference/docs/spec/api/checksums.html). When using gzip file operations, the [file reading path](/sample/gzip.html#reading) also explains how checksum errors reach the application.
