## One decoding task, several calls {#connection}

[Decoding](/verification/decoding.html) showed how `73 74 82 40 00` restores `ABABABAB`: five compressed bytes describe eight original bytes. A real application must also decide how to receive them. Files can be large, network input can arrive in pieces, and the output buffer may not hold the whole result.

**Streaming** carries one compression or decompression task across several function calls. The caller supplies the currently readable input and writable output; the library preserves its stage of work. Replacing a buffer does not restart the task, and temporarily exhausting input or output does not complete it.

Offer `inflate` only five output slots in this example:

<ol class="bk-route-flow" aria-label="Receive eight result bytes through a five-byte buffer">
<li><strong>First call</strong><code>Output ABABA</code><span>Three match bytes remain, at distance two</span></li>
<li><strong>Deliver this batch</strong><span>The application handles five bytes</span><span>The library retains the suffix needed to resume</span></li>
<li><strong>Second call</strong><code>Output BAB</code><span>Continue the match, then read the final block's end</span></li>
<li><strong>Raw stream complete</strong><code>ABABA ++ BAB</code><span>The application has all of ABABABAB</span></li>
</ol>

## Preserve the unfinished work {#saved-work}

At the first return, the decoder must neither reread the match instruction nor act as though all six bytes were copied. It must retain “three bytes left, distance two” and the B and A needed for the next reads. Two integers alone are insufficient: the application may overwrite old output memory, so the required bytes need their own valid storage.

[Stream state](/sample/stream-state.html) supplies a complete runnable C program, then develops these two actual calls: movement of `next_in` and `next_out`, the ordinary decoder's suspension point, and the separate work saved for bits, table construction and matches. Compression has the same delivery concern: accepting input does not mean all compressed bytes representing it have reached the application. Pending output must be drained to complete `Z_FINISH`.

## The wrapper surrounds the body {#framing}

The diagram uses raw DEFLATE, so finishing the final block completes the stream. Zlib and gzip add a **wrapper** around the same body: a header selects the format and required context, and a trailer carries a check of the original bytes. Gzip also records output size.

[Headers and wrappers](/sample/wrappers.html) uses the three-byte original text `ABC` to expose the complete byte layout. The smaller example makes every header, body and trailer byte visible. The application can have all of `ABC` while four zlib trailer bytes are still missing. Supplying that trailer performs validation without adding original output. A mismatch also cannot retract the `ABC` already delivered.

[Checksums and combination](/verification/checksums.html) develops the check over those original bytes. When output arrives in two batches, the accumulator must continue across them rather than restart when a buffer changes. Zlib uses Adler-32 and gzip uses CRC-32. Both check the original data, not the compressed body.

## Connect returns into one result {#guarantees}

The cross-call guarantee is that the second batch extends the first, the saved state accurately describes the remaining task, and even input or allocation errors retain the effects that really occurred. [Correctness across calls](/sample/stream-proof.html) starts from `ABABA` and `BAB`, connecting input evidence, the retained ring, replaceable caller buffers and wrapper completion in the same execution. It also follows a subtle exit: a decoder can write output before failing to allocate its retained window.

When writing a calling loop, use the full [`inflate`](/reference/functions/inflate.html) and [`deflate`](/reference/functions/deflate.html) contracts to distinguish a temporary block, dictionary request, completion and error.

## Continue, restart or release {#lifetime}

A call may pause, but a whole task may also be cancelled, reset or copied into a checkpoint. Those actions change more than data positions: they affect ownership of windows and tables. [State and memory](/verification/lifecycle.html) develops this boundary. Another call continues the task, Reset starts a different task, Copy preserves two independent continuations, and End releases private storage.
