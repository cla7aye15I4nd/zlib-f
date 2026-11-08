## From pending records to caller bytes {#connection}

The compressor has [selected literals and matches](/verification/matching.html) and can [construct Huffman codes](/verification/huffman.html) from their frequencies. The application still needs bytes it can pass to a decoder. Three connected jobs remain: select a block form, join its fields into adjacent bits, and deliver complete bytes to the caller.

Continue with the selected `A`, `B`, length 6/distance 2, which expand to `ABABABAB`. In a final fixed block, the header, two literals, length code, distance code and end marker occupy 38 meaningful bits. Completing the last byte gives `73 74 82 40 00`. Fixed coding makes a complete trace possible here; this does not predict the symbols or block form selected by an actual zlib call.

<figure class="bk-route-flow" aria-label="Records becoming caller output"><ol><li><strong>Records</strong><span>A, B, length 6/distance 2: three symbols occupying nine internal record bytes.</span></li><li><strong>Block fields</strong><span>With fixed coding selected, add the header and end marker for 38 meaningful bits.</span></li><li><strong>Internal bytes</strong><span>The bit writer produces 73 74 82 40 00; bits short of a byte remain in its register.</span></li><li><strong>Caller output</strong><span>Deliver two bytes and then three: the compressed data remains the same.</span></li></ol><figcaption>Record bytes, original bytes and compressed bytes have separate counts: three records represent eight original bytes and occupy five compressed bytes.</figcaption></figure>

## Choose a block the receiver understands {#blocks}

[Block forms and costs](/sample/blocks.html) starts from those nine record bytes and derives the fixed block's 38 bits. It places the other choices at the same decision point: dynamic coding pays for a description in exchange for shorter payload; stored coding copies original bytes and requires that source range to remain readable. These are alternative branches, not three consecutive steps.

[Bit writing and delivery](/sample/bits.html) follows the same fields. After the header and A, the register holds 11 bits. B adds 8, crossing its 16-bit boundary: the writer emits `73 74` and keeps three bits. This explains why code words cannot each be padded to a byte, and why encoding bits and delivering bytes happen at different times.

## Output must not catch unread records {#storage}

The default layout saves a separate allocation by letting pending records and compressed output share memory. The writer must preserve bit order and let the next record survive until it is read. [Shared storage](/sample/storage.html) first places our three records and five output bytes on one address axis, then derives the need for a cost bound at every prefix. Fitting at completion does not guarantee that earlier writes preserved unread input.

[Encoding, storage and delivery agreement](/sample/proof.html) combines the guarantees along this process: records expand to the right input; each append writes the right bits; output preserves unread records; and a small-buffer return remembers the undelivered suffix. This is also where Huffman construction meets memory safety: a dynamic block's total-cost comparison does not supply its prefix-space bounds.

Once the five bytes reach the receiver, [decompression and decoding](/verification/decoding.html) reverses this process to recover eight original bytes. zlib and gzip add [wrapper and checksum fields](/verification/streaming.html) outside this raw block. The [streaming interface](/sample/interfaces.html) and complete [deflate contract](/reference/functions/deflate.html) explain caller space, resumption and stream completion.
