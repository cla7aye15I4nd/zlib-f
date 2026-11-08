The [block-selection chapter](/sample/blocks.html) determined six fields for our fixed block. Those fields contain 38 meaningful bits. They are not six byte-sized objects, and their boundaries do not line up with the output bytes. We now follow the implementation that packs them.

Two boundaries will matter throughout: a field becomes part of the encoded bit sequence, then complete bytes become available in pending storage. Delivery to the caller is a later operation.

## Code words and arrival order {#order}

DEFLATE writes ordinary numeric fields with the least significant bit first. Huffman code words are consumed in code-word order, with the most significant bit of the word first. zlib reconciles these rules by storing a **reversed canonical word** in its encoding table. The bit writer can then treat both kinds of field as an integer whose low bit is the next bit to send.

For example, the fixed canonical word for literal A is `01110001`. Reverse those eight positions and the integer given to `send_bits` is `10001110`, hexadecimal `8e`. Reading that integer from bit 0 upward sends `0,1,1,1,0,0,0,1`: exactly the original canonical word. This is not a reversal of the stream after it has been written.

For the final fixed block, the three-bit numeric header is value 3. Its low-first order is `1,1,0`: final flag 1 followed by fixed block type `01` in its numeric field order. The complete calls for our selected example are:

| Field | Writer `value` (hex) | `length` (decimal) |
| --- | --- | --- |
| Final fixed header | `03` | 3 |
| A | `8e` | 8 |
| B | `4e` | 8 |
| Length 6 | `10` | 7 |
| Distance 2 | `10` | 5 |
| End of block | `00` | 7 |

Here `10` is hexadecimal `0x10`, or decimal 16. The equal numeric value for the length and distance does not make them the same field. Their widths and their roles in the format differ.

## A sixteen-bit staging register {#register}

The state fields are `bi_buf`, the register, and `bi_valid`, the number of meaningful low bits it contains. Pending bytes precede these held bits in the logical output. Let `r = bi_valid`, `v = value`, and `l = length`. The writer appends the low `l` bits of `v` after the existing `r` bits.

When `r ≤ 16-l`, the field fits:

```text
bi_buf   := bi_buf OR (v << r)
bi_valid := r + l
```

When `r > 16-l`, part of the new field completes a 16-bit word. The implementation combines those low bits with the register, writes the word's low byte and then its high byte to pending storage, and retains the rest:

```text
write low 16 bits of (bi_buf OR (v << r))
bi_buf   := v >> (16-r)
bi_valid := r + l - 16
```

These equations describe the bit operations; the actual C includes its stated casts and machine widths. The fit test is strict in the overflow branch. At **exactly 16 valid bits**, the fit branch may leave the full register in place. Its contents are emitted by a later overflowing append or by a flush.

This staging avoids a byte write for every short code or extra-bit field. It also makes the state less obvious: encoded bits may already have a definite meaning while remaining inside the register.

<div class="zl-demo-mount" id="writer"><zlib-demo kind="writer"><p>Start with an empty 16-bit register. Append header, A, B, length, distance and end code. The B append writes 73 74; the end code writes 82 40; final alignment writes 00.</p></zlib-demo></div>

## The example across register boundaries {#trace}

Watch the register and the pending array together. The hexadecimal register values below put the high bit on the left; emission still takes the low byte first.

| Completed operation | `bi_buf` (hex) | `bi_valid` (decimal) | Newly pending bytes (hex) |
| --- | --- | --- | --- |
| Header | `0003` | 3 | — |
| A | `0473` | 11 | — |
| B | `0002` | 3 | `73 74` |
| Length 6 | `0082` | 10 | — |
| Distance 2 | `4082` | 15 | — |
| End of block | `0000` | 6 | `82 40` |
| Final alignment | `0000` | 0 | `00` |

The B call has 11 existing bits and eight new bits. Only five new bits fit into the current word; the remaining three become the new register. The end code similarly crosses the boundary from 15 to 22 bits. It emits a word and leaves six zero bits that still belong to the end code. Final alignment adds two padding zeros and writes the last byte.

The resulting raw bytes are `73 74 82 40 00`. Decoding this constructed stream recovers `ABABABAB`. That finite example checks our field accounting; it does not prove the writer for all inputs or assert the token choices of the real compressor.

## Flush, alignment and delivery {#delivery}

`bi_flush` writes complete bytes while retaining a partial byte. With 16 valid bits it writes two bytes and clears the register; with 8 through 15 it writes one byte and keeps the remaining bits. With fewer than eight it does nothing. The output remains ready for a later field to continue the same byte.

`bi_windup` instead closes the partial byte. It writes one or two bytes as needed, clears the register and records the meaningful-bit count of the last byte in `bi_used`. It is used where the format requires alignment, including the end of a final block. Applying it between arbitrary fields would insert padding into the encoded data.

Neither operation by itself means the application has received those bytes. `flush_pending` first calls `_tr_flush_bits` to expose complete held bytes, then copies at most `min(pending, avail_out)` bytes to `next_out`. It advances both output cursors, updates `total_out`, reduces `avail_out` and the pending count, and restores `pending_out` to the buffer base once all pending bytes have been delivered. Small caller buffers therefore affect delivery without changing the already encoded fields.

The next chapter places both the pending bytes and the unread symbol records into [their shared allocation](/sample/storage.html). That explains why a correct bit sequence and sufficient final capacity still leave an additional memory obligation.

The actual implementation reading and its caller-entry assumptions remain **to confirm** over the full public domain. The [bit-output component argument](/reference/docs/proof/trees.html#bits-pending-bytes-and-compress_block) leads to the relevant register and capacity obligations; [deflatePending](/reference/functions/deflatePending.html) exposes pending-byte and held-bit counts to callers.
