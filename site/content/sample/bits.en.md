[Block encoding](/sample/blocks.html#example) gives the selected `ABABABAB` example six fields: a 3-bit header, two 8-bit literals, a 7-bit length code, a 5-bit distance code and a 7-bit end marker. Padding each field to a byte would insert extra bits between fields and change what the decoder reads. The writer must join the fields directly, split off complete bytes and retain the unfinished tail.

The six fields contain 38 meaningful bits; final alignment gives five bytes, `73 74 82 40 00`. We first determine the value passed for each field, then trace all five bytes through the 16-bit register. Afterwards we distinguish two locations: encoded bytes first occupy internal pending storage, and the application receives them only when they are copied to its output buffer.

## Code words and arrival order {#order}

DEFLATE writes ordinary numeric fields with the least significant bit first. Huffman code words are consumed in code-word order, with the most significant bit of the word first. zlib reconciles these rules by storing a **reversed canonical word** in its encoding table. The bit writer can then treat both kinds of field as an integer whose low bit is the next bit to send.

For example, the fixed canonical word for literal A is `01110001`. Reverse those eight positions and the integer given to `send_bits` is `10001110`, hexadecimal `8e`. Reading that integer from bit 0 upward sends `0,1,1,1,0,0,0,1`: exactly the original canonical word. This is not a reversal of the stream after it has been written.

For the final fixed block, the three-bit numeric header is value 3. Its low-first order is `1,1,0`: final flag 1 followed by fixed block type `01` in its numeric field order. Each writer request has a numeric `value` and a bit count `length`. This count is the encoded field width, not the number of original bytes a match will copy. The complete calls for our selected example are:

| Field | Writer `value` (hex) | `length` (decimal) |
| --- | --- | --- |
| Final fixed header | `03` | 3 |
| A | `8e` | 8 |
| B | `4e` | 8 |
| Length 6 | `10` | 7 |
| Distance 2 | `10` | 5 |
| End of block | `00` | 7 |

Here `10` is hexadecimal `0x10`, or decimal 16. The equal numeric value for the length and distance does not make them the same field. Their widths and their roles in the format differ.

## The example across register boundaries {#trace}

The implementation first holds up to 16 bits in a register: `bi_buf` is its content and `bi_valid` counts meaningful bits. The pending array contains complete bytes already written. Watch both locations first; the implementation equations follow afterwards. The hexadecimal register values below put the high bit on the left; emission still takes the low byte first.

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

<div class="zl-demo-mount" id="writer"><zlib-demo kind="writer"><p>Start with an empty 16-bit register. Append header, A, B, length, distance and end code. The B append writes 73 74; the end code writes 82 40; final alignment writes 00.</p></zlib-demo></div>

## A sixteen-bit staging register {#register}

The state fields are `bi_buf`, the register, and `bi_valid`, the number of meaningful low bits it contains. Pending bytes precede these held bits in the logical output. For the equations, shorten the existing valid-bit count to `r = bi_valid`, the new field value to `v = value`, and its width in bits to `l = length`. Thus the B append has `r = 11`, `v = 0x4e`, `l = 8`. The writer appends the low `l` bits of `v` after the existing `r` bits. The shift `v << r` places the new field at the first free bit, and bitwise `OR` joins it to the old register. The entry conditions ensure the field fits its declared width and other register bits do not interfere with that concatenation.

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

The real C is the overflow branch of the release [`send_bits` macro, trees.c:276–281](https://github.com/madler/zlib/blob/757f0527154291bcf6bfbd6396ecde6bedd2db95/trees.c#L274-L286). A trailing backslash continues the macro onto the next line. This excerpt stops within the `if` branch; the source link includes its `else`. `Buf_size` names the register capacity in bits and is 16. In this macro, `len` is the new field width, `val` is a local integer copy of its value, `s` points to the compressor state, and `put_short` writes a two-byte word low byte first.

```c
if (s->bi_valid > (int)Buf_size - len) {\
  int val = (int)value;\
  s->bi_buf |= (ush)val << s->bi_valid;\
  put_short(s, s->bi_buf);\
  s->bi_buf = (ush)val >> (Buf_size - s->bi_valid);\
  s->bi_valid += len - Buf_size;\
```

Substitute the B append line by line. The first line tests `11 > 16−8` and enters the branch. The second takes value `0x4e`. The third shifts it left by 11, combines it with old register `0x0473`, and retains `0x7473` in the 16-bit register. The fourth emits low byte first: `73 74`. The fifth shifts right by `16−11 = 5`, leaving `0x0002`. The sixth sets the valid count to `11+8−16 = 3`. This is the B row of the trace above.

These equations describe the bit operations; the actual C includes its stated casts and machine widths. The overflow branch uses a strict greater-than test. At **exactly 16 valid bits**, the fit branch leaves the full register in place. Compare the three cases:

| Old valid count r | New field width l | After this call |
| --- | --- | --- |
| 11 | 4 | Retain all 15 bits |
| 11 | 5 | Retain exactly 16 bits |
| 11 | 8 | Emit 16 of 19 bits and retain 3 |

A full register has not necessarily been emitted. The middle row becomes pending bytes only on a later overflowing append or flush.

This staging avoids a byte write for every short code or extra-bit field. It also makes the state less obvious: encoded bits may already have a definite meaning while remaining inside the register.

## Flush, alignment and delivery {#delivery}

`bi_flush` writes complete bytes while retaining a partial byte. With 16 valid bits it writes two bytes and clears the register; with 8 through 15 it writes one byte and keeps the remaining bits. With fewer than eight it does nothing. The output remains ready for a later field to continue the same byte.

`bi_windup` instead closes the partial byte. It writes one or two bytes as needed, clears the register and records the meaningful-bit count of the last byte in `bi_used`. It is used where the format requires alignment, including the end of a final block. Applying it between arbitrary fields would insert padding into the encoded data.

Delivery has a separate byte account: `pending` counts internally buffered bytes not yet delivered, `pending_out` points to the first of them, `next_out` points to the caller's next destination, and `avail_out` counts writable caller bytes. `total_out` is the cumulative delivered-byte count. Neither register operation by itself means the application has received those bytes. `flush_pending` first calls `_tr_flush_bits` to expose complete held bytes, then copies at most `min(pending, avail_out)` bytes to `next_out`. It advances both output cursors, updates `total_out`, reduces `avail_out` and the pending count, and restores `pending_out` to the buffer base once all pending bytes have been delivered. Small caller buffers therefore affect delivery without changing the already encoded fields.

The same fields are now five bytes. Even when the caller accepts only two bytes at a time, delivery splits existing bytes without changing their encoding. One memory question remains: where does the space for these writes come from? [Shared storage](/sample/storage.html) places the five output bytes and three unread records in one allocation and explains why emission must preserve the next record.

The writer composition proof over the full public domain is unfinished. Actual call paths must establish register and capacity conditions and carry the returned state into later emission or delivery. [Exact bit output](/sample/proof.html#bitstream) shows local theorems composing along one bit sequence; [the bit-output implementation argument](/reference/docs/proof/trees.html#bits-pending-bytes-and-compress_block) gives detailed conditions. [deflatePending](/reference/functions/deflatePending.html) lets callers query pending-byte and held-bit counts.
