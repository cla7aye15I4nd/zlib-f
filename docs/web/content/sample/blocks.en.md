[Match selection](/verification/matching.html) replaces repetition with instructions saved as literal and length/distance records. The receiver cannot read those records directly. Block encoding chooses stored, fixed or dynamic representation for this data and writes a header that identifies the form. The dynamic candidate uses [codes built from frequencies](/verification/huffman.html), the fixed candidate uses prescribed codes, and the stored candidate copies original bytes.

Select one representation of `ABABABAB`: literals `A`, `B`, then “go back 2 bytes and copy 6.” The first two bytes give the decoder a source; expanding the match one byte at a time supplies the remaining `ABABAB`. In a final fixed block, the three records become six fields totaling 38 meaningful bits. Alignment gives `73 74 82 40 00`. We follow the nine record bytes to these five output bytes, then return to the source's cost comparison.

The three symbols are already selected here; an actual zlib call's symbols and block form depend on its search and strategy. The fixed-block example provides a complete record-to-bit trace without requiring dynamic tree construction first.

## Three block forms {#forms}

A DEFLATE block begins with the final-block flag and a two-bit block type. Its body can take one of three forms.

A **stored block** carries original bytes. It aligns to a byte boundary, writes a 16-bit length and its 16-bit complement, then copies the bytes. It avoids paying for a code description, but it needs the original byte range to remain available. An array of length/distance records cannot simply be copied as stored input.

A **fixed block** uses the code lengths prescribed by DEFLATE. The decoder already knows those codes, so the encoder sends no tree description. The data still goes through length/distance coding; fixed does not mean uncompressed.

A **dynamic block** sends a description of its own codes before the data. zlib builds the literal/length and distance trees, computes their lengths, and assigns canonical words. The decoder must reconstruct the same lengths and words before reading the first payload symbol.

For a small block, that description can cost more than it saves. For a larger block with a skewed distribution, shorter frequent codes can repay it. The decision depends on the entire block, including metadata.

## Symbols awaiting emission {#symbols}

A **literal** names one byte directly; a **match** names a byte count and a backward distance. The compressor keeps these choices until the block is ready to encode. In the default build without the alternative `LIT_MEM` storage layout, zlib stores each pending symbol in three bytes. The first two hold the distance, low byte first. A zero distance identifies a literal; the third byte is then the literal value. For a match, the distance is nonzero and the third byte holds `length - MIN_MATCH`, where `MIN_MATCH = 3` is the shortest match the format can represent. Subtracting that minimum maps allowed lengths 3 through 258 to offsets 0 through 255, which fit in one byte.

The encoder also needs an internal representation it can read back later. The three instructions occupy nine bytes in memory; these are not the final compressed output:

| Symbol | Stored distance bytes (hex) | Third byte (hex) | Expanded output |
| --- | --- | --- | --- |
| Literal A | `00 00` | `41` | `A` |
| Literal B | `00 00` | `42` | `B` |
| Length 6, distance 2 | `02 00` | `03` | `ABABAB` |

In the source, `s` points to the compressor state, `sym_buf` is the symbol-byte view, and `sym_next` is its next free byte offset. The value `dist` is the copy distance in bytes, or zero for a literal; `lc` is the literal byte or the length offset just described. These bytes come directly from the ordinary-layout branch of [`_tr_tally`, trees.c:1100–1102](https://github.com/madler/zlib/blob/757f0527154291bcf6bfbd6396ecde6bedd2db95/trees.c#L1100-L1102):

```c
s->sym_buf[s->sym_next++] = (uch)dist;
s->sym_buf[s->sym_next++] = (uch)(dist >> 8);
s->sym_buf[s->sym_next++] = (uch)lc;
```

The first line saves the low eight distance bits and advances the index. The second shifts by eight to save the high byte and advances again. The third saves the literal or length offset and advances once more. For the match `(dist, lc) = (2, 3)`, the stores are `02`, `00`, `03`. Non-debug builds also use inline tally macros; the function body makes each store in the same packed representation visible here.

The match record does not contain those six output bytes; the decoder will produce them from history. Put the three quantities side by side to see why they cannot share one counter:

| What is counted | This example | Where it matters |
| --- | --- | --- |
| Symbols awaiting encoding | 3 records occupying 9 record bytes | Save and reread the compressor’s choices |
| Original bytes represented by them | 8 bytes | Compare with input and identify recovered content |
| Final fixed block | 38 meaningful bits, aligned to 5 bytes | Deliver compressed data to the decoder |

Reading one record can account for six original bytes while appending one match’s encoding. Storage bounds and bit costs below must retain those unit distinctions.

Tallying also updates the literal/length and distance frequencies. A match contributes a length **code** frequency, not six literal frequencies. The selected length may also need extra bits; likewise for a distance. The end-of-block symbol has its own frequency. These statistics are the input to tree construction when the block is ready to emit.

The handoff matters: `compress_block` later reads the stored records again. The output writer must preserve each record until that read. We will return to its physical storage in [Shared storage](/sample/storage.html).

## A fixed block, field by field {#example}

For our selected symbol sequence, choose a final fixed block starting at an empty bit buffer. First derive the symbols from the two fields saved in the match record. All values in the following code tables are decimal.

| Copy length | Stored `lc = length - 3` | Literal/length symbol | Extra length bits |
| --- | --- | --- | --- |
| 3 | 0 | 257 | 0 |
| 4 | 1 | 258 | 0 |
| 5 | 2 | 259 | 0 |
| 6 | 3 | 260 | 0 |

The literal/length alphabet reserves symbols 0 through 255 for the 256 byte values and symbol 256 for end-of-block. Match-length groups therefore start at 257. The source names the byte-value count `LITERALS = 256`; `_length_code` maps a saved length offset to its group number. For length 6, `lc` is 3, `_length_code[3]` is 3, and `compress_block` adds `LITERALS + 1 = 257`, giving symbol `257 + 3 = 260`. Larger length groups need extra bits to choose a value within the group's range; this group has only one possible length.

The selected literal/length table, `ltree`, supplies a code word and bit width for each symbol; `send_code` writes that pair. This is exactly the length step in [`compress_block`, trees.c:922–923](https://github.com/madler/zlib/blob/757f0527154291bcf6bfbd6396ecde6bedd2db95/trees.c#L922-L923):

```c
code = _length_code[lc];
send_code(s, code + LITERALS + 1, ltree);
```

The first line maps saved length offset 3 to length-code group 3. The second adds that group to 257 and emits literal/length symbol 260. `send_code` takes that symbol’s word and width from `ltree`. Each step from record `02 00 03` to symbol 260 now has a concrete object to follow.

For the distance, the encoder first subtracts one from the stored distance. Distance 2 becomes 1, and `d_code(1)` is 1. The initial distance groups make the mapping visible:

| Copy distance range | Distance symbol | Base distance | Extra distance bits |
| --- | --- | --- | --- |
| 1 | 0 | 1 | 0 |
| 2 | 1 | 2 | 0 |
| 3 | 2 | 3 | 0 |
| 4 | 3 | 4 | 0 |
| 5–6 | 4 | 5 | 1 |

Now use the fixed literal/length alphabet to determine widths:

| Literal/length symbol range | Fixed width |
| --- | --- |
| 0–143 | 8 bits |
| 144–255 | 9 bits |
| 256–279 | 7 bits |
| 280–287 | 8 bits |

Symbols 286 and 287 in the last fixed range are reserved and cannot encode a valid match length. The valid distance symbols have five-bit fixed codes. ASCII A and B are 65 and 66, so both use eight bits. Symbol 260 and end-of-block symbol 256 use seven bits. Distance symbol 1 uses five bits; neither selected group needs extra bits. The complete fields are therefore:

| Field | Meaning | Width |
| --- | --- | --- |
| Header | Final block, fixed coding | 3 bits |
| Literal A | Byte 65 | 8 bits |
| Literal B | Byte 66 | 8 bits |
| Length symbol 260 | Copy length 6 | 7 bits |
| Distance symbol 1 | Distance 2 | 5 bits |
| End of block | Stop reading this block | 7 bits |

The sum is `3 + 8 + 8 + 7 + 5 + 7 = 38` meaningful bits. A final alignment adds two zero padding bits, giving five raw DEFLATE bytes. At an initially aligned position, the stored representation of the same eight original bytes would occupy thirteen bytes: the header and alignment, four length bytes, then eight data bytes. A zlib or gzip wrapper would add its own fields outside this raw block.

## Cost calculation and selection {#selection}

For positive compression levels, `_tr_flush_block` builds the literal/length and distance trees. It accumulates both the dynamic payload cost and the cost of encoding the same symbols with the fixed trees. Building a dynamic candidate does not commit the writer to using it.

The dynamic description itself has two layers. The literal/length and distance **code lengths** form a sequence. `scan_tree` identifies repeated lengths and zero runs. `build_bl_tree` constructs the smaller code-length alphabet used to encode that sequence. `send_all_trees` eventually writes the count fields, the code-length alphabet's lengths, and the encoded sequence, including the extra bits of repeat instructions. This is an optimization of the description, not a change to the data symbols.

The comparison needs both alternatives in the same unit. `s->opt_len` counts the dynamic payload and description in bits; `s->static_len` counts the fixed payload in bits. Both include the end code but exclude the three-bit block header. Their byte-rounded candidates are named `opt_lenb` and `static_lenb`:

```c
opt_lenb = (s->opt_len + 3 + 7) >> 3;
static_lenb = (s->static_len + 3 + 7) >> 3;
```

These lines are from [`_tr_flush_block`, trees.c:1027–1028](https://github.com/madler/zlib/blob/757f0527154291bcf6bfbd6396ecde6bedd2db95/trees.c#L1027-L1028). The first converts the dynamic bit cost; the second performs the same conversion for fixed coding. For our three symbols, the fixed payload and end code cost `8+8+7+5+7 = 35` bits. The second line gives `(35+3+7)>>3 = 5` bytes, matching the earlier derivation. The dynamic description must still be included in its own candidate; this example does not assert which form the real call chooses.

The three accounts for the block header; the seven implements upward rounding to bytes. The fixed candidate wins a tie, and the `Z_FIXED` strategy requests fixed coding rather than dynamic coding. For stored output, `stored_len` is the original data length in bytes. The stored branch is then eligible when `stored_len + 4` is no larger than the selected compressed candidate and the raw source pointer is nonnull. The four represents the two 16-bit length fields. The actual stored writer separately performs bit alignment and writes the header.

These are concrete source selection rules. They do not constitute a search for the globally shortest possible compressed stream: the earlier match decisions and the block boundary have already constrained the alternatives. Full paths for forced stored output and other configurations need their own treatment.

The three records now correspond to six specific fields, but we still need to join their unequal widths into bytes. [Bit writing and delivery](/sample/bits.html) continues the same fixed-block trace: B's eight bits cross the register boundary, producing the first two bytes `73 74`.

[Output agreement](/sample/proof.html) follows the records, bits, storage and delivery guarantees. [The tree and block implementation argument](/reference/docs/proof/trees.html) gives detailed statements; the complete [deflate contract](/reference/functions/deflate.html) specifies the public call.
