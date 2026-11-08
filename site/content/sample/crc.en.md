Suppose a gzip stream should recover `AB`, but damage makes the recovered data `AC`. The gzip trailer includes a CRC-32 computed from the original uncompressed bytes. The receiver computes the same kind of 32-bit summary of its recovered bytes and compares them. A different summary detects damage; matching summaries do not rule out every possible corruption. CRC-32 supplies this integrity check. It does not compress or recover the bytes.

An update takes a previous CRC, a readable byte range and its length, and returns the CRC after that range. Start a new sequence at zero. If one call supplies A and the next supplies B, pass the first result directly into the next call. If the two buffers were checksummed independently instead, joining those summaries requires a different operation and B's length.

We will follow one byte through a small bit machine before introducing the polynomial language used to justify it. Then we can see why the C replaces repeated bit steps by tables, and long byte dependencies by interleaved word computations. Each optimization must produce the same checksum.

## Reflected register {#register}

The calculation needs a small state that summarizes all bytes processed so far. It keeps that state in a 32-bit working value, called its register `r`. Each step removes its low bit by shifting right. When the removed bit was one, it also XORs the constant `0xedb88320` into the shifted result. XOR compares bits independently: equal bits give zero, different bits give one, with no carries. The notation `>> 1` shifts right by one bit, and `r & 1` keeps only the low bit to test it. Hexadecimal constants use the prefix `0x`. Call one such step `T`:

```text
T(r) = (r >> 1) XOR (0xedb88320 if r & 1 else 0)
```

To consume the next byte, call its value `b`, XOR it into the register's low eight bits, then apply `T` eight times. The byte's least significant bit enters first. This is the reflected bit convention: the computation moves toward the low bit.

The public running checksum is the bitwise complement of this internal register: each zero bit becomes one and vice versa. A new public checksum starts at 0, so its working register starts at `ffffffff`. The function complements the incoming checksum, processes bytes, then complements the result. Callers pass the returned value directly into the next update; complementing it again would change the calculation.

The constant is chosen by CRC's polynomial rule. A register's bits can be read as coefficients that are either zero or one; polynomial addition then becomes XOR. This arithmetic is called GF(2). The CRC polynomial has degree 32, with its highest term `x^32` implicit in the stored constant. We will use that description when joining separately computed chunks; the one-byte calculation needs only the shift-and-XOR rule above.

## One byte {#one-byte}

For ASCII A, `b = 0x41`. Starting from public checksum zero gives internal register `ffffffff`. XOR the byte to obtain `ffffffbe`, then perform the eight bit steps:

| Bit steps completed | Internal register, hexadecimal |
| --- | --- |
| Before stepping | `ffffffbe` |
| 1 | `7fffffdf` |
| 2 | `d2477ccf` |
| 3 | `849b3d47` |
| 4 | `aff51d83` |
| 5 | `ba420de1` |
| 6 | `b09985d0` |
| 7 | `584cc2e8` |
| 8 | `2c266174` |

The first step only shifts because the outgoing bit is zero. The next step shifts `7fffffdf` to `3fffffef`, then XORs `edb88320`, giving `d2477ccf`. Complementing the eighth result gives public CRC `d3d99e8b`.

<div class="zl-demo-mount"><zlib-demo kind="crc"><p>Start with public checksum zero and internal register ffffffff. Step through AB, ABABABAB or ABC one bit at a time, checking the outgoing low bit before each shift and conditional polynomial XOR. This fixed-seed teaching model does not implement arbitrary-seed or combination contracts.</p></zlib-demo></div>

Now let the first buffer end after A. Its returned checksum `d3d99e8b` can be stored as the whole continuation state. Passing it into an update over B gives `30694c07`, the CRC of AB. Processing B independently from zero gives `4ad0cf31`; that number alone has no A contribution. The independent recurrence and pinned C functions agree on these examples. This checks the displayed numbers, not all inputs.

## Byte tables {#tables}

Eight shifts and conditional XORs for every byte are repetitive. The contribution from the low byte has only 256 possibilities, so compute each once and store it in an array called `table`. In the notation below, `i` is one of those byte values, `T⁸` means eight applications of the bit step, and `byte_step` is the working register after consuming one byte:

```text
table[i] = T⁸(i)
byte_step(r,b) = (r >> 8) XOR table[(r XOR b) & 255]
```

The upper 24 register bits shift down, while the table supplies the lower byte's polynomial contribution. This separation works because the steps preserve XOR: applying them to two values XORed together gives the XOR of their separate results. For A, the index is `be`; `table[be] = 2cd99e8b`. XOR with `00ffffff` again gives `2c266174`.

In the C, `buf` points to the next input byte, `len` is the remaining byte count, `crc_table` is this 256-entry table, and local `crc` holds the internal register. The latter differs from the public checksum while the calculation is in progress. Here is the byte tail that actually uses the table, from [pinned `crc32.c`, lines 934–940](https://github.com/madler/zlib/blob/757f0527154291bcf6bfbd6396ecde6bedd2db95/crc32.c#L934-L940):

```c
    while (len) {
        len--;
        crc = (crc >> 8) ^ crc_table[(crc ^ *buf++) & 0xff];
    }

    /* Return the CRC, post-conditioned. */
    return crc ^ 0xffffffff;
```

`len` is the remaining byte count. The guard ensures a byte remains before the decrement and read. `*buf++` reads that byte and advances the pointer; XOR and `& 0xff` form the table index, always from 0 to 255. `crc >> 8` moves the old register's upper bits down, and `^` combines them with the table contribution. The return flips the low 32 bits back to the public convention. Earlier, [line 635](https://github.com/madler/zlib/blob/757f0527154291bcf6bfbd6396ecde6bedd2db95/crc32.c#L626-L635) performed `crc = (~crc) & 0xffffffff`, so this local `crc` is the working register, not the public value during the loop.

[`get_crc_table`](/reference/functions/get_crc_table.html) exposes this byte table. Its entries describe internal register updates, without the public complements. The returned storage is static and read-only; the pointer does not authorize reading neighboring braid tables, writing entries, or freeing the array.

## Words and braids {#braids}

Table lookup removes the eight-bit inner loop, but every next byte still needs the previous register. To expose independent work, the selected default branch groups input into eight-byte units, called words, and reads each as a 64-bit value. It keeps five interleaved running values, called braided lanes: each lane has its own register and handles every fifth word. Number the words from zero after the initial alignment bytes: lane zero handles positions 0,5,10,…; lane one handles 1,6,11,…, and so on.

Those are spaced subsequences. Their tables account for the polynomial distance between successive words. Lane zero receives the preprocessed incoming register `(~crc) & 0xffffffff`; the other lanes start at zero. They are not five ordinary checksums of contiguous chunks. The last-block code merges their contributions in the original byte order using word recurrences.

This branch cannot start safely just because one word remains. In the C, `N` counts lanes and `W` counts bytes per word. Its [entry and alignment loop, lines 640–650](https://github.com/madler/zlib/blob/757f0527154291bcf6bfbd6396ecde6bedd2db95/crc32.c#L640-L650), first require `len >= N * W + W - 1`, then consume individual bytes until `((z_size_t)buf & (W - 1)) == 0`. For `N=5,W=8`, the threshold is `5×8 + 8−1 = 47` bytes. Alignment means the input address is a multiple of eight; the mask `W - 1` tests its low three address bits. At most seven bytes reach such an address, leaving at least one 40-byte block.

One block contains one word for each lane, so it has `N × W = 40` bytes. The C counter `blks` counts complete blocks left, including a final block reserved for merging. The [block loop at line 710](https://github.com/madler/zlib/blob/757f0527154291bcf6bfbd6396ecde6bedd2db95/crc32.c#L706-L728) uses `while (--blks)`: it processes all but the last block. Separate code handles that last block and its merge. Reserving at least one block prevents the initial decrement from underflowing. Fewer than 40 bytes remain afterward, handled by an unrolled byte tail and then individual bytes.

To see the independent dependencies in the C, follow lane zero through the little-endian branch. Here `words` is a pointer into the input measured in eight-byte words. `crc0` is lane zero’s running register; `word0` temporarily holds its XOR with the next input word. The table `crc_braid_table` has a row for each byte position within a word, and `k` selects that position. These excerpts select its statements from [line 712](https://github.com/madler/zlib/blob/757f0527154291bcf6bfbd6396ecde6bedd2db95/crc32.c#L710-L720), [lines 728–732](https://github.com/madler/zlib/blob/757f0527154291bcf6bfbd6396ecde6bedd2db95/crc32.c#L728-L732) and [lines 748–765](https://github.com/madler/zlib/blob/757f0527154291bcf6bfbd6396ecde6bedd2db95/crc32.c#L748-L765). Intervening statements for the other lanes and their preprocessor guards are omitted; this is not the complete loop:

```c
                word0 = crc0 ^ words[0];

                words += N;

                crc0 = crc_braid_table[0][word0 & 0xff];

                for (k = 1; k < W; k++) {
                    crc0 ^= crc_braid_table[k][(word0 >> (k << 3)) & 0xff];
                }
```

`words[0]` loads the next word assigned to lane zero; `word0` mixes that word with the lane's old `crc0`. The neighboring source lines do the same for `words[1]` through `words[4]` and `crc1` through `crc4`. All five words are loaded before `words += N` advances the common pointer to the next block. Each lane update depends on its own old value and input word, so it can proceed without waiting for another lane's newly computed CRC.

For a concrete address path, call the first aligned byte's offset `q`. With the selected `N=5,W=8`, lane zero first reads bytes `q…q+7`, lane one reads `q+8…q+15`, and lane four reads `q+32…q+39`. Advancing `words` by five words moves it 40 bytes. If another regular iteration remains, lane zero then reads `q+40…q+47`, and lane one reads `q+48…q+55`. Successive words in the same lane are therefore 40 bytes apart; they are not adjacent eight-byte chunks.

The first table lookup handles byte position zero of `word0`. The `k` loop extracts positions 1 through 7 by right-shifting 8 through 56 bits, looks each up, and XORs their contributions into `crc0`. On this little-endian path, the low byte corresponds to the earliest byte of the loaded word. The table row `k` means a byte position within a word, not a lane number; all lanes use the same rows. These braid tables include the spacing between same-lane words, unlike the ordinary one-byte table. The [last-block merge, lines 772–780](https://github.com/madler/zlib/blob/757f0527154291bcf6bfbd6396ecde6bedd2db95/crc32.c#L772-L780), then combines lanes zero through four in order with `crc_word`, restoring a single register before the byte tail.

This organization exposes independent lane dependencies while amortizing loop work. Word endianness and address alignment remain part of selecting and interpreting the actual loads. The selected proof model assembles the same bytes in target order; the C cast and ABI correspondence require their own review.

## Polynomial operators {#operators}

What if two workers computed A and B independently and discarded their bytes? We cannot update the first CRC using the second CRC as if it were B's data. We need to move A's contribution past the byte position occupied by B, then combine the two contributions with XOR.

For general byte sequences X followed by Y, call Y's length `n`. `CRC(X)` and `CRC(Y)` mean independently computed public checksums, each started at zero; `X ++ Y` means concatenation. Let `T⁸ⁿ` mean applying the earlier bit step `8n` times, advancing a 32-bit value through `n` zero bytes without the public complements. Then:

```text
CRC(X ++ Y) = T⁸ⁿ(CRC(X)) XOR CRC(Y)
```

The initial and final complement terms cancel in this concatenation identity. Do not implement `T⁸ⁿ` by calling the public update on `n` zero bytes: that call includes its own complement convention.

For X=A and Y=B, `T⁸(d3d99e8b) = 7ab98336`. XOR with B's independent `4ad0cf31` gives `30694c07`, the CRC of AB.

The advance preserves XOR, so it can be represented by a binary matrix or by multiplication modulo the CRC polynomial. The selected source uses polynomial multiplication. Its [generator, lines 954–960](https://github.com/madler/zlib/blob/757f0527154291bcf6bfbd6396ecde6bedd2db95/crc32.c#L954-L960), calls `x2nmodp(len2, 3)`: `len2` is Y’s length in bytes, and the helper computes a power representing that many bytes of advancement. Its second argument selects a power of two per length unit; 3 selects eight bit steps per byte, since `2^3 = 8`. [That helper, lines 184–194](https://github.com/madler/zlib/blob/757f0527154291bcf6bfbd6396ecde6bedd2db95/crc32.c#L184-L194), examines one length bit at a time. The powers in `x2n_table` come from repeated squaring. For each set length bit the helper multiplies by the corresponding power, then shifts the length right and moves to the next power. This computes an operator for `x^(8n)` without traversing `n` bytes. In this reflected multiplication representation, the identity is `0x80000000`.

## Checksum entries {#entries}

[`crc32_z`](/reference/functions/crc32_z.html) uses a `z_size_t` byte count, 64 bits in the selected build; [`crc32`](/reference/functions/crc32.html) uses a 32-bit count. [`crc32_combine`](/reference/functions/crc32_combine.html) and [`crc32_combine64`](/reference/functions/crc32_combine64.html) take independent checksums and Y's signed length.

When many second chunks share a length, generate its operator once with [`crc32_combine_gen`](/reference/functions/crc32_combine_gen.html) or [`crc32_combine_gen64`](/reference/functions/crc32_combine_gen64.html), then reuse it through [`crc32_combine_op`](/reference/functions/crc32_combine_op.html). A generated operator is a domain requirement, not merely any nonzero integer.

Negative lengths generate zero and make the combine call return zero. A genuine empty Y has CRC zero and preserves X's checksum. Arbitrary scalar inputs at length zero instead produce the XOR of their low 32 bits. NULL update queries return zero even with nonzero lengths. The [proof chapter](/sample/checksum-proof.html) separates these exact API cases from checksum concatenation and explains the memory-view assumptions.
