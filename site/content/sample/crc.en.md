The gzip wrapper uses CRC-32 for its uncompressed data. Like Adler-32, it can continue across buffers or combine independent chunks. Its arithmetic is different: bits are polynomial coefficients over GF(2), so addition is XOR and has no carries.

Begin with the byte-at-a-time meaning. Tables, word reads and braided lanes are ways to compute that same result with different dependencies. They do not define a different checksum for aligned buffers or long inputs.

## Reflected register {#register}

The underlying polynomial has degree 32; the leading `x^32` term is implicit in the representation. zlib's reflected bit convention uses the constant `0xedb88320`: register movement is toward the low bit, so a bit step shifts right. If the bit shifted out was one, XOR the polynomial constant into the shifted register:

```text
T(r) = (r >> 1) XOR (0xedb88320 if r & 1 else 0)
```

The register is a 32-bit value. To consume byte `b`, XOR it into the register's low eight bits, then apply `T` eight times. The byte's least significant bit enters first.

The public running checksum is complemented relative to that internal register. A new checksum starts at 0. The function complements the incoming checksum, processes bytes, then complements the result. Callers pass the returned value directly into the next update; complementing it again would change the calculation.

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

Continuing with B gives `30694c07`. Processing B independently from zero gives `4ad0cf31`; those are different tasks. The independent recurrence and pinned C functions agree on these examples. This checks the displayed numbers, not all inputs.

## Byte tables {#tables}

Eight bit steps are a fixed linear operation. Precompute their result for every possible low byte:

```text
table[i] = T⁸(i)
byte_step(r,b) = (r >> 8) XOR table[(r XOR b) & 255]
```

There are 256 possible indices. The upper 24 register bits shift down, while the table supplies the lower byte's polynomial contribution. For A, the index is `be`; `table[be] = 2cd99e8b`. XOR with `00ffffff` again gives `2c266174`.

[`get_crc_table`](/reference/functions/get_crc_table.html) exposes this byte table. Its entries describe internal register updates, without the public complements. The returned storage is static and read-only; the pointer does not authorize reading neighboring braid tables, writing entries, or freeing the array.

## Words and braids {#braids}

The byte recurrence still has one long dependency chain: every next byte needs the previous register. The default selected branch uses eight-byte words and five braided lanes. Conceptually, lane zero handles word positions 0,5,10,…; lane one handles 1,6,11,…, and so on.

Those are spaced subsequences. Their tables account for the polynomial distance between successive words. Lane zero receives the preprocessed incoming register `(~crc) & 0xffffffff`; the other lanes start at zero. They are not five ordinary checksums of contiguous chunks. The last-block code merges their contributions in the original byte order using word recurrences.

The threshold is `5×8 + 8−1 = 47` bytes. At most seven bytes establish alignment, leaving at least one 40-byte block. The loop processes all but the last block; separate code handles that last block and its merge. Fewer than 40 bytes remain afterward, handled by an unrolled byte tail and then individual bytes.

This organization exposes independent lane dependencies while amortizing loop work. Word endianness and address alignment remain part of selecting and interpreting the actual loads. The selected proof model assembles the same bytes in target order; the C cast and ABI correspondence require their own review.

## Polynomial operators {#operators}

Let `T⁸ⁿ` advance a register by `n` zero bytes without the public complements. For independently computed checksums of X and Y, with `n = length(Y)`:

```text
CRC(X ++ Y) = T⁸ⁿ(CRC(X)) XOR CRC(Y)
```

The initial and final complement terms cancel in this concatenation identity. Do not implement `T⁸ⁿ` by calling the public update on `n` zero bytes: that call includes its own complement convention.

For X=A and Y=B, `T⁸(d3d99e8b) = 7ab98336`. XOR with B's independent `4ad0cf31` gives `30694c07`, the CRC of AB.

The advance is a linear map on 32 bits. It can be represented by a binary matrix or by multiplication modulo the CRC polynomial. The selected source uses polynomial multiplication and precomputed powers in `x2n_table`, processing the bits of the length by repeated squaring. It computes an operator for `x^(8n)` without iterating through `n` bytes. In this reflected multiplication representation, the identity is `0x80000000`.

## Checksum entries {#entries}

[`crc32_z`](/reference/functions/crc32_z.html) uses a size-type length; [`crc32`](/reference/functions/crc32.html) uses a 32-bit count. [`crc32_combine`](/reference/functions/crc32_combine.html) and [`crc32_combine64`](/reference/functions/crc32_combine64.html) take independent checksums and Y's signed length.

When many second chunks share a length, generate its operator once with [`crc32_combine_gen`](/reference/functions/crc32_combine_gen.html) or [`crc32_combine_gen64`](/reference/functions/crc32_combine_gen64.html), then reuse it through [`crc32_combine_op`](/reference/functions/crc32_combine_op.html). A generated operator is a domain requirement, not merely any nonzero integer.

Negative lengths generate zero and make the combine call return zero. A genuine empty Y has CRC zero and preserves X's checksum. Arbitrary scalar inputs at length zero instead produce the XOR of their low 32 bits. NULL update queries return zero even with nonzero lengths. The [proof chapter](/sample/checksum-proof.html) separates these exact API cases from checksum concatenation and explains the memory-view assumptions.
