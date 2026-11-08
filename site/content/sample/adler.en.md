The compressed body describes how to recover bytes. A checksum asks another question: did those recovered bytes agree with the stream's integrity field? The zlib wrapper uses Adler-32. Its input is the uncompressed byte sequence, not the Huffman codes or the bytes delivered in a particular output call.

Follow the same `ABABABAB` example through two small accumulators. Then separate two useful operations: continuing a checksum over another buffer, and combining checksums computed independently. Neither requires preserving the earlier bytes in a private compression window.

## Two accumulators {#accumulators}

Let `M = 65521`. Begin with `a = 1` and `s = 0`. For each byte value `b`, compute:

```text
a := (a + b) mod M
s := (s + a) mod M
```

The second line uses the new `a`. Thus `a` accumulates byte values, while `s` accumulates successive prefix sums. After `n` bytes, the unreduced expressions are:

```text
a = 1 + b₁ + b₂ + ... + bₙ
s = n + n·b₁ + (n−1)·b₂ + ... + bₙ
```

All these equalities become congruences modulo `M` after reduction. The weights in the second sum make byte order matter: swapping A and B preserves the first sum but generally changes the second.

The returned checksum packs the reduced `a` into the low 16 bits and `s` into the high 16 bits: `a | (s << 16)`. This numeric layout is separate from a wrapper's byte order. The zlib trailer transmits the four checksum bytes most significant first.

## Eight bytes {#bytes}

ASCII A is 65; B is 66. No reduction is needed in this short example:

| Bytes processed | `a` | `s` | Packed checksum, hexadecimal |
| --- | --- | --- | --- |
| Empty | 1 | 0 | `00000001` |
| A | 66 | 66 | `00420042` |
| AB | 132 | 198 | `00c60084` |
| ABA | 197 | 395 | `018b00c5` |
| ABAB | 263 | 658 | `02920107` |
| ABABA | 328 | 986 | `03da0148` |
| ABABAB | 394 | 1380 | `0564018a` |
| ABABABA | 459 | 1839 | `072f01cb` |
| ABABABAB | 525 | 2364 | `093c020d` |

For the second byte, `a` becomes `66 + 66 = 132`; `s` becomes `66 + 132 = 198`. The second accumulator does not simply add the new byte. The final zlib checksum field for these eight bytes is therefore `09 3c 02 0d`.

<div class="zl-demo-mount"><zlib-demo kind="adler"><p>Starting from a=1 and s=0, step through the fixed byte strings AB, ABABABAB or ABC. A gives a=66,s=66; the following B gives a=132,s=198. This teaching model uses the normal initial seed; it does not model arbitrary-seed or combination API cases.</p></zlib-demo></div>

These values were checked with an independent byte recurrence and the pinned C checksum functions. That is a finite check of this example, not a universal correctness result.

## Batches and reductions {#batches}

Taking a remainder after every addition is unnecessary. zlib can keep unreduced machine sums for a bounded number of bytes, then reduce both sums at the boundary. Congruence is preserved throughout; the missing condition is that the machine additions must not overflow before reduction.

The source selects `NMAX = 5552`. Starting with reduced components and bytes at most 255, its portable worst-case second-sum bound is:

```text
s ≤ (n + 1)(M − 1) + 255·n(n + 1)/2
```

At `n = 5552`, this is `4294690200`, below `2^32 − 1`. At 5553 it becomes `4296171735`, above that limit. This explains the batch size; it is not an arbitrary tuning constant.

Each full batch executes 347 groups of 16 byte steps. The unrolled groups reduce loop overhead while retaining the dependency from each new `a` to `s`. Remaining data uses groups of 16 followed by individual bytes. Separate short and one-byte paths avoid unnecessary setup.

The selected LP64 build has wider `unsigned long` sums, but the implementation keeps the same batch size. Another optional source branch replaces division using `2^16 ≡ 15 (mod 65521)`. That identity explains the possibility of folding high bits downward; it does not make that branch part of the default execution described here.

## Buffer boundaries {#chunks}

To process another buffer, pass the previous checksum back as the seed. Finishing the first call does not reset either accumulator. Updating over A and then B gives exactly the ordinary checksum of AB when starting from the normal seed 1.

This is why application input splits need not coincide with batch boundaries. One call may finish after a single byte; the next can continue from the packed, reduced sums. The checksum state describes accepted bytes, not the number of calls used to supply them.

The checksum function itself does not allocate, retain a caller pointer, or write the input. The enclosing compressor or decoder separately decides which newly processed bytes contribute to its wrapper checksum.

## Independent chunks {#combination}

Suppose X and Y were checksummed separately, each starting at 1. Write their components as `(aX,sX)` and `(aY,sY)`, and let `n` be Y's byte length. Then, modulo `M`:

```text
aXY = aX + aY − 1
sXY = sX + sY + n·(aX − 1)
```

Subtracting one removes Y's extra initial value. The length term accounts for X's byte sum contributing to every new prefix in Y. The relevant length is Y's, not X's or their combined length.

For X=A and Y=B, the components are `(66,66)` and `(67,67)`. With `n=1`, the result is `(132,198)`, again `00c60084`. For a large Y, the implementation first reduces its nonnegative length modulo 65521; no scan of Y is needed. Adler combination uses this length-weighted arithmetic, rather than the polynomial powers used by [CRC-32](/sample/crc.html).

## Checksum entries {#entries}

[`adler32_z`](/reference/functions/adler32_z.html) takes a size-type count; [`adler32`](/reference/functions/adler32.html) takes a 32-bit count. Use several updates or the wider entry instead of truncating a large count.

[`adler32_combine`](/reference/functions/adler32_combine.html) and [`adler32_combine64`](/reference/functions/adler32_combine64.html) combine independently started checksums using Y's signed length. Negative lengths return `0xffffffff`. Genuine empty Y has checksum 1 and preserves X's checksum.

The precise NULL and arbitrary-seed cases matter: this project's Adler initialization query requires NULL with length zero. A forged seed need not follow the canonical one-byte recurrence. The [checksum proof chapter](/sample/checksum-proof.html) explains those domains and the connection from these equations to actual memory and machine arithmetic.
