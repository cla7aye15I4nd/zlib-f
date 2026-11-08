Suppose a stream is meant to recover `AB`, but a damaged byte makes it recover `AC`. Both are ordinary byte strings. Decoding them is not enough to tell which one the sender intended. The zlib wrapper therefore carries an Adler-32 checksum: the sender computes a 32-bit summary of the original bytes; the receiver recomputes it from the recovered bytes and compares the two values. A mismatch detects damage. Agreement is an integrity check, not a guarantee that no other byte string could have the same checksum.

An update takes a previous checksum, a readable byte range and its length, and returns the checksum after that range. For a new sequence the previous checksum is 1. The input is uncompressed data, not Huffman codes. If a decoder delivers A in one call and B in the next, the second update must continue the first: the trailer describes all of AB.

We will first see what information the checksum keeps, then follow `ABABABAB` through it. The C implementation delays some arithmetic to save work. Finally, we will distinguish continuing over a new buffer from combining two independently computed checksums. Neither operation needs to retain the earlier bytes.

## Two accumulators {#accumulators}

One running total records the sum of the byte values. A second records the sum of all the running totals, so an early byte affects more terms than a late byte. Call these totals `a` and `s`. To keep each small enough for half of the result, reduce it modulo `M = 65521`; “modulo” means keeping the remainder after division by `M`. Begin with `a = 1` and `s = 0`. For the next byte value `b`, compute:

```text
a := (a + b) mod M
s := (s + a) mod M
```

The second line uses the new `a`: the first A makes both totals 66, then B makes them 132 and 198. If that B becomes C, the totals instead become 133 and 199, so the checksum changes. If A and B trade places, the byte sum remains the same but the prefix sum changes. To express this for any input, call its length `n` and its byte values `b₁` through `bₙ`. Before taking remainders:

```text
a = 1 + b₁ + b₂ + ... + bₙ
s = n + n·b₁ + (n−1)·b₂ + ... + bₙ
```

After taking remainders, the two sides have the same remainder modulo `M`. The weights in the second expression explain why byte order matters: the first byte contributes to all `n` prefixes, while the last contributes to only one.

The returned checksum packs the reduced `a` into the low 16 bits and `s` into the high 16 bits: `a | (s << 16)`. The shift `<< 16` moves `s` into the upper half; bitwise OR, `|`, joins the two disjoint halves. This numeric layout is separate from a wrapper's byte order. The zlib trailer transmits the four checksum bytes most significant first.

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

The table above follows the mathematical rule byte by byte. On a long buffer, taking a remainder after every addition would repeat expensive work. Adding first and taking the remainder later gives the same remainder, provided the machine sum does not overflow in between. zlib therefore groups a bounded number of byte steps into a batch.

The C needs to track both the checksum and its place in the buffer. Its two running sums are `adler` for `a` and `sum2` for `s`; `buf` points to the next bytes and `len` counts how many bytes remain. The modulus `M` is named `BASE` in the source. A batch may process at most `NMAX = 5552` bytes before reducing the sums; we will derive that limit below. Within a batch, the C counter `n` counts groups of 16 bytes, not individual bytes. The macro argument `i` is a byte offset from `buf`; the sixteen-step expansion uses offsets 0 through 15.

Here is the single-byte macro and the body of a full-batch loop, from the [pinned `adler32.c`, lines 14–18](https://github.com/madler/zlib/blob/757f0527154291bcf6bfbd6396ecde6bedd2db95/adler32.c#L14-L18) and [97–106](https://github.com/madler/zlib/blob/757f0527154291bcf6bfbd6396ecde6bedd2db95/adler32.c#L97-L106). The two excerpts are separated by the blank line:

```c
#define DO1(buf,i)  {adler += (buf)[i]; sum2 += adler;}

    while (len >= NMAX) {
        len -= NMAX;
        n = NMAX / 16;
        do {
            DO16(buf);
            buf += 16;
        } while (--n);
        MOD(adler);
        MOD(sum2);
    }
```

`DO1` reads one byte, adds it to the first sum, then adds the updated first sum to the second. `DO16` expands this operation sixteen times in order. The `while` guard reserves a complete batch before `len` is decreased. `n` counts its sixteen-byte groups; after each group `buf` advances by 16. `--n` ends the inner loop after the reserved groups. The two `MOD` lines then reduce the sums; in the selected default branch each means `% BASE`. The proof must connect these pointer advances and delayed remainders to the bytewise rule, not replace the C by that simpler rule.

Why choose 5552 bytes for `NMAX`? Call the number of bytes since the last reduction `m`, to distinguish it from the C group counter `n`. Starting with reduced components, each at most `M−1`, and bytes at most 255, the second sum is bounded by:

```text
s ≤ (m + 1)(M − 1) + 255·m(m + 1)/2
```

The first term covers the initial second sum and `m` copies of the initial first sum. The last term covers the worst-case byte contributions with weights `m,m−1,…,1`. At `m = 5552`, this is `4294690200`, below `2^32 − 1`. At 5553 it becomes `4296171735`, above that limit. This is why the source selects `NMAX = 5552`.

Each full batch executes 347 groups of 16 byte steps. The unrolled groups reduce loop overhead while retaining the dependency from each new `a` to `s`. Remaining data uses groups of 16 followed by individual bytes. Separate short and one-byte paths avoid unnecessary setup.

In the selected LP64 build, pointers and `unsigned long` are 64 bits wide. Its sums therefore have more room than the 32-bit bound above, but the implementation keeps the same batch size. Another optional source branch replaces division using `2^16 ≡ 15 (mod 65521)`. That identity explains the possibility of folding high bits downward; it does not make that branch part of the default execution described here.

## Buffer boundaries {#chunks}

Return to the decoder that delivers A, then B. The first update starts at 1 and returns `00420042`. Pass that returned number as the next seed; the function unpacks it into `a=66,s=66`. Reading B then returns `00c60084`, exactly the ordinary checksum of AB. Starting the second call at 1 would instead compute B alone, `00430043`, and lose A's contribution.

This is why application input splits need not coincide with batch boundaries. One call may finish after a single byte; the next can continue from the packed, reduced sums. The checksum state describes accepted bytes, not the number of calls used to supply them.

The checksum function itself does not allocate, retain a caller pointer, or write the input. The enclosing compressor or decoder separately decides which newly processed bytes contribute to its wrapper checksum.

## Independent chunks {#combination}

Suppose two workers already computed A and B separately, each from 1, and kept only their checksums. They might be two threads or two programs handling separate file chunks. Passing B's checksum as an update seed cannot join them: an update consumes bytes, not a second checksum. Combination instead recovers the checksum of the concatenation using the two summaries and the second chunk's length, without rereading either chunk.

For general chunks X followed by Y, write the separately computed components as `(aX,sX)` and `(aY,sY)`. Let `n` be Y's byte length, and `(aXY,sXY)` the components we want for X followed by Y. Then, modulo `M`:

```text
aXY = aX + aY − 1
sXY = sX + sY + n·(aX − 1)
```

Subtracting one removes Y's extra initial value. The length term accounts for X's byte sum contributing to every new prefix in Y. The relevant length is Y's, not X's or their combined length.

For X=A and Y=B, the components are `(66,66)` and `(67,67)`. With `n=1`, the result is `(132,198)`, again `00c60084`. For a large Y, the implementation first reduces its nonnegative length modulo 65521; no scan of Y is needed. Adler combination uses this length-weighted arithmetic, rather than the polynomial powers used by [CRC-32](/sample/crc.html).

## Checksum entries {#entries}

[`adler32_z`](/reference/functions/adler32_z.html) takes a `z_size_t` byte count, 64 bits in the selected build; [`adler32`](/reference/functions/adler32.html) takes a 32-bit count. Use several updates or the wider entry instead of truncating a large count.

[`adler32_combine`](/reference/functions/adler32_combine.html) and [`adler32_combine64`](/reference/functions/adler32_combine64.html) combine independently started checksums using Y's signed length. Negative lengths return `0xffffffff`. Genuine empty Y has checksum 1 and preserves X's checksum.

Here a seed is the checksum value supplied before an update. A genuine continuation seed is a previous result; an arbitrary seed is any caller-supplied integer, which may not describe a real prefix. NULL means that no input pointer is supplied. The precise NULL and arbitrary-seed cases matter: this project's Adler initialization query requires NULL with length zero. A forged seed need not follow the canonical one-byte recurrence. The [checksum proof chapter](/sample/checksum-proof.html) explains those domains and the connection from these equations to actual memory and machine arithmetic.
