[The topic entry](/verification/checksums.html) places checksums between body decoding and trailer comparison. [Adler-32](/sample/adler.html) and [CRC-32](/sample/crc.html) develop the two algorithms. The connection to establish now is: **does the computed number describe exactly the original data processed by this compression or decoding call?**

A five-byte output buffer receives `ABABA`, then `BAB`. The checksum must continue across the calls and finally describe `ABABABAB`. Counting the first part twice, skipping the last byte, or restarting from the initial value would break the trailer comparison even if every addition and lookup were correct. The proof therefore tracks the byte slice, running checksum, and read pointer together, then hands that relation to [wrapper completion](/sample/wrappers.html#proof-boundary).

For manageable arithmetic below, shorten the data to A and B. The algorithm, machine arithmetic, memory reads, and chunk combination are different steps in that same connection.

Suppose the application supplies A in one buffer and B in the next. The [Adler-32](/sample/adler.html) recurrence says the final checksum is `00c60084`; [CRC-32](/sample/crc.html) says `30694c07`. That calculation alone does not establish that zlib reads each requested byte exactly once, carries the first result into the second call, or returns without an invalid access. The C also uses different code for short inputs, delayed reductions, tables and aligned words. A proof must connect every selected path to the same byte meaning.

The proof must describe both the bytes and where the program reads them. The caller heap records the existing memory objects and their contents. A pointer selects the first byte, and a length counts the requested bytes. The seed is the checksum supplied before this update, normally the previous call's result. These inputs must satisfy the entry's explicit domain. Its conclusion includes the exact return value and the unchanged heap. To see what that buys the application, keep three questions separate:

| Question | What must be established? |
| --- | --- |
| Does the call run safely and finish? | Every read, arithmetic operation and loop is admitted; execution returns without a model fault. |
| What number does it return? | The exact numeric behavior of that C entry, including arbitrary seed words and query/error cases. |
| Is that number the checksum of the intended data? | The seed describes the actual prefix, this call covers exactly the next bytes, and combination uses the actual second length. |

A numerically correct call over the wrong buffer still checksums the wrong bytes. Conversely, a readable buffer with a forged seed can be safe while its numeric result does not mean “the checksum of this whole stream.” The proof is organized to expose both distinctions.

## Independent recurrences {#model}

First choose a definition of the answer that does not borrow the implementation's optimizations. The independent [format definitions](/reference/source/ZlibF/Spec/Format/Checksum.html) define Adler through bytewise modular updates and CRC through bytewise XOR and eight reflected bit steps. Neither definition invokes the translated checksum function or its tables. A table generated incorrectly by C therefore cannot make the intended answer change to match it.

To “fold” a byte sequence means to start with the seed and apply its update step to each byte in order. Call the first sequence X and the second Y. Folding over X and then Y equals folding over `X ++ Y`, their concatenation. This establishes model-level incremental meaning. It does not show that the pointer loop visits that list or its unrolled arithmetic computes the same step.

Execution supplies those facts on the actual heap. Let `off` be the initial array offset and `k` the number of bytes already read. The loop invariant connects three things: the pointer is at `off+k`, the next read is still permitted when bytes remain, and the register represents the first `k` requested bytes. Initialization establishes this at zero reads. One step preserves it; loop exit yields the full requested sequence.

For example, the short Adler branch maintains two sums: `adler` adds byte values, and `sum2` adds each updated first sum. `buf` points to the next byte and `len` counts bytes left. `BASE` is Adler’s modulus, 65521; `MOD28` is a reduction macro, implemented as remainder by `BASE` in the selected default build. The branch actually contains these lines, from [pinned `adler32.c`, lines 85–94](https://github.com/madler/zlib/blob/757f0527154291bcf6bfbd6396ecde6bedd2db95/adler32.c#L85-L94):

```c
    if (len < 16) {
        while (len--) {
            adler += *buf++;
            sum2 += adler;
        }
        if (adler >= BASE)
            adler -= BASE;
        MOD28(sum2);            /* only added so many BASE's */
        return adler | (sum2 << 16);
    }
```

`len < 16` selects this path; it does not itself establish that `buf` is readable. `while (len--)` tests the old count, so the body runs only while a byte remains. `*buf++` reads the current byte before advancing. The next line uses the updated first sum. When the old count is zero, the unsigned post-decrement wraps but the loop body does not run; treating that wrap as a negative count would describe different C. The proof relates the actual loop to the natural-number count of completed reads, then justifies the remaining lines: one conditional subtraction reduces `adler`, `MOD28` reduces `sum2`, and the return packs them into the low and high halves. On one two-byte AB buffer, the two iterations produce the familiar `(132,198)` components. Two separate one-byte calls instead take the earlier fast path; the execution proof must cover both routes.

## Machine arithmetic {#arithmetic}

The loop invariant must describe the arithmetic the machine really performs. Adler's mathematical modulus is 65521. Machine unsigned overflow uses a power-of-two modulus. These are not interchangeable: `2^32 mod 65521 = 225`, so an unnoticed 32-bit wrap before reduction can change the desired answer. “Unsigned wrap is defined C” would establish only that this operation is allowed, not that the answer matches Adler's recurrence.

In the selected LP64 build, pointers and `unsigned long` are 64 bits wide. Adler’s additions therefore use 64-bit `unsigned long`. Let `a` and `s` be the unreduced first and second sums, and `j` the number of bytes read in a batch. For up to 5552 steps starting from masked 16-bit seed halves, a convenient bound is:

```text
a ≤ 65535 + 255j
s ≤ 65535 + j(65535 + 255×5552)
```

For `j≤5552`, these give `a≤1481295` and `s≤8224215375`, below `2^64`. Thus the additions agree with natural-number arithmetic. Congruence then justifies postponing reduction. The [Adler chapter’s batch limit](/sample/adler.html#batches), `NMAX = 5552` bytes between reductions, was derived using 32-bit sums and already reduced components; the wider bound also accommodates the masked arbitrary seeds used by the numeric execution argument.

CRC uses a different arithmetic: each bit is a coefficient that is zero or one, and addition is XOR with no carries. This is arithmetic over GF(2). Lean’s `UInt32` represents a 32-bit unsigned value; XOR and logical right shifts on it implement the CRC register steps directly. Its table proof must show that each entry equals the corresponding eight polynomial bit steps; merely showing that 256 entries exist establishes no numeric meaning. Word recurrences also track widened temporaries, byte order and the final 32-bit projection. Thus Adler's main arithmetic bridge is bounded unreduced sums, while CRC's is equality between different representations of the same bit transition.

## Memory views {#memory}

Now connect the sequence to memory. `offset` is the first byte's position, `length` is the requested count, and `array.size` is the containing byte object's size. Readability requires `offset+length≤array.size`; dereferences occur before the endpoint. For example, offset 3 and length 2 in a five-byte object permit reading positions 3 and 4; position 5 is the endpoint and is never read. An empty range can use the object's one-past pointer, the position immediately after its last byte. Both updates retain the whole heap and ownership: they read their input, allocate nothing and retain no caller pointer.

CRC’s eight-byte loads need an address divisible by eight. That depends on the address where an object begins as well as the index within it. The model gives allocated byte blocks an aligned origin; static and embedded arrays may begin at any fixed address remainder modulo eight. These remainders are the origin residues. The [general byte-view theorem](/reference/source/ZlibF/Proof/crc32.c.views.html#L567) covers those represented views and residues. It does not prove a general machine ABI or every effective-type alias.

The [CRC chapter’s word path](/sample/crc.html#braids) assigns one eight-byte word to each of five interleaved lanes, making a block of 40 bytes. Its entry threshold is 47 bytes: at most seven byte steps reach an aligned address, leaving at least one whole block. That matters before the pre-decrement block loop. Row indices stay below 8, byte indices below 256, and extraction shifts at most 56 bits in a 64-bit word. These facts justify accesses; polynomial invariants justify their contents and merges.

The [platform premise](/reference/docs/spec/platform.html) bounds each represented byte object below `2^63` bytes, not total stream length. It must not be silently inserted into checksum statements with wider domains. General C alignment, casting and aliasing correspondence remain in the [trusted base](/reference/docs/trusted-base.html).

## Combined lengths {#composition}

Continuing an update needs bytes, but combination needs two checksums and the second chunk's length. If A and B were computed independently, Adler combination must produce `00c60084` and CRC combination `30694c07` without reading either buffer. Proving this requires both the exact scalar computation and a theorem connecting its inputs to real sequences. A wrong second length still produces a number, with no concatenation guarantee.

Adler combination expands the two independently started component sums, removes the duplicated initial one, and counts the first chunk's contribution to new prefixes. The implementation's nonnegative-length reduction must preserve that length contribution; negative lengths follow the separate rejection branch.

For CRC combination, first move the first chunk’s contribution past the second chunk. Let `n` be the second chunk’s length in bytes, and `T` one register step on a zero input bit. Then `T^(8n)` means `8n` such steps, because each byte occupies eight bits. This advance can be represented by a binary matrix or by multiplication modulo the CRC polynomial.

The selected source uses polynomial multiplication: `multmodp` multiplies two values whose low 32 bits encode polynomial remainders. A generated operator is the value encoding the required `n`-byte advance. The powers stored in `x2n_table` let the implementation build that operator from the set bits of `n`, instead of performing `8n` separate steps. The proof connects those precomputed powers and each actual multiplication to the independent bit recurrence.

Termination has a real domain condition. In [pinned `crc32.c`, lines 166–175](https://github.com/madler/zlib/blob/757f0527154291bcf6bfbd6396ecde6bedd2db95/crc32.c#L166-L175), `multmodp` begins its scan at bit 31. It can break only after finding a set bit with no lower set bits left. If the low 32 bits of that operand were all zero, shifting its scan mask down would never reach that break. Any nonzero 64-bit integer is therefore not enough.

The operator-generation theorem establishes the required low-bit fact before multiplication. The [`crc32_combine_op` contract](/reference/functions/crc32_combine_op.html) therefore uses generated operators, including the zero rejection result. In the C, [lines 969–972](https://github.com/madler/zlib/blob/757f0527154291bcf6bfbd6396ecde6bedd2db95/crc32.c#L969-L972) return zero before calling `multmodp` when the generated operator is zero. For a valid positive operator the proof uses the proved multiplication result, not an assumed callee contract.

## Queries and seed domains {#domains}

A seed is the numeric checksum passed into an update. Short examples normally use the initial seeds 1 for Adler or 0 for CRC. A public numeric theorem must also account for callers who supply other seed words, empty ranges and query arguments. These cases must be read from the actual branch order.

Adler's [one-byte fast path, lines 70–82](https://github.com/madler/zlib/blob/757f0527154291bcf6bfbd6396ecde6bedd2db95/adler32.c#L70-L82), precedes its NULL check: at length one it reads `buf[0]` before reaching the query branch. The project's explicit initialization-query domain is NULL with zero length; this restriction appears in the [deviations](/reference/docs/deviations.html). CRC checks NULL first and returns zero for any supplied length. A non-NULL empty CRC update preserves the incoming low 32 bits.

Adler also distinguishes normal checksums from forged seed words. For `adler32_z(0xfffffff0,"\0",1)`, the masked components are 65520 and 65535. The low half, 65520, is the first sum; the high half, 65535, is the second. Adding the zero byte leaves the first sum unchanged, then adding that first sum makes the second sum 131055; one conditional subtraction leaves 65534, producing `0xfffefff0`. Fully reducing the starting components would instead leave high component 13. The call is memory-safe; the naive arbitrary-seed functional statement is wrong.

The numeric specification [`adlerValue`](/reference/source/ZlibF/Spec/Public/Checksums.html#L41) retains that one-byte behavior and canonicalizes other lengths. Genuine incremental seeds agree with the ordinary recurrence. Entry widths, non-NULL empty ranges, negative combine lengths and generated operators need distinct cases.

## Exact results {#evidence}

The proofs below cover updates, independent chunk combination, and static lookup data. Follow each link to its definitions and derivation; [Progress](/reference/docs/progress.html#group-checksums) records the current state.

[`adler_z_public` and `adler_public`](/reference/source/ZlibF/Proof/public-adler-update.html#L36) cover all represented readable ranges and all seeds, the explicit zero-length NULL query, exact numeric result and unchanged heap. The [Adler combine results](/reference/source/ZlibF/Proof/public-adler-combine.html#L118) give total execution for scalar arguments, negative-length rejection, and concatenation when the checksums and second length describe actual sequences.

The [CRC update results](/reference/source/ZlibF/Proof/public-crc-updates.html#L18) retain fixed-global premises and the full represented byte-view domain. The [CRC combination results](/reference/source/ZlibF/Proof/public-crc-combine.html#L76) cover generators, generated-operator application and both combine widths with exact polynomial results and immutable heaps. [`get_crc_table`](/reference/functions/get_crc_table.html) separately specifies the static pointer and all 256 entries.

These scopes do not establish the complete compressor or decoder: those callers must checksum exactly their accepted or produced bytes and validate the appropriate wrapper field. The full-domain C-correspondence proof is unfinished: address, alignment, cast, and alias boundaries recorded in the reference still require their correspondence arguments. [Progress](/reference/docs/progress.html#group-checksums) owns current registration and acceptance evidence; the [component arguments](/reference/docs/proof/README.html) provide the detailed derivations.

## Pass the local guarantee to the wrapper {#integration}

An update proof establishes the checksum of a specified memory range. [Streaming accounting](/sample/stream-state.html#accounting) identifies the range actually processed by this call. Connecting them lets a wrapper preserve the cumulative checksum at each return and compare the whole original data with the trailer. [The cross-call argument](/sample/stream-proof.html) carries that state into the next call.

For gzip file operations, [file reads and buffering](/sample/gzip.html#reading) extend the guarantee to file chunks and bytes returned to the application. Checksums thus connect algorithms, streaming, wrapper validation, and application interfaces rather than standing as isolated arithmetic results.
