The [Adler-32](/sample/adler.html) and [CRC-32](/sample/crc.html) algorithms are in place. Now connect their recurrences to actual delayed reductions, tables, word reads and combination helpers.

Separate three claims: no-fault execution, exact numeric behavior for arbitrary seeds, and a checksum of particular original bytes. The last additionally needs genuine prefix checksums and correct lengths.

## Independent recurrences {#model}

The independent [format definitions](/reference/source/ZlibF/Spec/Format/Checksum.html) define Adler through bytewise modular updates and CRC through bytewise XOR and eight reflected bit steps. Neither definition invokes the translated checksum function or its tables.

Folding over X and then Y equals folding over `X ++ Y`. This establishes model-level incremental meaning. It does not show that the pointer loop visits that list or its unrolled arithmetic computes the same step.

Execution supplies those facts on the actual heap. After `k` reads, the pointer is at `off+k` and the register represents the first `k` requested bytes. Each iteration preserves meaning and access rights.

## Machine arithmetic {#arithmetic}

Adler's mathematical modulus is 65521. Machine unsigned overflow uses a power-of-two modulus. These are not interchangeable: `2^32 mod 65521 = 225`, so an unnoticed 32-bit wrap before reduction can change the desired answer.

The selected LP64 additions use 64-bit `unsigned long`. For up to 5552 steps starting from masked 16-bit seed halves, a convenient bound is:

```text
a ≤ 65535 + 255j
s ≤ 65535 + j(65535 + 255×5552)
```

For `j≤5552`, these give `a≤1481295` and `s≤8224215375`, below `2^64`. Thus the additions agree with natural-number arithmetic. Congruence then justifies postponing reduction. The earlier 32-bit NMAX calculation assumed reduced components; the wider bound also accommodates the masked arbitrary seeds used by the numeric execution argument.

CRC's `UInt32` XOR and logical shifts implement the GF(2) register directly. Tables must equal polynomial steps, not merely fit their type. Word recurrences also track widened temporaries, byte order and the final 32-bit projection.

## Memory views {#memory}

Both updates retain the whole heap and ownership. Readability requires `offset+length≤array.size`; dereferences occur before the endpoint. An empty range can use the object's one-past pointer.

CRC word alignment depends on the address, not just the array index. The model gives allocated byte blocks an aligned origin; static and embedded arrays have arbitrary stable origin residues. The [general byte-view theorem](/reference/source/ZlibF/Proof/crc32.c.views.html#L567) covers those represented views and residues. It does not prove a general machine ABI or every effective-type alias.

In the selected eight-byte, five-lane branch, 47 initial bytes leave at least one 40-byte block after alignment. That matters before the pre-decrement block loop. Row indices stay below 8, byte indices below 256, and extraction shifts at most 56 bits in a 64-bit word. These facts justify accesses; polynomial invariants justify their contents and merges.

The [platform premise](/reference/docs/spec/platform.html) bounds each represented byte object below `2^63` bytes, not total stream length. It must not be silently inserted into checksum statements with wider domains. General C alignment, casting and aliasing correspondence remain in the [trusted base](/reference/docs/trusted-base.html).

## Combined lengths {#composition}

Adler combination expands two independently started component sums, removes the duplicated initial one, and counts the first chunk's contribution to new prefixes. A wrong second length produces a number without a concatenation guarantee.

CRC's `T^(8n)` advance has equivalent binary-matrix and polynomial representations. The selected source uses polynomial multiplication. The repeated-squaring argument connects `x2n_table`, length-bit iteration and actual `multmodp` calls to the independent zero-bit recurrence.

Termination has a real domain condition. `multmodp` scans the low 32-bit operand from bit 31; it needs a set bit. The operator-generation result must establish that condition before multiplication. Any nonzero 64-bit integer is not enough. The [`crc32_combine_op` contract](/reference/functions/crc32_combine_op.html) therefore uses generated operators, including the zero rejection result. No unproved callee contract substitutes for the execution theorem.

## Queries and seed domains {#domains}

Adler's one-byte fast path precedes its NULL check. The project's explicit initialization-query domain is NULL with zero length; this restriction appears in the [deviations](/reference/docs/deviations.html). CRC checks NULL first and returns zero for any supplied length. A non-NULL empty CRC update preserves the incoming low 32 bits.

Adler also distinguishes normal checksums from forged seed words. For `adler32_z(0xfffffff0,"\0",1)`, the masked components are 65520 and 65535. Their second sum is 131055; one conditional subtraction leaves 65534, producing `0xfffefff0`. Fully reducing the starting components would instead leave high component 13. The call is memory-safe; the naive arbitrary-seed functional statement is wrong.

The numeric specification [`adlerValue`](/reference/source/ZlibF/Spec/Public/Checksums.html#L41) retains that one-byte behavior and canonicalizes other lengths. Genuine incremental seeds agree with the ordinary recurrence. Entry widths, non-NULL empty ranges, negative combine lengths and generated operators need distinct cases.

## Exact results {#evidence}

The current source contains [`adler_z_public` and `adler_public`](/reference/source/ZlibF/Proof/public-adler-update.html#L36): all represented readable ranges and all seeds, the explicit zero-length NULL query, exact numeric result and unchanged heap. The [Adler combine results](/reference/source/ZlibF/Proof/public-adler-combine.html#L118) give total execution for scalar arguments, negative-length rejection, and concatenation when the checksums and second length describe actual sequences.

The [CRC update results](/reference/source/ZlibF/Proof/public-crc-updates.html#L18) retain fixed-global premises and the full represented byte-view domain. The [CRC combination results](/reference/source/ZlibF/Proof/public-crc-combine.html#L76) cover generators, generated-operator application and both combine widths with exact polynomial results and immutable heaps. [`get_crc_table`](/reference/functions/get_crc_table.html) separately specifies the static pointer and all 256 entries.

These scopes do not establish the complete compressor or decoder: those callers must checksum exactly their accepted or produced bytes and validate the appropriate wrapper field. Full-domain C correspondence remains **to confirm** where the reference records model gaps. [Progress](/reference/docs/progress.html#group-checksums) owns current registration and acceptance evidence; the [component arguments](/reference/docs/proof/README.html) provide the detailed derivations.
