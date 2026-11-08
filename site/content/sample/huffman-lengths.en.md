[The merge tree](/sample/huffman-tree.html) has given A, B, C and D depths `1,2,3,3`. The encoder knows those depths, but the receiver has neither the tree nor a way to identify symbols in the next bits. Both ends need a rule that reconstructs the same words from lengths and symbol order alone: canonical coding. These lengths assign A through D the words `0,10,110,111`.

This small tree happens to satisfy the format limits. Deeper merge trees can exceed DEFLATE's maximum code widths. We first encode and decode a message with legal lengths, then examine why overlong words cannot simply be clamped. The repaired lengths determine the final words and must also reach the receiver in the dynamic description. The last section connects that description in receiver order.

## Encoding and recovering four symbols {#example}

The previous chapter produced initial lengths `A:1, B:2, C:3, D:3`. Both ends assign words by placing shorter codes first and ordering equal-length codes by symbol number. They need no left/right orientation from the original tree. Length one starts at `0`; skipping its occupied branch makes length two start at `10`; skipping that branch makes length three start at `110`:

| Symbol | Length | Canonical word | Stored low-first integer, hexadecimal |
| --- | --- | --- | --- |
| A | 1 | `0` | `0x0` |
| B | 2 | `10` | `0x1` |
| C | 3 | `110` | `0x3` |
| D | 3 | `111` | `0x7` |

For a short message `ABCD`, concatenation gives `0 | 10 | 110 | 111`: nine bits. Given the lengths and symbol order, a decoder rebuilds the same table. It recognizes A at `0`, B at `10`, then C at `110` and D at `111`. Each step consumes only its word and leaves the later bits for the next symbol.

The final column needs both a value and a width. For C, stored `0x3` has code length 3, so the three-bit integer is `011`. Taking low bits first sends `1,1,0`, the canonical word `110` seen by the receiver. Treating integer 3 as only the two bits `11` would omit a bit belonging to C. [The bit writer](/sample/bits.html#order) follows that convention through a complete fixed block.

This round trip demonstrates symbol words, not a complete DEFLATE block. A real block also needs permitted symbol alphabets, the end marker `END_BLOCK`, a block header and its length description. First resolve a problem that can prevent the code table from existing at all; then connect the operations to the actual C and description.

## Depths and the length limit {#depths}

DEFLATE permits at most 15 bits for literal/length and distance codes, and 7 for the small tree used to describe lengths. Unused symbols have length zero.

A long Huffman tree can exceed the format limit. Simply clamping each deep leaf would create too many short code words. To see this with small numbers, use a **teaching limit of 3**, not DEFLATE's actual limit, and abstract frequencies `A:8, B:4, C:2, D:1, E:1`. Huffman merging gives depths `1,2,3,4,4`. How can we tell whether lengths fit together? One length-b word occupies `2^-b` of all binary paths: for example, `0` occupies the half starting with zero, so no other word may start with it. The sum of these shares is the Kraft sum. Above one means the code cannot fit; equality means it fills the space completely. The original lengths satisfy:

```text
1/2 + 1/4 + 1/8 + 1/16 + 1/16 = 1
```

Clamping to `1,2,3,3,3` changes the sum to `9/8`. Five leaves still exist, but the proposed code occupies more space than a binary prefix tree has. A legal maximum length alone does not make the assignment usable.

## Repairing the length counts {#repair}

First list how many symbols have each length: this is a histogram. Write `bl_count[b]` for the number with length b and `L` for the limit. The source also keeps `overflow`, a count of traversed nodes whose parent-derived length exceeds the limit; it controls how many repair rounds remain. In the five-symbol example the two depth-four leaves give `overflow=2`. Deeper trees can include internal nodes in this count too. Repair changes these counts before changing individual leaves. It finds the largest occupied length `b` below the limit `L`, removes one code at that length, creates two at `b+1`, and removes one at length `L`:

This is **teaching bookkeeping**, not a verbatim C excerpt:

```text
bl_count[b]     -= 1
bl_count[b + 1] += 2
bl_count[L]     -= 1
overflow       -= 2
```

Splitting one length-b leaf into two children preserves Kraft weight and adds one leaf. Removing a length-L leaf restores the leaf count and subtracts `2^-L` of weight. For the example, the clamped counts are one length-1, one length-2 and three length-3 leaves. Choose `b=2`: the repaired counts are one length-1 and four length-3 leaves. Their sum is `1/2 + 4/8 = 1`.

The source then reconstructs individual lengths by scanning the retained nodes backwards, assigning the longest classes first and skipping internal nodes. In the example, A keeps length 1 and the other four leaves receive length 3. Their payload cost becomes `8×1 + 4×3 + 2×3 + 1×3 + 1×3 = 32` bits. The unrestricted tree cost 30 bits; satisfying a format limit can increase cost.

Canonical assignment after repair gives A, B, C, D, E the words `0, 100, 101, 110, 111`. Thus `ABCDE` becomes `0 | 100 | 101 | 110 | 111` and decodes to the original message; the stored integers are `0, 1, 5, 3, 7`. This five-symbol example completes the path from merge depths to bounded lengths, words and decoding. Its limit of 3 remains a teaching condition.

### Connecting the example to actual length calculation {#length-code}

`gen_bitlen` sets the root's length to zero. It traverses the retained nodes from parent to descendant, reads `Len(parent)+1`, and clamps that value to the descriptor's maximum. The maximum is 15 for literal/length and distance codes, and 7 for the smaller code-length alphabet. Unused symbols keep length zero.

Only leaf lengths enter `bl_count`: `bl_count[b]` counts symbols assigned length `b`. This pass also estimates how many payload bits each coding choice would use. `opt_len` is the accumulated bit cost using the new dynamic codes; `static_len` is the cost using the predefined fixed codes, where such a tree exists. For each symbol occurrence, the cost includes its code length and any extra numeric bits needed to specify a match length or distance. A length code might identify a range, for example, while extra bits select the exact length within that range. Thus computing lengths and estimating the payload are linked, but the length is not itself the entire cost of a match.

The source increments `overflow` for every traversed node whose parent-derived length exceeds the limit, including internal nodes. It is not simply a counter of overlong leaf codes. In this small tree, two depth-four leaves contribute overflow 2. For deeper subtrees, the internal-node contributions matter to the repair count.

In the loop below, `s` points to compressor state, `max_length` is the selected limit in bits, and local `bits` searches downward for the occupied length called b in the explanation. `s->bl_count` is the histogram just computed. The actual repair loop is reproduced verbatim from pinned [`trees.c:583–593`](https://github.com/madler/zlib/blob/757f0527154291bcf6bfbd6396ecde6bedd2db95/trees.c#L583-L593):

```c
    do {
        bits = max_length - 1;
        while (s->bl_count[bits] == 0) bits--;
        s->bl_count[bits]--;        /* move one leaf down the tree */
        s->bl_count[bits + 1] += 2; /* move one overflow item as its brother */
        s->bl_count[max_length]--;
        /* The brother of the overflow item also moves one step up,
         * but this does not affect bl_count[max_length]
         */
        overflow -= 2;
    } while (overflow > 0);
```

Substitute the example's limit 3: initialization sets `bits=2`, whose count is nonzero. The three stores change `(1,1,3)` to `(1,0,3)`, then `(1,0,5)`, then `(1,0,4)`. Subtracting two makes overflow zero and ends the loop. [`Lines 600–610`](https://github.com/madler/zlib/blob/757f0527154291bcf6bfbd6396ecde6bedd2db95/trees.c#L600-L610) then scan retained nodes backwards, skip internal nodes, write four length-three leaves and one length-one leaf, and adjust the cost.

The arithmetic is useful only if the search for `b` finds a nonempty class, the final-class decrement does not underflow, and the reverse scan has enough leaf entries. Those are consequences to establish from the full built tree and its retained order. Treating an arbitrary list of clamped lengths as if it already had those properties would hide the important part of the repair.

## Canonical words and reversed storage {#canonical}

Both round trips above use canonical assignment. Once lengths are final, this assignment no longer needs the merge tree's left/right orientation. `gen_codes` derives the first word of each length from the histogram. Here `bits` is the code length being assigned, in bits; `code` holds the integer start word being calculated, and `next_code[bits]` saves the next unused word of that length. Left shift by one (`<< 1`) appends a zero bit when moving to the next length. These two lines are verbatim from pinned [`trees.c:213–214`](https://github.com/madler/zlib/blob/757f0527154291bcf6bfbd6396ecde6bedd2db95/trees.c#L213-L214):

```c
        code = (code + bl_count[bits - 1]) << 1;
        next_code[bits] = (ush)code;
```

For the four-symbol example, length one's start is 0. Length two starts at `(0+1)×2=2`, or `10`. Length three starts at `(2+1)×2=6`, or `110`. The counts must describe the actual lengths, with `bl_count[0]=0`.

Symbols are then visited in numeric order. The loop variable `n` is the symbol number, and `max_code` is the largest symbol number included by preparation. In its node record, `Len` is the assigned bit length and `Code` is the integer to be stored for the low-first writer. The assignment is verbatim from [`lines 223–227`](https://github.com/madler/zlib/blob/757f0527154291bcf6bfbd6396ecde6bedd2db95/trees.c#L223-L227):

```c
    for (n = 0;  n <= max_code; n++) {
        int len = tree[n].Len;
        if (len == 0) continue;
        /* Now reverse the bits */
        tree[n].Code = (ush)bi_reverse(next_code[len]++, len);
```

`len` reads the current symbol's length; zero skips assignment. C has length three, takes `next_code[3]=6` and increments it to 7, then reverses three bits to store 3. D takes 7, whose reversal is still 7. The postfix `++` must supply the old value, and `bi_reverse` must reverse exactly `len` bits. The low-first writer can then emit the canonical word, rather than sending C as `011`.

<div class="zl-demo-mount"><zlib-demo kind="huffman"><p>The four-symbol example has lengths 1,2,3,3 and Kraft sum 1. Shortening B to length 1 oversubscribes the code space. Unused symbols have length zero.</p></zlib-demo></div>

Canonical assignment lets the encoder send lengths rather than a pointer-shaped tree. Both sides use the same symbol order and counting rule, defined precisely in the [canonical Huffman specification](/reference/docs/spec/format/README.html#canonical-huffman-codes). The remaining problem is how to send hundreds of lengths economically.

## Encoding runs of lengths {#runs}

The literal/length and distance lengths form two sequences, including zeros for absent symbols. Sending each as a raw fixed-width number would often waste much of the dynamic block's saving. DEFLATE therefore has a 19-symbol code-length alphabet. Symbols 0 through 15 give a length directly. Three further symbols describe runs:

| Symbol | Meaning | Extra numeric bits |
| --- | --- | --- |
| 16 | Repeat the previous length 3–6 times | 2 bits, count minus 3 |
| 17 | Emit 3–10 zeros | 3 bits, count minus 3 |
| 18 | Emit 11–138 zeros | 7 bits, count minus 11 |

A 16 instruction needs a preceding length; 17 and 18 do not. Consider four copies of 3, ten zeros, one 2, then eleven zeros. This is a teaching fragment of a length sequence, not a complete DEFLATE data tree by itself. One source-compatible decomposition is:

```text
3, 16(extra=0), 17(extra=7), 2, 18(extra=0)
```

Expansion gives 3 at positions 1–4, zeros at 5–14, 2 at 15 and zeros at 16–26: all 26 entries recovered. The first direct 3 establishes the previous length. Symbol 16 adds three more. Symbol 17 adds ten zeros, the direct 2 changes length, and symbol 18 adds eleven zeros. The numbers in parentheses are values for their stated widths, not additional code-length symbols. Long runs are split when they reach the instruction's maximum. The source tracks the current run length with `count`, measured in **length entries**, not bits or input bytes. `max_count` is the largest run it will collect before emission; `min_count` is the threshold at which a repeat instruction is worthwhile. Those thresholds depend on whether this is a zero run, a continuing nonzero run, or a new length.

Why is another Huffman tree useful? The payload symbols have been compressed, but their description is itself a long list with repeated zeros and lengths. That repetition makes the description worth coding too.

`scan_tree` first executes this run logic to count the code-length symbols. `build_bl_tree` constructs their Huffman tree. `send_tree` later follows the corresponding run decomposition and actually emits the codes and extra bits. The two passes save buffering an additional instruction sequence, at the cost of requiring their decisions to agree. A guard length `0xffff` at `max_code+1` ends the final run; it is compared as a sentinel and must not become a code-length-alphabet index.

For the excerpt, `curlen` is the current repeated length, `prevlen` is the last length already described, `count` is the number of remaining entries in this run, and `s->bl_tree` contains the codes for the 19 description symbols. `REP_3_6` names symbol 16; `send_code` writes its Huffman word and `send_bits` writes the following fixed-width number. Pinned [`trees.c:772–783`](https://github.com/madler/zlib/blob/757f0527154291bcf6bfbd6396ecde6bedd2db95/trees.c#L772-L783) contains this verbatim nonzero-run branch:

```c
        } else if (curlen != 0) {
            if (curlen != prevlen) {
                send_code(s, curlen, s->bl_tree); count--;
            }
            Assert(count >= 3 && count <= 6, " 3_6?");
            send_code(s, REP_3_6, s->bl_tree); send_bits(s, count - 3, 2);
```

For the four 3s, `curlen=3` differs from the previous length, so the branch sends a direct 3 and decreases count from 4 to 3. It then sends symbol 16 (`REP_3_6`) with the two-bit value `3−3=0`. The following zero-run branches send ten zeros as 17 plus three-bit 7, and eleven as 18 plus seven-bit 0. `Assert` marks a source check; it cannot stand in for a proof about actual callers.

## The dynamic description on the wire {#description}

There is one final level to make explicit. To decode the run instructions, the receiver needs the small code-length tree first. Its own lengths are at most 7, so they can be sent as raw three-bit values in this prescribed order:

```text
16,17,18,0,8,7,9,6,10,5,11,4,12,3,13,2,14,1,15
```

The [dynamic-code specification](/reference/docs/spec/format/README.html#dynamic-codes) defines this description layer. The encoder drops an unused tail of this order but announces at least four entries. Each count says how many entries this description includes: `lcodes` counts literal/length lengths in symbol-number order; `dcodes` counts distance lengths; `blcodes` counts announced small-tree lengths in the prescribed order above. These counts include zero-length entries within the transmitted range, rather than counting only nonzero codes.

Pinned [`trees.c:841–843`](https://github.com/madler/zlib/blob/757f0527154291bcf6bfbd6396ecde6bedd2db95/trees.c#L841-L843) emits the three count fields verbatim:

```c
    send_bits(s, lcodes - 257, 5);  /* not +255 as stated in appnote.txt */
    send_bits(s, dcodes - 1,   5);
    send_bits(s, blcodes - 4,  4);  /* not -3 as stated in appnote.txt */
```

The wire fields for those three counts are named HLIT, HDIST and HCLEN. Each stores the count minus its permitted minimum, saving bits because smaller counts are not needed. For example, `lcodes=257, dcodes=1, blcodes=4` encodes them as `257−257=0, 1−1=0, 4−4=0`, with widths 5, 5 and 4 respectively. Adding the offsets back tells the receiver to read four raw three-bit lengths first, for symbols 16, 17, 18 and 0. After using that small tree to decode the following instructions, it must recover 257 literal/length lengths and one distance length. This demonstrates only the count-field conversion: no actual lengths have been specified, and no complete legal block has been constructed or claimed.

There is no endless chain of small trees describing other trees: the outermost layer sends raw three-bit values whose interpretation the receiver already knows. The complete dependency is now finite: raw lengths describe the small tree; that tree decodes run instructions; those instructions recover the data-tree lengths; those lengths determine payload codes. `build_bl_tree` includes the instruction costs and raw-description/count costs in the dynamic candidate's accounting. [Block selection](/sample/blocks.html#selection) can then compare that candidate against fixed and stored output.

The dynamic candidate now returns two related products to [block selection](/sample/blocks.html#selection): words used to encode the actual records, and the cost of describing those words to the receiver. If dynamic coding is selected, the description precedes the payload; fixed and stored selections take their own emission branches.

The proof from the actual constructor to a complete dynamic block is unfinished. It must connect actual caller premises, repaired lengths, both description passes and the same emitted bits. [Tree construction and decoding agreement](/sample/huffman-proof.html) follows those steps through local results and remaining connections; [the tree implementation argument](/reference/docs/proof/trees.html) gives detailed statements.
