The [tree constructor](/sample/huffman-tree.html) has produced parent links and retained nodes in a usable traversal order. A DEFLATE decoder will never receive those parent links. It receives code lengths, reconstructs canonical codes, and then decodes the payload. This chapter follows the transformations between those two views.

Three jobs are involved: keep lengths within the format limit, give every used symbol a deterministic word, and describe the lengths compactly enough to make a dynamic block worthwhile.

## Depths and the length limit {#depths}

`gen_bitlen` sets the root's length to zero. It traverses the retained nodes from parent to descendant, reads `Len(parent)+1`, and clamps that value to the descriptor's maximum. The maximum is 15 for literal/length and distance codes, and 7 for the smaller code-length alphabet. Unused symbols keep length zero.

Only leaf lengths enter `bl_count`: `bl_count[b]` counts symbols assigned length `b`. The same pass adds frequency times code length and extra-bit width to `opt_len`; where a fixed tree exists, it also updates `static_len`. Thus computing lengths and estimating the payload are linked, but the length is not itself the entire cost of a match.

A long Huffman tree can exceed the format limit. Simply clamping each deep leaf would create too many short code words. To see this with small numbers, use a **teaching limit of 3**, not DEFLATE's actual limit, and abstract frequencies `A:8, B:4, C:2, D:1, E:1`. Huffman merging gives depths `1,2,3,4,4`. Their Kraft sum is one:

```text
1/2 + 1/4 + 1/8 + 1/16 + 1/16 = 1
```

Clamping to `1,2,3,3,3` changes the sum to `9/8`. Five leaves still exist, but the proposed code occupies more space than a binary prefix tree has. A legal maximum length alone does not make the assignment usable.

The source increments `overflow` for every traversed node whose parent-derived length exceeds the limit, including internal nodes. It is not simply a counter of overlong leaf codes. In this small tree, two depth-four leaves contribute overflow 2. For deeper subtrees, the internal-node contributions matter to the repair count.

## Repairing the length counts {#repair}

The repair loop works on the histogram before changing individual leaves. It finds the largest occupied length `b` below the limit `L`, removes one code at that length, creates two at `b+1`, and removes one at length `L`:

```text
bl_count[b]     -= 1
bl_count[b + 1] += 2
bl_count[L]     -= 1
overflow       -= 2
```

Splitting one length-b leaf into two children preserves Kraft weight and adds one leaf. Removing a length-L leaf restores the leaf count and subtracts `2^-L` of weight. For the example, the clamped counts are one length-1, one length-2 and three length-3 leaves. Choose `b=2`: the repaired counts are one length-1 and four length-3 leaves. Their sum is `1/2 + 4/8 = 1`.

The source then reconstructs individual lengths by scanning the retained nodes backwards, assigning the longest classes first and skipping internal nodes. In the example, A keeps length 1 and the other four leaves receive length 3. Their payload cost becomes `8×1 + 4×3 + 2×3 + 1×3 + 1×3 = 32` bits. The unrestricted tree cost 30 bits; satisfying a format limit can increase cost.

The arithmetic is useful only if the search for `b` finds a nonempty class, the final-class decrement does not underflow, and the reverse scan has enough leaf entries. Those are consequences to establish from the full built tree and its retained order. Treating an arbitrary list of clamped lengths as if it already had those properties would hide the important part of the repair.

## Canonical words and reversed storage {#canonical}

Once lengths are final, code assignment no longer needs the merge tree's left/right orientation. `gen_codes` derives the first word of each length from the histogram:

```text
code = (code + bl_count[bits - 1]) << 1
next_code[bits] = code
```

It then visits symbols in numeric order. A used symbol takes the next word at its length, and that next-word counter advances. Unused symbols take no word.

Return to the four-symbol lengths `A:1, B:2, C:3, D:3`. The first available words at lengths 1, 2 and 3 are 0, binary 10 and binary 110. Assigning within each class gives:

| Symbol | Length | Canonical word | Stored low-first integer, hexadecimal |
| --- | --- | --- | --- |
| A | 1 | `0` | `0x0` |
| B | 2 | `10` | `0x1` |
| C | 3 | `110` | `0x3` |
| D | 3 | `111` | `0x7` |

`bi_reverse` reverses exactly the assigned length before the word is stored. The low-bit-first writer then emits the canonical word in its intended order. This is why numeric `0x3` for C does not mean the code word is `011` in arrival order. [The bit writer](/sample/bits.html#order) traces that convention in a complete fixed block.

<div class="zl-demo-mount"><zlib-demo kind="huffman"><p>The four-symbol example has lengths 1,2,3,3 and Kraft sum 1. Shortening B to length 1 oversubscribes the code space. Unused symbols have length zero.</p></zlib-demo></div>

Canonical assignment lets the encoder send lengths rather than a pointer-shaped tree. Both sides use the same symbol order and counting rule. The remaining problem is how to send hundreds of lengths economically.

## Encoding runs of lengths {#runs}

The literal/length and distance lengths form two sequences, including zeros for absent symbols. Sending each as a raw fixed-width number would often waste much of the dynamic block's saving. DEFLATE therefore has a 19-symbol code-length alphabet. Symbols 0 through 15 give a length directly. Three further symbols describe runs:

| Symbol | Meaning | Extra numeric bits |
| --- | --- | --- |
| 16 | Repeat the previous length 3–6 times | 2 bits, count minus 3 |
| 17 | Emit 3–10 zeros | 3 bits, count minus 3 |
| 18 | Emit 11–138 zeros | 7 bits, count minus 11 |

A 16 instruction needs a preceding length; 17 and 18 do not. Consider four copies of 3, ten zeros, one 2, then eleven zeros. One source-compatible decomposition is:

```text
3, 16(extra=0), 17(extra=7), 2, 18(extra=0)
```

The first direct 3 establishes the previous length. Symbol 16 adds three more. Symbol 17 adds ten zeros, the direct 2 changes length, and symbol 18 adds eleven zeros. The numbers in parentheses are values for their stated widths, not additional code-length symbols. Long runs are split when they reach the instruction's maximum; the source's `max_count` and `min_count` also distinguish continuing nonzero runs from newly encountered lengths.

`scan_tree` first executes this run logic to count the code-length symbols. `build_bl_tree` constructs their Huffman tree. `send_tree` later follows the corresponding run decomposition and actually emits the codes and extra bits. The two passes save buffering an additional instruction sequence, at the cost of requiring their decisions to agree. A guard length `0xffff` at `max_code+1` ends the final run; it is compared as a sentinel and must not become a code-length-alphabet index.

## The dynamic description on the wire {#description}

There is one final level to make explicit. To decode the run instructions, the receiver needs the small code-length tree first. Its own lengths are at most 7, so they can be sent as raw three-bit values in this prescribed order:

```text
16,17,18,0,8,7,9,6,10,5,11,4,12,3,13,2,14,1,15
```

The encoder drops an unused tail of this order but announces at least four entries. The header has five bits for `lcodes−257`, five for `dcodes−1`, and four for `blcodes−4`. The counts therefore determine how many raw three-bit lengths and subsequently how many literal/length and distance lengths must be recovered.

The complete dependency is now finite: raw lengths describe the small tree; that tree decodes run instructions; those instructions recover the data-tree lengths; those lengths determine payload codes. `build_bl_tree` includes the instruction costs and raw-description/count costs in the dynamic candidate's accounting. [Block selection](/sample/blocks.html#selection) can then compare that candidate against fixed and stored output.

The implementation-to-format connections still require the explicit source and caller premises marked **to confirm** in the [tree argument](/reference/docs/proof/trees.html). The next [proof chapter](/sample/huffman-proof.html) explains how the retained forest, repair accounting, canonical assignment and two description passes become one composable argument.
