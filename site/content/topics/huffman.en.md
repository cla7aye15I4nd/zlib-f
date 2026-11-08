## From symbol counts to decodable words {#connection}

[Match selection](/verification/matching.html) removes repeated bytes but leaves symbols to encode. Suppose literals `A`, `B` and length 6/distance 2 have been selected for `ABABABAB`. Emission must still distinguish A, B, a length code, a distance code and the end-of-block marker. Huffman coding gives frequent symbols short words and less frequent symbols longer words, while allowing a receiver to identify each symbol in consecutive bits.

zlib counts and constructs separate alphabets for literal/length symbols and distances. Length 6 increments one length-code frequency; distance 2 increments one distance-code frequency. Neither becomes six occurrences of byte A or B. The end marker also needs a code. A dynamic block sends a description of its chosen codes; a fixed block uses codes prescribed by the format.

This construction serves dynamic blocks. To first see symbols become actual compressed bytes, go directly to the [fixed-block field trace](/sample/blocks.html#example), which uses prescribed codes. Stored blocks bypass symbol coding. Building a dynamic candidate informs the cost comparison; it does not mean every emitted block sends a custom tree.

<figure class="bk-route-flow" aria-label="From frequencies to dynamic codes"><ol><li><strong>Count frequencies</strong><span>Identify the symbols this block uses and their occurrence counts.</span></li><li><strong>Merge a tree</strong><span>Repeatedly join the two lighter subtrees to obtain initial symbol depths.</span></li><li><strong>Assign bounded lengths and words</strong><span>Repair lengths beyond the format limit, then assign canonical words in a fixed order.</span></li><li><strong>Send the description</strong><span>Describe the lengths before emitting records with those codes.</span></li></ol><figcaption>The decoder receives a length description and bits, never the compressor's in-memory tree pointers.</figcaption></figure>

## Frequencies small enough to calculate {#example}

Three records make a useful complete-block trace but do not reveal much about unequal frequencies. [Merge-tree construction](/sample/huffman-tree.html) therefore uses abstract counts `A:8, B:4, C:2, D:2`. These are 16 symbol occurrences in one coding alphabet. A, B, C and D label leaves; they are not a recount of the earlier eight input bytes.

Merging lighter nodes produces lengths `1,2,3,3`. The weighted payload cost is `8×1 + 4×2 + 2×3 + 2×3 = 28` bits, against 32 bits with two bits per symbol. This compares symbol payload only; it has not paid for a dynamic description. A tree that reduces payload does not guarantee that the dynamic block will be selected.

## From tree depths to the receiver {#handoff}

[Length limits and the coding description](/sample/huffman-lengths.html) continues with lengths `1,2,3,3`. Both ends assign `0,10,110,111` by the same rule, so the receiver identifies C at `110` and knows where to read the next symbol. A deeper small tree then shows why long codes cannot simply be clamped and how repair preserves decodability. Finally, repeated-length instructions compress hundreds of lengths, with an explicit account of how the receiver recovers them.

[Tree construction and decoding agreement](/sample/huffman-proof.html) relates these operations to actual arrays and Lean results: leaves cannot be repeated or omitted, parents must be available before children use them, repair must retain legal code space, and the emitted description must reconstruct the same lengths. It also explains why decodable words and protection of shared storage require different information.

With codes available, the main process returns to [block selection and output](/verification/output.html): compare the dynamic description cost with fixed and stored alternatives, then write bits for the selected records. Continue to [decompression and decoding](/verification/decoding.html) to follow how the receiver uses those lengths.
