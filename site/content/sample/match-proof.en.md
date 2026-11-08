[Candidate search and lazy decisions](/sample/match-search.html) allow the compressor to visit fewer positions or delay a choice by one byte. Those choices can change compression ratio, but must preserve recovered content. The relation to maintain is: **after each committed literal or match, independently expanding the symbols gives exactly the committed input prefix.** This connects the window and search to the later encoder, which must preserve the meaning of those same symbols.

Return to processed `ABCQABCR` and current `ABCQABCX`. Length 3, distance 4 recovers `ABC`; length 7, distance 8 recovers `ABCQABC`. They cover different amounts of input, but either can be correct. If the second distance is mistakenly written as 4, copying produces R rather than Q at the fourth byte. The wrong reference can stay in bounds while changing the data. The argument therefore follows byte identity through retention, candidate indexing, comparison and the actual committed choice, rather than stopping at array bounds.

## Split one choice into connected guarantees {#claim}

The proof takes the actual translated execution, explicit caller premises, and a relation between the state and logical input. It must establish a fault-free result, the correct next state, and byte meaning. A natural-number equality supplies only part of that argument. Each layer's premises must be established by the preceding actual layer; an unproved callee contract cannot be assumed.

This explains the order below. The [window](/sample/window.html) retains source bytes and keeps their positions meaningful after moving them. The candidate chain justifies the inserted positions reached by search. Search supplies equal-byte witnesses for an accepted length. The strategy then commits a match from the correct starting position. A local theorem at one handoff does not automatically supply the whole `deflate` API guarantee.

## Bytes across a moving representation {#representation}

Consider a fault that would invalidate later search: changing the position counters without moving the corresponding bytes to their new indexes. Every number could remain in bounds while search reads the wrong history. Excluding that fault requires a statement about both storage ranges and contents.

To state the storage bound, name three byte quantities. `W` is the configured window scale; the byte array has capacity `2W`. `strstart` is the array index where current input begins, and `lookahead` counts real unprocessed bytes already loaded after that index. For `W=512`, index 800 and 100 loaded bytes end at index 900, inside the 1024-byte allocation. In general, the window-shape fact is `strstart + lookahead ≤ 2W`. It explains why refill fits, but says nothing about the content copied.

A functional relation must also connect each retained window position to its logical stream position. Call the logical stream position represented by array index zero L, measured in bytes from the beginning of the input. Let i be an array byte index. A retained array byte at i must agree with input byte L+i. Thus when L=512 and i=188, that cell represents input byte 700, not byte 188.

After a slide by W, the new base is L+W and the new array byte at i is the old byte at i+W. The two expressions name the same logical position:

```text
(L + W) + i = L + (i + W)
```

The window example made this concrete: current position 800 and candidate 700 became 288 and 188 after a slide of 512. Byte identities and distance 100 were preserved together. A proof that only subtracts 512 from the counters would miss the necessary content equality.

The allocation argument is separate. The slide copies `[W, strstart+lookahead)` down to the base; the destination count is `strstart+lookahead-W`. Bounds must be derived before interpreting the source's unsigned subtractions, and the two ranges must be valid and disjoint for `memcpy`. The natural-number theorem [slide_copy](/reference/source/ZlibF/Proof/deflate.c.engine.window.html#L52) establishes the corresponding range arithmetic under `W ≥ 512`, the shape bound and the slide test. It is a numeric lemma, not by itself a theorem executing all of `fill_window`.

Read operations then connect caller bytes to the actual window array and update the input cursors. The [read_buf_ok theorem](/reference/source/ZlibF/Proof/deflate.c.engine.readbuf.html#L99) describes a scoped translated copy and its accounting. Its buffer and stream premises must be established at the call site. Guard initialization must stay within the allocation without extending the logical input. `block_start` records where the current block's original bytes begin, relative to the current array base. A slide can move that base past the block's beginning. Its signed value must therefore be allowed to become negative; imposing nonnegativity everywhere would silently remove real execution paths.

## Meaningful links and overwritten slots {#hash}

Correct window bytes do not make every table entry a usable candidate. If a later position has reused a predecessor slot, reading it as the older position's link can follow a different insertion generation. The proof needs to distinguish a value merely present in the array from a meaningful link in the current chain.

The head table stores the newest candidate position for each hash bucket. The predecessor table, named `prev`, stores the next older candidate for an inserted position. It has only W slots: positions p and p+W reuse the same slot. The source does not initialize every `prev` slot at allocation time. It clears the heads and writes predecessor slots as positions are inserted. Requiring all slots to contain valid links would describe a different initialization policy. The useful statement is about the slots that the search can actually reach.

[HashChains](/reference/source/ZlibF/Proof/deflate.c.engine.chains.html#L29) records this idea. A nonzero reachable position p must be a meaningful inserted position while its slot still belongs to it. The recorded three-byte string hashes to the selected bucket. Since W is a power of two, `p & (W-1)` computes p modulo W: it selects the predecessor slot, not the byte position to compare. The value stored in that slot must be an earlier position, smaller than p. The `top` parameter limits the generation of insertions being described: the condition `top ≤ p+W` identifies links whose ring slot has not been reused by a position one window later.

Insertion changes two cells. The predecessor slot receives the old head; the head receives the new position. The proof splits newly reachable nodes into the new position and nodes already reachable in the old chain. It also proves that writing the new slot does not destroy a still-retained predecessor. [chains_insert](/reference/source/ZlibF/Proof/deflate.c.engine.chains.html#L76) proves that structural preservation for the mathematical table functions. [INSERT_STRING_ok](/reference/source/ZlibF/Proof/deflate.c.engine.macros.html#L177) gives the actual translated reads and stores under its heap, parameter and range assumptions. Connecting the two is how a structural statement becomes useful to a program proof.

Sliding is another change of representation. Every retained position decreases by W, and subtracting W preserves its slot modulo W. Window contents move by exactly the same offset. [chains_slide](/reference/source/ZlibF/Proof/deflate.c.engine.chains.html#L138) transports the chain relation through those transformations; [slide_hash_ok](/reference/source/ZlibF/Proof/deflate.c.engine.slide.html#L166) describes the table-update execution. Unused garbage slots may be transformed too. They remain harmless because no proof treats them as meaningful chain links.

The skipped third-byte comparison also needs a content fact, not an intuition about collisions. [hkey_third](/reference/source/ZlibF/Proof/deflate.c.engine.hash.html#L139) derives third-byte equality from equal keys, equal first two bytes and the stated hash parameters. This is precisely the fact used after the cheap probes pass.

## Search meaning and termination {#search}

With correct bytes and a justified chain, we can interpret one search result. A claim of length 7 needs seven equal corresponding bytes, rather than equality only at the endpoints. A search invariant keeps the current candidate on the justified chain, the cached endpoint bytes equal to the window bytes they represent, and the best length within its allowed range. The body can reject a candidate without changing the best result. When it improves the result, the invariant must include a witness: an earlier position, an allowed distance, and equality of every byte in the claimed range.

The unrolled comparison is related to a simpler mathematical scan. [firstMis_spec](/reference/source/ZlibF/Proof/deflate.c.engine.match.html#L50) characterizes the first mismatch, or the maximum bound of 258. The [inner-loop result](/reference/source/ZlibF/Proof/deflate.c.engine.lminner.html#L36) connects the eight-way short-circuit condition to that scan. The memory margin establishes that all reached reads are in the actual array; the byte equalities establish that the result is a match. Each supports a different part of the conclusion.

First inspect the actual write that this guarantee must describe. `len` is the compared candidate's matching byte count; `best_len` is the byte count to beat, initialized from the caller's baseline `prev_length`. `cur_match` is that candidate's earlier array index, while state field `match_start` remembers the accepted source index. `nice_match` is a byte-length target at which search may stop early. Pinned [`longest_match`, lines 1543–1546](https://github.com/madler/zlib/blob/757f0527154291bcf6bfbd6396ecde6bedd2db95/deflate.c#L1543-L1546) begins its update branch with:

```c
if (len > best_len) {
    s->match_start = cur_match;
    best_len = len;
    if (len >= nice_match) break;
```

The first line requires strict improvement. Only then does the second publish the candidate as `match_start`; the third updates the best length with it. The fourth allows an early exit at the target length. At that write, the proof must already have the equal-byte witness for this candidate. Without entering the branch, the old `match_start` does not become a new witness for the current input.

The same function's [return, lines 1557–1558](https://github.com/madler/zlib/blob/757f0527154291bcf6bfbd6396ecde6bedd2db95/deflate.c#L1557-L1558) does a separate job:

```c
if ((uInt)best_len <= s->lookahead) return (uInt)best_len;
return s->lookahead;
```

The first line returns the best length unchanged when real input covers it. The second returns `lookahead` when it does not. This establishes a real-input length bound; it cannot replace the content argument. Both excerpts are actual C; the execution theorem still has to cover the omitted function body.

The scoped [longest_match_ok](/reference/source/ZlibF/Proof/deflate.c.engine.lmmain.html#L212) states an execution result under `LMEnv`. That environment supplies the actual window and predecessor arrays, power-of-two W from 512 through 32768, masks, room through the comparison range, a valid earlier initial candidate and the semantic chain facts. The theorem names the search's final internal best length `best`; it returns the smaller of that length and the real loaded input count, `min(best, lookahead)`. It changes only `match_start` and distinguishes two cases:

- No improvement over `prev_length`: the old `match_start` is retained.
- An improvement: `match_start` witnesses byte equality, a preceding position, an allowed distance and length at most 258.

The first case is not a fresh matching witness for the current position. The strategy must use the previous-state relationship when it decides to retain the earlier match. Nor does this theorem promise maximality among all window positions; search budget and nice-length exits deliberately avoid that requirement.

Termination can use the position of the current chain node. Every continuing predecessor is strictly smaller, and the represented position fits within the runtime loop budget. The [lm_loop_ok proof](/reference/source/ZlibF/Proof/deflate.c.engine.lmmain.html#L77) uses `cur_match.toNat` as its decreasing measure. It does not depend on assuming that the unsigned chain counter can never wrap from zero. This is important when relating the configured defaults to the wider [deflateTune contract](/reference/functions/deflateTune.html). Establishing the required chain for every admitted tuning and call history is still a caller-composition obligation.

## From a decision to a symbol sequence {#symbols}

Call a logical input byte position S; S+1 is its next byte. The final step excludes another shift error: search finds a valid match for S+1, but the strategy commits it as though it began at S. Both searches could be in bounds and have equal-byte witnesses, yet their composition could omit or duplicate an input byte. We therefore reconnect search to the stream. At an ordinary strategy boundary, distinguish the already committed logical prefix, any deferred byte, and the remaining unprocessed input. A lazy step can advance `strstart` while preserving a byte as deferred work; it has not thereby emitted that byte. A relationship using only `strstart` as the number of committed output bytes would be wrong.

For the example `XABCDEFGQ`, emitting literal X extends the committed expansion by one byte. Accepting the retained seven-byte match then extends it by `ABCDEFG`. A match can be longer than its distance: the independent expansion reads from the growing logical history, one byte at a time. When the corresponding window bytes agree, induction over the copied length shows that each newly produced byte is the required next input byte. Let S be the match's logical output start, d its backward distance in bytes, and j its zero-based copy step. The destination is S+j, so step j reads the logical source at `S+j-d`. Since j starts at zero, j=3 means the fourth copy. At distance 2 it reads S+1, the byte already produced at j=1.

| Copy step j | Source | Why its byte is already justified |
| --- | --- | --- |
| 0 | `S-2` | History preceding this match |
| 1 | `S-1` | History preceding this match |
| 2 | `S` | Produced at step 0 |
| 3 | `S+1` | Produced at step 1 |

In general, `j < d` reads earlier history. Otherwise it reads the byte produced at step `j-d`. A positive distance gives `j-d < j`, so induction already supplies that byte’s meaning. This justifies copying from output of the same match when length exceeds distance.

The strategy also needs exact length and distance bounds before tallying. A literal is a byte; a match has length 3 through 258, so its stored length offset is 0 through 255. Its positive distance is at most the format limit 32768. The selected search path establishes the stronger implementation limit `W-262`, in bytes: the configured scale W minus the margin reserved for input and comparison. This is the `MAX_DIST` search limit from the [candidate search](/sample/match-search.html#candidates). Tallying appends one three-byte record and updates the appropriate frequencies. The [tallyCalls_preserves result](/reference/source/ZlibF/Proof/trees.c.tally-support.html#L46) gives a scoped composition of actual valid tally calls with enough symbol room. Its own statement explicitly does not establish the translated strategy's input history or its emitted block.

The relation reaches the next component at the records. For literals A, B and length 6/distance 2, it says the three symbols expand to `ABABABAB`. [Block encoding](/sample/blocks.html#example) must turn those same symbols into fields with the same meaning. [Huffman construction](/sample/huffman-tree.html) can change their words, but not their order. [Output agreement](/sample/proof.html#meaning) connects this expansion to the actual bit stream.

The complete composition of initialization, strategy loops, refill, flush and public call sequences is unfinished. The remaining connections are in the [deflate implementation argument](/reference/docs/proof/deflate.html) and [project progress](/reference/docs/progress.html). The public [deflate target](/reference/functions/deflate.html#formal-target) also includes wrapper, output and call-boundary obligations after these records.
