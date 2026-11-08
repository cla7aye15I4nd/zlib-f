The previous two chapters followed bytes through [refill and sliding](/sample/window.html), then through [candidate search and lazy decisions](/sample/match-search.html). The observable promise is simple: when a strategy replaces input with a match, expanding that match must recover the bytes it replaced. Faster rejection and a smaller search budget may change the chosen representation, but they must preserve that promise.

The proof follows the same handoffs as the implementation. First retain the right bytes and positions. Then justify the chain being followed. Then establish what a returned search result means. Finally connect the strategy's committed symbols to the input prefix. These are related obligations; a theorem about one handoff does not supply the others automatically.

## Bytes across a moving representation {#representation}

The window-shape fact is `strstart + lookahead ≤ 2W`. It explains why refill fits, but says nothing about the content copied. A functional relation must also connect each retained window position to its logical stream position. If the represented stream base is L, a retained array byte at i agrees with the corresponding input byte at L+i.

After a slide by W, the new base is L+W and the new array byte at i is the old byte at i+W. The two expressions name the same logical position:

```text
(L + W) + i = L + (i + W)
```

The window example made this concrete: current position 800 and candidate 700 became 288 and 188 after a slide of 512. Byte identities and distance 100 were preserved together. A proof that only subtracts 512 from the counters would miss the necessary content equality.

The allocation argument is separate. The slide copies `[W, strstart+lookahead)` down to the base; the destination count is `strstart+lookahead-W`. Bounds must be derived before interpreting the source's unsigned subtractions, and the two ranges must be valid and disjoint for `memcpy`. The natural-number theorem [slide_copy](/reference/source/ZlibF/Proof/deflate.c.engine.window.html#L52) establishes the corresponding range arithmetic under `W ≥ 512`, the shape bound and the slide test. It is a numeric lemma, not by itself a theorem executing all of `fill_window`.

Read operations then connect caller bytes to the actual window array and update the input cursors. The [read_buf_ok theorem](/reference/source/ZlibF/Proof/deflate.c.engine.readbuf.html#L99) describes a scoped translated copy and its accounting. Its buffer and stream premises must be established at the call site. Guard initialization must stay within the allocation without extending the logical input. Likewise, a signed negative `block_start` after a slide must remain allowed; imposing nonnegativity everywhere would silently remove real execution paths.

## Meaningful links and overwritten slots {#hash}

The source does not initialize every `prev` slot at allocation time. It clears the heads and writes predecessor slots as positions are inserted. Requiring all slots to contain valid links would describe a different initialization policy. The useful statement is about the slots that the search can actually reach.

[HashChains](/reference/source/ZlibF/Proof/deflate.c.engine.chains.html#L29) records this idea. A nonzero reachable position p must be a meaningful inserted position while its slot still belongs to it. The recorded three-byte string hashes to the selected bucket, and the predecessor stored at `p & (W-1)` is smaller than p. The `top` parameter limits the generation of insertions being described: the condition `top ≤ p+W` identifies links whose ring slot has not been reused by a position one window later.

Insertion changes two cells. The predecessor slot receives the old head; the head receives the new position. The proof splits newly reachable nodes into the new position and nodes already reachable in the old chain. It also proves that writing the new slot does not destroy a still-retained predecessor. [chains_insert](/reference/source/ZlibF/Proof/deflate.c.engine.chains.html#L76) proves that structural preservation for the mathematical table functions. [INSERT_STRING_ok](/reference/source/ZlibF/Proof/deflate.c.engine.macros.html#L177) gives the actual translated reads and stores under its heap, parameter and range assumptions. Connecting the two is how a structural statement becomes useful to a program proof.

Sliding is another change of representation. Every retained position decreases by W, and subtracting W preserves its slot modulo W. Window contents move by exactly the same offset. [chains_slide](/reference/source/ZlibF/Proof/deflate.c.engine.chains.html#L138) transports the chain relation through those transformations; [slide_hash_ok](/reference/source/ZlibF/Proof/deflate.c.engine.slide.html#L166) describes the table-update execution. Unused garbage slots may be transformed too. They remain harmless because no proof treats them as meaningful chain links.

The skipped third-byte comparison also needs a content fact, not an intuition about collisions. [hkey_third](/reference/source/ZlibF/Proof/deflate.c.engine.hash.html#L139) derives third-byte equality from equal keys, equal first two bytes and the stated hash parameters. This is precisely the fact used after the cheap probes pass.

## Search meaning and termination {#search}

A search invariant keeps the current candidate on the justified chain, the cached endpoint bytes equal to the window bytes they represent, and the best length within its allowed range. The body can reject a candidate without changing the best result. When it improves the result, the invariant must include a witness: an earlier position, an allowed distance, and equality of every byte in the claimed range.

The unrolled comparison is related to a simpler mathematical scan. [firstMis_spec](/reference/source/ZlibF/Proof/deflate.c.engine.match.html#L50) characterizes the first mismatch, or the maximum bound of 258. The [inner-loop result](/reference/source/ZlibF/Proof/deflate.c.engine.lminner.html#L36) connects the eight-way short-circuit condition to that scan. The memory margin establishes that all reached reads are in the actual array; the byte equalities establish that the result is a match. Each supports a different part of the conclusion.

The scoped [longest_match_ok](/reference/source/ZlibF/Proof/deflate.c.engine.lmmain.html#L212) states an execution result under `LMEnv`. That environment supplies the actual window and predecessor arrays, power-of-two W from 512 through 32768, masks, room through the comparison range, a valid earlier initial candidate and the semantic chain facts. The theorem returns `min(best, lookahead)`, changes only `match_start`, and distinguishes two cases:

- No improvement over `prev_length`: the old `match_start` is retained.
- An improvement: `match_start` witnesses byte equality, a preceding position, an allowed distance and length at most 258.

The first case is not a fresh matching witness for the current position. The strategy must use the previous-state relationship when it decides to retain the earlier match. Nor does this theorem promise maximality among all window positions; search budget and nice-length exits deliberately avoid that requirement.

Termination can use the position of the current chain node. Every continuing predecessor is strictly smaller, and the represented position fits within the runtime loop budget. The [lm_loop_ok proof](/reference/source/ZlibF/Proof/deflate.c.engine.lmmain.html#L77) uses `cur_match.toNat` as its decreasing measure. It does not depend on assuming that the unsigned chain counter can never wrap from zero. This is important when relating the configured defaults to the wider [deflateTune contract](/reference/functions/deflateTune.html). Establishing the required chain for every admitted tuning and call history is still a caller-composition obligation.

## From a decision to a symbol sequence {#symbols}

The final step reconnects search to the stream. At an ordinary strategy boundary, distinguish the already committed logical prefix, any deferred byte, and the remaining unprocessed input. A lazy step can advance `strstart` while preserving a byte as deferred work; it has not thereby emitted that byte. A relationship using only `strstart` as the number of committed output bytes would be wrong.

For the example `XABCDEFGQ`, emitting literal X extends the committed expansion by one byte. Accepting the retained seven-byte match then extends it by `ABCDEFG`. A match can be longer than its distance: the independent expansion reads from the growing logical history, one byte at a time. When the corresponding window bytes agree, induction over the copied length shows that each newly produced byte is the required next input byte. For a distance d, step j reads the logical source at `S+j-d`. If `j < d`, that source is in earlier history. Otherwise it is the byte produced at step `j-d`, whose meaning is already available from the induction. This covers reads that reach output of the same match.

The strategy also needs exact length and distance bounds before tallying. A literal is a byte; a match has length 3 through 258, so its stored length offset is 0 through 255. Its positive distance is at most the format limit 32768; the selected search path establishes the stronger implementation limit `W-262`. Tallying appends one three-byte record and updates the appropriate frequencies. The [tallyCalls_preserves result](/reference/source/ZlibF/Proof/trees.c.tally-support.html#L46) gives a scoped composition of actual valid tally calls with enough symbol room. Its own statement explicitly does not establish the translated strategy's input history or its emitted block.

That is the boundary to [Huffman construction](/sample/huffman-tree.html), [block selection](/sample/blocks.html) and [output preservation](/sample/proof.html). The complete argument must carry the **same** selected symbols through tallying, tree construction and emission, while retaining their meaning and unread storage. It cannot separately prove properties about unrelated symbol lists and treat them as the compressor's actual decisions.

The remaining initialization, strategy-loop, refill, flush and public-history connections are **to confirm** wherever the cited result does not cover them. The [implementation argument](/reference/docs/proof/deflate.html) describes their composition; [current progress](/reference/docs/progress.html) records accepted scope and remaining work. The public [deflate goal](/reference/functions/deflate.html#formal-target) keeps its own explicit domain.
