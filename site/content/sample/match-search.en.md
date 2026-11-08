Retaining history lets the compressor replace current input with a shorter representation. Suppose it has processed `ABCQABCR` and is about to process `ABCQABCX`. It could write literals or emit a length/distance pair referring to equal earlier bytes. Search asks: **where can copying start, and how many real input bytes can it cover?**

Its inputs are the [window's](/sample/window.html) contiguous bytes, a current start, and a candidate chain of earlier positions. Its immediate output is a possible match for the strategy to consider, not a symbol already written to the compressed stream. With no useful match, the strategy can still emit a literal with the same original-byte meaning.

## Compare two candidates first {#example}

The recent `ABCR` agrees with current `ABCQABCX` for three bytes, then differs at R versus Q. It offers length 3 at distance 4. The older `ABCQ` agrees for seven bytes, then differs at R versus X. It offers length 7 at distance 8. There are no space bytes here: the two history fragments are adjacent and immediately followed by the current input.

The seven-byte comparison passes the end of the earliest four-character fragment and continues into the following `ABC`. A candidate is the start of contiguous bytes in one window array, not a separately stored word.

<div class="zl-demo-mount"><zlib-demo kind="search"><p>In a schematic history, the newest candidate matches ABC for length 3. Following one predecessor reaches a candidate matching ABCQABC for length 7. A one-candidate budget stops before that second candidate.</p></zlib-demo></div>

The scene labels logical positions 0, 4 and 8. Actual zlib reserves position zero for `NIL`; shifting all these positions by one preserves the example's comparisons and distances without using that sentinel as a candidate. The scene illustrates the effect of the candidate budget, not the exact hash-table contents produced by every real call.

## Candidates and distance limits {#candidates}

`INSERT_STRING` returns the previous bucket head, called `hash_head` by the strategy. The new position has already been inserted, but searching starts at the earlier head. A nonzero head must precede `strstart`, and the caller tests its distance against `MAX_DIST = W - 262` before calling `longest_match`.

The search computes `limit = max(strstart - MAX_DIST, 0)`. Its first candidate is processed by a `do` body. Therefore a first candidate exactly at the distance limit can be examined; continuing through the predecessor chain requires the **next** candidate to be strictly above `limit`. The first-body rule and the continuation rule are not interchangeable.

## From a byte scan to quick rejection {#comparison}

The direct method compares from the candidate's beginning until the first mismatch, giving lengths 3 and 7 above. Repeating that scan for every candidate would repeatedly read many shared short prefixes. zlib first asks a cheaper question: “could this candidate beat the length already found?” Only a possible improvement warrants a full scan.

`longest_match` starts with `best_len = prev_length`, where `prev_length` is the baseline supplied by its caller. If a candidate cannot improve that baseline, a full scan would be wasted work. In the ordinary byte-comparison branch, the routine first compares bytes at offsets `best_len` and `best_len-1`, then the first two bytes. A mismatch at any of these positions rejects the candidate immediately.

The ordinary byte branch is actual pinned [`longest_match` code, lines 1511–1514](https://github.com/madler/zlib/blob/757f0527154291bcf6bfbd6396ecde6bedd2db95/deflate.c#L1511-L1514):

```c
if (match[best_len]     != scan_end  ||
    match[best_len - 1] != scan_end1 ||
    *match              != *scan     ||
    *++match            != scan[1])      continue;
```

Here `scan` points to current input and `match` to a candidate; `scan_end` and `scan_end1` cache current-input bytes near the best length. The first line tests the byte needed to beat that length; the second tests its predecessor; the third tests the beginning. The fourth advances the candidate pointer before testing the second byte. `||` short-circuits left to right: any failure executes `continue`, reaching the chain continuation condition. Passing the probes leads to the continuous scan described below; these four lines alone do not certify a whole match.

Checking near the current best end first is useful when many strings share a short prefix. A candidate could agree on its first twenty bytes yet already be known to fail at the byte needed to beat the current best. The cheap probe avoids replaying those twenty comparisons. A successful probe still does not certify all bytes between the beginning and that endpoint; the scan must establish them.

The third byte has a special role. With the selected hash parameters, equal three-byte hash keys and equal first two bytes imply an equal third byte. The implementation therefore does not repeat an ordinary comparison of offset 2 before its main scan. This is a property of this short shift/XOR hash under its parameter bounds, not a general property of hash collisions.

The main byte branch compares eight successive byte pairs per unrolled condition. Short-circuit evaluation stops at the first mismatch. The end test is less frequent than one test per byte, so the established window margin must cover the furthest read, through offset 258. An alternate `UNALIGNED_OK` branch compares two-byte words and needs its own width and alignment argument; a proof of the ordinary byte branch does not cover that configuration automatically.

The routine can inspect initialized window space beyond actual lookahead. Its result is clamped to `lookahead`, and its early-stop target is also clipped to available input. Extra readable space supports fast comparisons; it does not authorize consuming imaginary input. If no candidate improves `prev_length`, `match_start` is not newly certified for the current position. The caller must distinguish that case from a genuine improvement.

## Search budgets and engine choices {#budget}

The seven-byte match above is only found if search reaches the older candidate. Stopping after the first candidate still gives a correct three-byte reference, but may miss better compression. The ordinary configuration table controls that tradeoff with the following parameters. Some representative settings are:

| Level | Engine | Good length | Lazy/insertion setting | Nice length | Chain budget |
| --- | --- | --- | --- | --- | --- |
| 1 | fast | 4, ignored by fast search | 4 | 8 | 4 |
| 6 | slow | 8 | 16 | 128 | 128 |
| 9 | slow | 32 | 258 | 258 | 4096 |

In the ordinary `longest_match`, an already good previous length reduces the chain budget by a factor of four. Reaching `nice_match` stops the search early. The budget can stop before all retained candidates are visited, and the nice threshold can stop before the longest possible candidate is found. Consequently the function name does not promise the globally longest match in the entire window.

The fast strategy commits a useful current match immediately. For sufficiently short matches it inserts the intervening strings into the hash table; for long matches it can skip those insertions and restart the running hash near the new position. This saves work at the cost of fewer future candidates. In levels 1–3, the shared configuration field has this insertion-limit role rather than the slow engine's lazy-search role.

The slow strategy uses the field as `max_lazy_match`: it may skip another search when the previous match is already long enough. `Z_FILTERED` also rejects some short matches; an ordinary distant length-three match can be rejected by the `TOO_FAR` heuristic. `Z_HUFFMAN_ONLY` bypasses match search, and `Z_RLE` looks for distance-one runs. These are choices among valid encodings, not separate decompression formats. [deflateTune](/reference/functions/deflateTune.html) exposes search parameters, so an argument covering its full domain cannot silently assume only table defaults.

## Lazy decisions and symbol commitment {#lazy}

So far, search has compared candidates for one input start. The slow strategy also compares two adjacent starts: would taking a short match now block a longer match at the next byte? Use a second example to see why finding a match is not the same as committing it. Suppose earlier history contains `XABZ` and `ABCDEFGH`, and the current input is `XABCDEFGQ`. At current position S, `XAB` can match for length 3. At S+1, `ABCDEFG` can match for length 7. Assume the search reaches these candidates and the following position finds no improvement over that seven-byte match.

| Iteration begins at | Search result relevant to decision | Committed work |
| --- | --- | --- |
| S | Length 3; no previous pending decision | Defer the byte at S and advance one position |
| S+1 | Length 7 beats previous length 3 | Emit literal X from S; retain the seven-byte candidate |
| S+2 | No improvement over previous length 7 | Emit the match starting at S+1; advance to S+8 |

The remaining Q is then handled as a literal. The expansion is `X` + `ABCDEFG` + `Q`, the same nine input bytes. The alternative immediate three-byte match would have covered `XAB` and left the rest for subsequent decisions. Which alternative has fewer final bits depends on code and distance costs, not length alone.

At the table's third row, the current position is already S+2, but the match to commit begins at S+1. That is why pinned [`deflate_slow`, lines 2055–2056](https://github.com/madler/zlib/blob/757f0527154291bcf6bfbd6396ecde6bedd2db95/deflate.c#L2055-L2056) says:

```c
_tr_tally_dist(s, s->strstart - 1 - s->prev_match,
               s->prev_length - MIN_MATCH, bflush);
```

The first line computes distance from `strstart-1`, rather than `strstart`, to saved `prev_match`. The second passes the saved length minus the minimum match length 3 to symbol recording; `bflush` receives whether the record area needs flushing. This records a length/distance symbol, not its final Huffman bits. These lines execute only when the preceding branch conditions accept the previous match.

The state fields make this delay explicit: `match_available` records a deferred position; `prev_length` and `prev_match` keep the candidate from the previous start. Accepting that previous match consumes `prev_length-1` additional lookahead bytes, because one byte has already been stepped over. The insertion loop stops at `max_insert`, so it does not hash an incomplete three-byte string near the input tail.

Only after a branch commits a literal or match does the tally operation write its three-byte record and update code frequencies. This is the handoff to [Huffman construction](/sample/huffman-tree.html) and [block selection](/sample/blocks.html). Search may change which valid symbols are chosen; [its proof argument](/sample/match-proof.html) must explain why each chosen sequence still expands to the consumed bytes. The complete strategy, parameter and public-call composition remains **to confirm** beyond each explicitly scoped component result.
