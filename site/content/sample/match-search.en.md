[The window and candidate index](/sample/window.html) retain possible sources and link positions with the same three-byte hash. That is not yet enough to emit a reference: hash collisions can name unequal content, and a nearer source need not match for longer. Suppose the processed prefix is `ABCQABCR` and the next input is `ABCQABCX`. Two sources begin with `ABC`; comparison must continue to determine how much current input each can replace.

Search reads the window's contiguous bytes, the current start and the candidate chain, then returns a possible match to the strategy. The strategy still decides whether to accept it, wait one byte or commit a literal. Only a committed choice becomes a [record consumed by block encoding](/sample/blocks.html#symbols). We compare the two sources first, then examine the optimizations that reduce search work and the reason a decision may be delayed.

## Compare two candidates first {#example}

The recent `ABCR` agrees with current `ABCQABCX` for three bytes, then differs at R versus Q. It offers length 3 at distance 4. The older `ABCQ` agrees for seven bytes, then differs at R versus X. It offers length 7 at distance 8. There are no space bytes here: the two history fragments are adjacent and immediately followed by the current input.

The seven-byte comparison passes the end of the earliest four-character fragment and continues into the following `ABC`. A candidate is the start of contiguous bytes in one window array, not a separately stored word.

<div class="zl-demo-mount"><zlib-demo kind="search"><p>In a schematic history, the newest candidate matches ABC for length 3. Following one predecessor reaches a candidate matching ABCQABC for length 7. A one-candidate budget stops before that second candidate.</p></zlib-demo></div>

The scene labels logical positions 0, 4 and 8. Actual zlib reserves position zero for `NIL`; shifting all these positions by one preserves the example's comparisons and distances without using that sentinel as a candidate. The scene illustrates the effect of the candidate budget, not the exact hash-table contents produced by every real call.

## Candidates and distance limits {#candidates}

A candidate is an earlier **byte position**, not a copied string. To find candidates cheaply, the compressor groups three-byte prefixes by a hash value. A bucket head names the newest position in that group; predecessor links lead to older positions. The insertion operation `INSERT_STRING` puts the current position into this index and returns the **old** bucket head. The strategy calls that returned position `hash_head`. Starting from it avoids matching the current position against itself.

There is also a limit on how far back search may look. The current byte's array index is `strstart`; the configured window scale, in bytes, is `W` (`w_size` in C). This compressor reserves 262 bytes of margin for its input and comparison machinery. Its maximum search distance, `MAX_DIST`, is therefore `W - 262` bytes. With the usual `W=32768`, this limit is 32506 bytes. This is an implementation search limit; DEFLATE itself permits distances through 32768. The [window chapter](/sample/window.html#positions) derives the margin and array layout.

Before calling the comparison routine `longest_match`, the strategy checks that a nonzero `hash_head` precedes `strstart` and that `strstart - hash_head` does not exceed `MAX_DIST`. Zero means `NIL`, or no candidate.

The oldest position allowed by that distance is stored as `limit = max(strstart - MAX_DIST, 0)`. For example, current index 1000 and maximum distance 250 give limit 750: candidate 900 is close enough, while 700 is too old. The zero clamp handles a current index smaller than the maximum distance.

Read that bound together with the source’s loop order. The first candidate enters the `do` body before the continuation test. Only at the end does the loop take another predecessor and test it. An initial candidate of 750 may therefore be compared, whereas a later predecessor of 750 fails the strict condition “next position greater than 750” and stops the loop. Covering the entry check and the successor check separately preserves the source’s actual boundary behavior.

## From a byte scan to quick rejection {#comparison}

The direct method compares from the candidate's beginning until the first mismatch, giving lengths 3 and 7 above. Repeating that scan for every candidate would repeatedly read many shared short prefixes. zlib first asks a cheaper question: “could this candidate beat the length already found?” Only a possible improvement warrants a full scan.

The caller supplies a length to beat, measured in bytes, in `prev_length`. The search keeps its current best length in `best_len`, initially setting `best_len = prev_length`. For a baseline of 3, a useful improvement must agree for at least 4 bytes. If a candidate cannot improve that baseline, a full scan would be wasted work. In the ordinary byte-comparison branch, the routine first compares bytes at offsets `best_len` and `best_len-1`, then the first two bytes. A mismatch at any of these positions rejects the candidate immediately.

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

The seven-byte match above is only found if search reaches the older candidate. Stopping after the first candidate still gives a correct three-byte reference, but may miss better compression. Configuration therefore controls two costs: how many candidates to compare, and what match length is worth more search time.

| Decision to make | Source setting | Unit and effect |
| --- | --- | --- |
| How many candidates to visit | Chain budget | Candidate visits; stop when exhausted |
| What length is satisfactory | `nice_match` | Bytes; reaching it can stop search early |
| When an existing result deserves less search | `good_match` | Bytes; reaching it quarters the visit budget |
| Whether to search the next position or insert intervening positions | Lazy/insertion setting | A byte-length threshold whose role depends on the engine |

These settings control time spent searching. The format still permits the same legal lengths and distances. Below, separate the fast engine `deflate_fast`, which commits immediately, from `deflate_slow`, which also examines the next input position.

For example, level 6 can visit up to 128 candidates and can stop on a 128-byte match. If the previous match already reaches 8 bytes, it cuts the visit budget from 128 to 32 candidates. Some representative settings are:

| Level | Engine | Good length | Lazy/insertion setting | Nice length | Chain budget |
| --- | --- | --- | --- | --- | --- |
| 1 | fast | 4, ignored by fast search | 4 | 8 | 4 |
| 6 | slow | 8 | 16 | 128 | 128 |
| 9 | slow | 32 | 258 | 258 | 4096 |

In the ordinary `longest_match`, an already good previous length reduces the chain budget by a factor of four. Reaching `nice_match` stops the search early. The budget can stop before all retained candidates are visited, and the nice threshold can stop before the longest possible candidate is found. Consequently the function name does not promise the globally longest match in the entire window.

The fast strategy commits a useful current match immediately. For sufficiently short matches it inserts the intervening strings into the hash table; for long matches it can skip those insertions and restart the running hash near the new position. This saves work at the cost of fewer future candidates. In levels 1–3, the shared configuration field has this insertion-limit role rather than the slow engine's lazy-search role.

The slow strategy uses the field as `max_lazy_match`, a byte-length threshold: it may skip another search when the previous match is already long enough. `Z_FILTERED` also rejects some short matches; an ordinary distant length-three match can be rejected by the `TOO_FAR` heuristic. `Z_HUFFMAN_ONLY` bypasses match search, and `Z_RLE` looks for distance-one runs. These are choices among valid encodings, not separate decompression formats. [deflateTune](/reference/functions/deflateTune.html) exposes search parameters, so an argument covering its full domain cannot silently assume only table defaults.

## Lazy decisions and symbol commitment {#lazy}

So far, search has compared candidates for one input start. The slow strategy also compares two adjacent starts: would taking a short match now block a longer match at the next byte? Use a second example to see why finding a match is not the same as committing it. Suppose earlier history contains `XABZ` and `ABCDEFGH`, and the current input is `XABCDEFGQ`. Call the current byte position S; S+1 is the next byte. At S, `XAB` can match for length 3. At S+1, `ABCDEFG` can match for length 7. Assume the search reaches these candidates and the following position finds no improvement over that seven-byte match.

| Iteration begins at | Search result relevant to decision | Committed work |
| --- | --- | --- |
| S | Length 3; no previous pending decision | Defer the byte at S and advance one position |
| S+1 | Length 7 beats previous length 3 | Emit literal X from S; retain the seven-byte candidate |
| S+2 | No improvement over previous length 7 | Emit the match starting at S+1; advance to S+8 |

The remaining Q is then handled as a literal. The expansion is `X` + `ABCDEFG` + `Q`, the same nine input bytes. The alternative immediate three-byte match would have covered `XAB` and left the rest for subsequent decisions. Which alternative has fewer final bits depends on code and distance costs, not length alone.

At the table's third row, the current position is already S+2, but the match to commit begins at S+1. Before reading the tally call, name its saved values: `prev_match` is the earlier source index for the deferred match, `prev_length` is its byte length, and `MIN_MATCH=3` is the shortest match the format can encode. `s` points to the compressor state; `bflush` receives a yes/no result indicating that the symbol record area needs flushing. That is why pinned [`deflate_slow`, lines 2055–2056](https://github.com/madler/zlib/blob/757f0527154291bcf6bfbd6396ecde6bedd2db95/deflate.c#L2055-L2056) says:

```c
_tr_tally_dist(s, s->strstart - 1 - s->prev_match,
               s->prev_length - MIN_MATCH, bflush);
```

The first line computes distance from `strstart-1`, rather than `strstart`, to saved `prev_match`. The second passes the saved length minus the minimum match length 3 to symbol recording; `bflush` receives whether the record area needs flushing. This records a length/distance symbol, not its final Huffman bits. These lines execute only when the preceding branch conditions accept the previous match.

The state fields make this delay explicit: `match_available` records a deferred position; `prev_length` and `prev_match` keep the candidate from the previous start. Accepting that previous match consumes `prev_length-1` additional lookahead bytes, because one byte has already been stepped over. The insertion loop stops at `max_insert`, the last array start with three real bytes available. It therefore does not hash an incomplete three-byte string near the input tail.

Committing a choice connects search to encoding. Three record bytes save the literal or match for ordered block emission, while frequency tables count its codes. Length 6/distance 2 contributes one length-code occurrence and one distance-code occurrence, rather than six literals. [Huffman construction](/sample/huffman-tree.html) uses those counts; [block encoding](/sample/blocks.html#symbols) follows the saved records into fields.

To check why reduced search work still preserves content, [references and input agreement](/sample/match-proof.html) returns to these candidates and deferred choices. The complete strategy-to-public-call proof is unfinished. It must cover admitted tuning values and connect every search result, deferred starting position and committed record to the same input.
