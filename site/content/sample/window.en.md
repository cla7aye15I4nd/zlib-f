A compressor looks for content that has appeared before and describes a repeated passage with a reference. Start with the complete input, `0123ABCDABCDwxyz`: it contains two consecutive copies of `ABCD`. Suppose the compressor has processed `0123ABCD` and is about to process the second `ABCD`.

Going **back 4 bytes from the current position** reaches the start of the first `ABCD`. This repetition can therefore be described by “distance 4, length 4.” The compressor records those two quantities. When the decoder reads them, it goes back 4 bytes in the recovered output and copies 4 bytes in order to recover the second `ABCD`. The two blue groups in the figure contain the same bytes; the connecting arrow identifies the source of the reference.

Finding such repetitions requires keeping bytes that have already been processed. Input can keep growing, but history cannot accumulate forever. **A sliding window keeps only recent history available for later matches.** The illustration below uses a retention limit of 8 bytes. First locate the two groups of `ABCD`, then inspect the reference, then advance the processing position.

<div class="zl-demo-mount" id="window-example"><zlib-demo kind="window"><p>The complete input is 0123ABCDABCDwxyz. The prefix 0123ABCD has been processed; the current position is just before the second ABCD. Going back 4 bytes reaches the first ABCD; the copy length is 4. After this match, the last 8 processed bytes are ABCDABCD. After wxyz, they are ABCDwxyz.</p></zlib-demo></div>

After accepting the match, the processed prefix is `0123ABCDABCD`. Its last 8 bytes are `ABCDABCD`, so the old `0123` leaves the retained range. After processing `wxyz`, the window retains `ABCDwxyz`. The processing position advances while retained capacity stays at 8 bytes. Bytes outside that range no longer participate in later matches.

Eight illustrates a logical retention limit. It is not a valid zlib window setting or a picture of its physical slide schedule. DEFLATE permits distances through 32768; this implementation reserves comparison room and uses a slightly smaller search limit. We will separate these layers below.

The window stage takes new caller bytes and the compressor's old state. It provides **searchable history, contiguous unprocessed bytes, and position indexes consistent with them**. It does not yet produce compression symbols. The next chapter's [candidate search](/sample/match-search.html) chooses literals or references; the [matching argument](/sample/match-proof.html) explains how the handoffs preserve byte meaning.

## From retained history to an actual array {#layout}

A simple implementation could delete the oldest byte and shift everything on each new byte. zlib avoids that repeated copying: it advances within a larger contiguous array, moving bytes in a batch only near the end. A byte therefore has a fixed logical stream position and an array index that changes after a move. The logical range of recent history is different from the entire physical allocation.

## Positions and retained bytes {#positions}

First distinguish two kinds of position. A **stream position** identifies a byte in the whole input and never changes. An **array index** identifies the memory cell that currently holds it and changes when bytes move. The quantities below describe array storage and are measured in bytes.

The implementation holds two sets of bytes together: processed history available for matching, and input already read but not yet processed. Write `W` for the configured window scale, the C field `w_size`. The ordinary layout allocates a contiguous array `window` of `2W` bytes, with its capacity recorded in `window_size`. With `W = 512`, it has 1024 cells. Allocated capacity and permitted backward distance are separate limits.

The field `strstart` is the array index of the next byte to process. The field `lookahead` counts real input bytes already read from that point but not yet processed. For example, `strstart = 800` and `lookahead = 100` put unprocessed input in `[800, 900)`: index 800 is included and 900 is excluded. Real data ends at 900.

```text
array index: 0                  strstart              strstart + lookahead       2W
             [ earlier bytes ...][ read, unprocessed input ][ free space ........)
                                  ← lookahead bytes →
```

Not all earlier bytes in this picture remain eligible for matching; the next section defines the maximum distance. First consider storage: zlib compares bytes directly along this contiguous array. Reading onward from one index compares a whole passage without taking every byte address modulo W. Near the end, it moves retained data to lower indexes in a batch and makes room for new input at the tail. The predecessor table introduced later reuses slots cyclically; that is a different array.

### Match length, lookahead, and search distance {#search-limits}

A reference answers two questions: **how many bytes can be copied, and how far back does their source begin?** Both happen to be 4 in the opening `ABCD` example, but they measure different things. Length tells how much input this reference replaces. Distance identifies where its source begins in history.

A DEFLATE match represents a copy of 3 through 258 bytes. One or two equal bytes are insufficient for this kind of match; a longer repetition needs multiple symbols. The source names these length endpoints `MIN_MATCH = 3` and `MAX_MATCH = 258`. Both count input bytes.

The compressor also wants to see enough upcoming input before choosing a match. Reading only `AB` in this batch does not establish that the complete `ABCD` match is absent. During ordinary refill, zlib tries to prepare **262 bytes of lookahead**. The source names that target `MIN_LOOKAHEAD` and defines it as `MAX_MATCH + MIN_MATCH + 1`. Beyond the 258-byte maximum match, it reserves room for operations such as hashing a following three-byte string. This is the implementation's lookahead target. Input tails and flushes can be handled with fewer than 262 bytes.

This reserve explains the implementation's distance limit. Instead of using all of `W` as its maximum backward distance, zlib takes **the window scale minus the lookahead target**. The source calls this limit `MAX_DIST(s)`, where `s` is the compressor state. Its value is `s->w_size - MIN_LOOKAHEAD`, abbreviated here as `W - 262`. Ordinary match search excludes candidates farther back than that.

| Quantity needed by the reader | Source name | Value or relationship, in bytes |
| --- | --- | --- |
| Minimum length of one match | `MIN_MATCH` | 3 |
| Maximum length of one match | `MAX_MATCH` | 258 |
| Usual target for input prepared ahead | `MIN_LOOKAHEAD` | 262 |
| Farthest history distance searched by this implementation | `MAX_DIST(s)` | `W - 262` |

The usual `W = 32768` gives a search limit of `32768 - 262 = 32506` bytes. DEFLATE itself still permits distance 32768. This calculation describes **how far this compressor chooses to search**. Older bytes may remain physically stored without becoming eligible candidates. That is the difference between the stored range and the search range.

### Window parameters and byte counts {#window-settings}

The API parameter `windowBits` expresses the scale as an exponent: after normalization to b, `W = 2^b` bytes. An exponent of 9 means 512 bytes; 15 means 32768 bytes. Raw and gzip arguments also use a sign or an added value to select the wrapper. Initialization handles those choices before obtaining the exponent. [deflateInit2_](/reference/functions/deflateInit2_.html) gives the full argument rules.

In the selected default build, the actual range is `512 ≤ W ≤ 32768`. For zlib-wrapped compression, an accepted exponent of 8 is changed to 9. Raw and gzip reject the exponent-8 case, so this layout does not obtain a 256-byte window. The smallest actual scale, 512, still leaves `512 - 262 = 250` bytes of search distance. Substituting 256 into the same formula would leave no positive search allowance.

## Refill and lookahead {#refill}

When lookahead runs low, the refill function `fill_window` first counts free cells between the end of real data and the end of the array. It calls this free-byte count `more`. The total capacity `window_size` is `2W` in the ordinary layout:

```text
more = window_size - lookahead - strstart
```

In the C below, `s` points to the compressor state and `s->strm` to the caller’s public stream structure. The helper `read_buf` reads from that stream and returns the number of bytes actually copied, `n`. This is the actual read from pinned [`fill_window`, lines 311–312](https://github.com/madler/zlib/blob/757f0527154291bcf6bfbd6396ecde6bedd2db95/deflate.c#L311-L312), rather than teaching pseudocode:

```c
n = read_buf(s->strm, s->window + s->strstart + s->lookahead, more);
s->lookahead += n;
```

The first line places the destination immediately after existing real data and gives `read_buf` the free-space count `more` as a read limit. The second adds only the count `n` actually read. Even when input runs short, the counter still describes real bytes.

The public field `avail_in` counts the readable input bytes the caller still supplies in this call. After any necessary slide, `read_buf` copies at most `min(avail_in, more)` bytes into `window + strstart + lookahead`. It advances the caller's input pointer, reduces `avail_in`, updates input accounting and the selected wrapper checksum, and increases `lookahead` by the copied count. Accepting these bytes does not mean the match strategy has already consumed them into symbols.

The loop tries to obtain 262 bytes of lookahead, unless the caller has no more input available. At the strategy level, insufficient lookahead with `Z_NO_FLUSH` can cause `need_more` rather than forcing a decision on a short prefix. A finishing or flushing call can process the tail with less lookahead. Those internal states are not the public `deflate` return codes; [the call interface](/sample/interfaces.html) explains the enclosing protocol.

Optimized comparisons sometimes scan beyond the end of real input. A short initialized tail makes those reads avoid uninitialized contents. The field `high_water` is the exclusive end of the initialized prefix: every byte in `[0, high_water)` has been written. After refill, zlib zeroes as much of the next 258 bytes as necessary, stopping at the allocation boundary. The source names this padding count `WIN_INIT = MAX_MATCH = 258`. Zeroing makes memory readable; it does not add real input. The count `lookahead` still bounds how many bytes a match can consume.

Refill also completes postponed hash insertions. If the last call ended with only one or two remaining bytes, those positions did not yet have a complete three-byte string to insert. The `insert` count remembers this work. Once more bytes arrive, `fill_window` seeds the running hash and inserts the now-complete strings before ordinary searching continues.

## Sliding with concrete offsets {#sliding}

The slide test is `strstart ≥ W + MAX_DIST`, or `strstart ≥ 2W - 262`. Consider the permitted W of 512, with `strstart = 800` and `lookahead = 100`. Real data ends at 900, leaving `more = 1024 - 900 = 124` bytes. The threshold is 762, so the slide runs.

It copies `W - more = 388` bytes, from `[512, 900)` into `[0, 388)`. This is the valid part of the upper half, not an unconditional copy of all 512 bytes. The source and destination ranges do not overlap. `strstart` decreases by 512 to 288; `lookahead` stays 100. Free room increases to 636 bytes. If 300 new bytes are available, the next read places them at `[388, 688)`, raising lookahead to 400.

| Quantity | Before slide | After slide | After reading 300 bytes |
| --- | --- | --- | --- |
| `strstart` | 800 | 288 | 288 |
| `lookahead` | 100 | 100 | 400 |
| End of real data | 900 | 388 | 688 |
| Free room | 124 | 636 | 336 |

A retained candidate at old position 700 becomes 188. Its distance from the current position remains `800 - 700 = 288 - 188 = 100`. At the logical level, the base represented by window offset 0 has advanced by 512, so both pairs still name the same stream bytes.

The move must also update saved positions: `match_start` holds a match’s starting index, and `block_start` holds the original input start of the current compressed block. The local variable `wsize` is W; `zmemcpy` is the byte-copy helper macro. Connect the example to these four consecutive lines from pinned [`fill_window`, lines 287–290](https://github.com/madler/zlib/blob/757f0527154291bcf6bfbd6396ecde6bedd2db95/deflate.c#L287-L290):

```c
zmemcpy(s->window, s->window + wsize, (unsigned)wsize - more);
s->match_start -= wsize;
s->strstart    -= wsize; /* we now have strstart >= MAX_DIST */
s->block_start -= (long) wsize;
```

The first line moves the bytes: destination at the array base, source at W, and the example's count of 388. The second translates the saved match position; it does not certify that field as a usable candidate at this point. The third translates the current position. The fourth uses signed arithmetic for a block beginning that may precede the current array. Subsequent source limits postponed insertions, calls `slide_hash`, and adds W to the free-space count.

The same translation must reach the metadata. `slide_hash` turns each stored position m into `m-W` when `m ≥ W`, and into the zero sentinel otherwise. It updates both heads and predecessor entries. `block_start` is signed and may become negative: a block's original beginning can already have left the window. That is why [stored-block selection](/sample/blocks.html#selection) also checks whether a raw source pointer is available. An old `match_start` field can be stale; its unsigned subtraction must be analyzed at the point where that field is actually used, not treated as a permanently valid reference.

## Rolling hashes and predecessor slots {#hash}

Searching every earlier position compares many passages that cannot match. zlib first computes a small integer, a **hash**, for each three-byte string and groups its positions into a bucket with that number. Searching for `ABC` visits only positions in its bucket. Equal strings always share a bucket; different strings may share it too. Hashing narrows the candidates, and actual byte comparisons still follow.

More buckets usually separate unrelated candidates better, at the cost of more index memory. The initialization parameter `memLevel` controls this memory configuration. Its default value, 8, gives 32768 buckets. Several source fields describe that one index:

| Field | Role | Meaning of its default value |
| --- | --- | --- |
| `hash_size` | Number of buckets | 32768 buckets |
| `hash_bits` | Bits needed to express a bucket number | 15 bits, since `2^15 = 32768` |
| `hash_mask` | Keep only low bits within the bucket range | 32767, with all low 15 bits set |
| `hash_shift` | Bits to shift the running hash left per new byte | 5 bits |

To advance from `ABC` to `BCD` without recomputing all bytes, zlib updates a running hash. Write `h` for that current integer and `next_byte` for the numeric value of the next byte. Here `<<` shifts left, `XOR` combines bits by exclusive-or, and `AND` with the mask keeps only the low 15 bits:

```text
h := ((h << hash_shift) XOR next_byte) AND hash_mask
```

Starting from zero, the decimal byte values A=65, B=66, C=67 produce hash states 65, 2146, 3075. Adding D=68 to the last state produces 36, the same hash obtained by starting from zero on B,C,D. Three shifts discard the older contribution beyond the 15-bit mask. The recurrence therefore advances from one consecutive three-byte string to the next without recomputing its entire key.

A bucket usually contains several positions. zlib links them from newest to oldest: the head table `head` records each bucket’s newest position, while the predecessor table `prev` links a position to the previous insertion in that bucket. A predecessor is an older candidate with the same hash, not necessarily the immediately preceding input byte.

Let `hash` be the bucket number and p the position being inserted. The old head is `head[hash]`; p’s predecessor goes in `prev[p & (W-1)]`. Since W is a power of two, `& (W-1)` is equivalent to taking the remainder modulo W and selects one of W slots. For example, if bucket 3075 points to position 60, inserting position 100 gives `prev[100] = 60` and `head[3075] = 100`. This search starts at the old head, 60, rather than the newly inserted 100. The code returns that old head as `match_head`.

The following macro implements that order. Its parameter `s` points to the state, `str` is the insertion position, and `match_head` receives the old head. The state field `ins_h` stores the running hash, and `w_mask` equals `W-1`. The helper `UPDATE_HASH` performs the recurrence above; `Pos` is the integer type used to save positions. The ordinary pinned [`INSERT_STRING` macro, lines 160–163](https://github.com/madler/zlib/blob/757f0527154291bcf6bfbd6396ecde6bedd2db95/deflate.c#L160-L163) preserves the order:

```c
#define INSERT_STRING(s, str, match_head) \
   (UPDATE_HASH(s, s->ins_h, s->window[(str) + (MIN_MATCH-1)]), \
    match_head = s->prev[(str) & s->w_mask] = s->head[s->ins_h], \
    s->head[s->ins_h] = (Pos)(str))
```

The first line names the macro and its three parameters. The second completes the hash update using the current string's third byte. The third stores the old bucket head in both the predecessor slot and the returned `match_head`. Only the fourth publishes the current position as the new head. The comma expression executes in that order. The simplified implementation enabled by the build option `FASTEST` has a separate branch without predecessor chains, so this argument does not cover all of that configuration.

The predecessor array has only W slots. Positions p and p+W reuse the same slot. For W=512, positions 100 and 612 both use slot 100. Inserting 612 overwrites the link once saved for 100. Those positions are now 512 bytes apart, beyond this configuration’s 250-byte search limit, so the old position is no longer eligible as a new match source.

This saves memory, but the argument must remember which insertion owns a slot. Its value can be interpreted as p’s recorded predecessor only while a later position has not reused that slot. Sliding by W preserves `p mod W`, allowing each retained link to keep its slot while its stored position value changes. Zero means `NIL`; position zero is not offered as an ordinary candidate in the source implementation.

The hash groups candidate positions; [candidate search and lazy decisions](/sample/match-search.html) follows the actual byte comparisons. The window composition proof for all public calls is unfinished. It must connect initialization, refill, sliding and index preservation along one call history. The [compression implementation argument](/reference/docs/proof/deflate.html#d-window-bounds-and-fill_window) gives those obligations.
