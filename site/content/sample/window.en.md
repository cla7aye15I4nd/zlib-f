On seeing `ABCD` a second time, a compressor can say “go back four bytes and copy four bytes” instead of writing those bytes again. Finding that reference requires remembering the first `ABCD`. The input can keep growing, but memory cannot grow with it. The compressor therefore keeps recent history and retires bytes that are too old to search.

Start with a teaching example that retains only the last eight bytes. After processing `0123ABCD`, all eight are in history. After another `ABCD`, the last eight are `ABCDABCD`. After another `wxyz`, they are `ABCDwxyz`. The second `ABCD` can refer to the first; once `0123` leaves the retained range, it cannot supply a new reference.

<div class="zl-demo-mount"><zlib-demo kind="window"><p>Process through byte 8, 12 and 16: the last eight bytes change from 0123ABCD to ABCDABCD to ABCDwxyz. The retained range advances while its capacity stays eight bytes.</p></zlib-demo></div>

Eight illustrates a logical retention limit. It is not a valid zlib window setting or a picture of its physical slide schedule. DEFLATE permits distances through 32768; this implementation reserves comparison room and uses a slightly smaller search limit. We will separate these layers below.

The window stage takes new caller bytes and the compressor's old state. It provides **searchable history, contiguous unprocessed bytes, and position indexes consistent with them**. It does not yet produce compression symbols. The next chapter's [candidate search](/sample/match-search.html) chooses literals or references; the [matching argument](/sample/match-proof.html) explains how the handoffs preserve byte meaning.

## From retained history to an actual array {#layout}

A simple implementation could delete the oldest byte and shift everything on each new byte. zlib avoids that repeated copying: it advances within a larger contiguous array, moving bytes in a batch only near the end. A byte therefore has a fixed logical stream position and an array index that changes after a move. The logical range of recent history is different from the entire physical allocation.

## Positions and retained bytes {#positions}

Now name the storage in that picture. `W = w_size` is the configured window scale; the ordinary `window` allocation actually holds `2W` bytes. It contains both history and unprocessed input. Allocating `2W` does not permit references back by `2W`. `strstart` is the array position being processed and `lookahead` counts real input bytes available from there. The valid data therefore ends at `strstart + lookahead`, which must not exceed `2W`.

```text
window offsets: 0                         strstart       strstart+lookahead        2W
                [ retained earlier bytes ][ unprocessed input ][ free space .......)
```

This is not a ring of byte cells addressed modulo W. Byte comparisons use contiguous positions in the `2W` array. The ring-like part appears later in the predecessor table. Once processing approaches the array's end, retained bytes move down and new input can occupy the freed region.

The constants explain how much room the implementation reserves. `MIN_MATCH` is 3, `MAX_MATCH` is 258 and `MIN_LOOKAHEAD = MAX_MATCH + MIN_MATCH + 1 = 262`. In this compressor, `MAX_DIST` is `W - 262`. With the usual W of 32768, that is 32506. This is an implementation search limit, not a redefinition of DEFLATE's format limit of distance 32768. Older bytes may still be physically present while already outside the permitted search range. Remaining in memory does not make them eligible reference sources.

Normalized window parameters give `512 ≤ W ≤ 32768` in the selected default build. For zlib-wrapped compression, accepted `windowBits = 8` is normalized to 9; raw and gzip validation reject that eight-bit case. W therefore does not become 256. The distinction matters: subtracting the 262-byte reserve from 256 would not give a usable positive distance bound. The exact accepted arguments are in [deflateInit2_](/reference/functions/deflateInit2_.html).

## Refill and lookahead {#refill}

When a strategy needs more input, `fill_window` computes free space beyond real data:

```text
more = window_size - lookahead - strstart
```

Here is the actual read from pinned [`fill_window`, lines 311–312](https://github.com/madler/zlib/blob/757f0527154291bcf6bfbd6396ecde6bedd2db95/deflate.c#L311-L312), rather than teaching pseudocode:

```c
n = read_buf(s->strm, s->window + s->strstart + s->lookahead, more);
s->lookahead += n;
```

The first line places the destination immediately after existing real data and gives `read_buf` the free-space count `more` as a read limit. The second adds only the count `n` actually read. Even when input runs short, the counter still describes real bytes.

After any necessary slide, `read_buf` copies at most `min(avail_in, more)` bytes into `window + strstart + lookahead`. It advances the caller's input pointer, reduces `avail_in`, updates input accounting and the selected wrapper checksum, and increases `lookahead` by the copied count. Accepting these bytes does not mean the match strategy has already consumed them into symbols.

The loop tries to obtain 262 bytes of lookahead, unless the caller has no more input available. At the strategy level, insufficient lookahead with `Z_NO_FLUSH` can cause `need_more` rather than forcing a decision on a short prefix. A finishing or flushing call can process the tail with less lookahead. Those internal states are not the public `deflate` return codes; [the call interface](/sample/interfaces.html) explains the enclosing protocol.

There is also an initialized tail beyond the real data. `high_water` records how far the window has been written. After refill, zlib zeroes up to `WIN_INIT = 258` bytes beyond the current data end, clipped to the allocation boundary, when that range has not already been initialized. This supports the comparison routine's wide scanning margin. Those zeros do not become input: `lookahead`, not `high_water`, limits how many real bytes a match may consume.

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

Connect the example to the implementation. These are four consecutive lines from pinned [`fill_window`, lines 287–290](https://github.com/madler/zlib/blob/757f0527154291bcf6bfbd6396ecde6bedd2db95/deflate.c#L287-L290):

```c
zmemcpy(s->window, s->window + wsize, (unsigned)wsize - more);
s->match_start -= wsize;
s->strstart    -= wsize; /* we now have strstart >= MAX_DIST */
s->block_start -= (long) wsize;
```

The first line moves the bytes: destination at the array base, source at W, and the example's count of 388. The second translates the saved match position; it does not certify that field as a usable candidate at this point. The third translates the current position. The fourth uses signed arithmetic for a block beginning that may precede the current array. Subsequent source limits postponed insertions, calls `slide_hash`, and adds W to the free-space count.

The same translation must reach the metadata. `slide_hash` turns each stored position m into `m-W` when `m ≥ W`, and into the zero sentinel otherwise. It updates both heads and predecessor entries. `block_start` is signed and may become negative: a block's original beginning can already have left the window. That is why [stored-block selection](/sample/blocks.html#selection) also checks whether a raw source pointer is available. An old `match_start` field can be stale; its unsigned subtraction must be analyzed at the point where that field is actually used, not treated as a permanently valid reference.

## Rolling hashes and predecessor slots {#hash}

Searching every earlier position would repeatedly compare many impossible candidates. zlib indexes three-byte strings by a short hash: it computes a small integer from the three bytes and uses it as a bucket number. Equal strings always enter the same bucket; different strings may share it too. A bucket therefore contains candidates to check, rather than already certified matches. With default `memLevel = 8`, `hash_bits = 15`, `hash_size = 32768`, `hash_mask = 32767`, and `hash_shift = 5`. The update is

```text
h := ((h << hash_shift) XOR next_byte) AND hash_mask
```

Starting from zero, the decimal byte values A=65, B=66, C=67 produce hash states 65, 2146, 3075. Adding D=68 to the last state produces 36, the same hash obtained by starting from zero on B,C,D. Three shifts discard the older contribution beyond the 15-bit mask. The recurrence therefore advances from one consecutive three-byte string to the next without recomputing its entire key.

`head[hash]` names the newest inserted position for that bucket. `prev[position & (W-1)]` stores its predecessor. To insert position p, the macro first saves the old head into that predecessor slot and returns it as `match_head`; it then publishes p as the new head. Searching starts at the **old** head, so inserting the current position does not produce a self-match.

This is not a search of the current position followed by self-rejection. The ordinary pinned [`INSERT_STRING` macro, lines 160–163](https://github.com/madler/zlib/blob/757f0527154291bcf6bfbd6396ecde6bedd2db95/deflate.c#L160-L163) preserves the order:

```c
#define INSERT_STRING(s, str, match_head) \
   (UPDATE_HASH(s, s->ins_h, s->window[(str) + (MIN_MATCH-1)]), \
    match_head = s->prev[(str) & s->w_mask] = s->head[s->ins_h], \
    s->head[s->ins_h] = (Pos)(str))
```

The first line names the macro and its three parameters. The second completes the hash update using the current string's third byte. The third stores the old bucket head in both the predecessor slot and the returned `match_head`. Only the fourth publishes the current position as the new head. The comma expression executes in that order. `FASTEST` has a separate branch without predecessor chains, so this argument does not cover all of that configuration.

The predecessor array has only W slots. Positions p and p+W reuse the same slot. This saves memory, but a slot can only be interpreted as p's recorded link while p remains in the relevant retained generation. Sliding by W preserves `p mod W`, allowing each retained link to keep its slot while its stored position value changes. Zero means `NIL`; position zero is not offered as an ordinary candidate in the source implementation.

The hash is a filter, not proof of equal contents. The next chapter follows [candidate search and lazy decisions](/sample/match-search.html), including what is checked before a reference becomes a symbol. The complete C-to-call composition remains **to confirm**; the [compression implementation argument](/reference/docs/proof/deflate.html#d-window-bounds-and-fill_window) records its exact obligations.
