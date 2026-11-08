Before a compressor can replace bytes with a reference, it needs a place to keep both the bytes already processed and the bytes it is about to inspect. This chapter follows that storage. The next chapter will search it for a match; the [matching argument](/sample/match-proof.html) will then explain which relationships a proof must preserve.

A single position has two identities. It names a byte in the logical input stream, but the implementation also represents it as an index in a finite array. Sliding the array changes the second identity without changing the first. Understanding that distinction makes the window, the hash chains and their updates one mechanism.

## Positions and retained bytes {#positions}

Let `W = w_size`. In the ordinary layout, `window` has `2W` bytes. `strstart` is the array position being processed and `lookahead` counts real input bytes available from there. The valid data therefore ends at `strstart + lookahead`, which must not exceed `2W`.

```text
window offsets: 0                         strstart       strstart+lookahead        2W
                [ retained earlier bytes ][ unprocessed input ][ free space .......)
```

This is not a ring of byte cells addressed modulo W. Byte comparisons use contiguous positions in the `2W` array. The ring-like part appears later in the predecessor table. Once processing approaches the array's end, retained bytes move down and new input can occupy the freed region.

The constants explain how much room the implementation reserves. `MIN_MATCH` is 3, `MAX_MATCH` is 258 and `MIN_LOOKAHEAD = MAX_MATCH + MIN_MATCH + 1 = 262`. In this compressor, `MAX_DIST` is `W - 262`. With the usual W of 32768, that is 32506. This is an implementation search limit, not a redefinition of DEFLATE's format limit of distance 32768.

Normalized window parameters give `512 ≤ W ≤ 32768` in the selected default build. For zlib-wrapped compression, accepted `windowBits = 8` is normalized to 9; raw and gzip validation reject that eight-bit case. W therefore does not become 256. The distinction matters: subtracting the 262-byte reserve from 256 would not give a usable positive distance bound. The exact accepted arguments are in [deflateInit2_](/reference/functions/deflateInit2_.html).

## Refill and lookahead {#refill}

When a strategy needs more input, `fill_window` computes free space beyond real data:

```text
more = window_size - lookahead - strstart
```

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

The same translation must reach the metadata. `slide_hash` turns each stored position m into `m-W` when `m ≥ W`, and into the zero sentinel otherwise. It updates both heads and predecessor entries. `block_start` is signed and may become negative: a block's original beginning can already have left the window. That is why [stored-block selection](/sample/blocks.html#selection) also checks whether a raw source pointer is available. An old `match_start` field can be stale; its unsigned subtraction must be analyzed at the point where that field is actually used, not treated as a permanently valid reference.

## Rolling hashes and predecessor slots {#hash}

Searching every earlier position would repeatedly compare many impossible candidates. zlib indexes three-byte strings by a short hash. With default `memLevel = 8`, `hash_bits = 15`, `hash_size = 32768`, `hash_mask = 32767`, and `hash_shift = 5`. The update is

```text
h := ((h << hash_shift) XOR next_byte) AND hash_mask
```

Starting from zero, the decimal byte values A=65, B=66, C=67 produce hash states 65, 2146, 3075. Adding D=68 to the last state produces 36, the same hash obtained by starting from zero on B,C,D. Three shifts discard the older contribution beyond the 15-bit mask. The recurrence therefore advances from one consecutive three-byte string to the next without recomputing its entire key.

`head[hash]` names the newest inserted position for that bucket. `prev[position & (W-1)]` stores its predecessor. To insert position p, the macro first saves the old head into that predecessor slot and returns it as `match_head`; it then publishes p as the new head. Searching starts at the **old** head, so inserting the current position does not produce a self-match.

The predecessor array has only W slots. Positions p and p+W reuse the same slot. This saves memory, but a slot can only be interpreted as p's recorded link while p remains in the relevant retained generation. Sliding by W preserves `p mod W`, allowing each retained link to keep its slot while its stored position value changes. Zero means `NIL`; position zero is not offered as an ordinary candidate in the source implementation.

The hash is a filter, not proof of equal contents. The next chapter follows [candidate search and lazy decisions](/sample/match-search.html), including what is checked before a reference becomes a symbol. The complete C-to-call composition remains **to confirm**; the [compression implementation argument](/reference/docs/proof/deflate.html#d-window-bounds-and-fill_window) records its exact obligations.
