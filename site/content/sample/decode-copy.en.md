With [tables installed](/sample/decode-tables.html), the decoder can interpret symbols. It has two execution routes: the ordinary dispatch handles small or interrupted work, while `inflate_fast` removes many repeated availability checks when sufficient margins already exist. Both must implement the same literal and match meanings.

Keep the familiar match: after output `AB`, length 6 and distance 2 produce `ABABAB`. This is a chosen symbol example, not a complete DEFLATE stream. It will explain overlap before we move to a wrapped window and a fast-path exit.

## Ordinary dispatch {#dispatch}

The slow path enters `LEN`, looks up the literal/length entry, follows a subtable if needed, and consumes the entry's code bits. A literal changes mode to `LIT`; an end marker changes to `TYPE`; an invalid entry selects `BAD`. A length base continues through `LENEXT`, distance lookup in `DIST`, extra distance bits in `DISTEXT`, then `MATCH`.

These modes store unfinished work explicitly. `LIT` checks output room before writing. `MATCH` limits each copy by remaining match length, available output room, and the contiguous portion of its source. An exhausted buffer can therefore leave a positive remaining length for the next call. Other states handle stored blocks, dynamic-table descriptions and wrapper fields.

The translated [`inflate_LEN`](/reference/source/ZlibF/Zlib/inflate.c.html#L734) also contains the fast branch. Default configuration does not mean every call takes it: buffer sizes, held bits and the current mode select the route at run time.

## Fast-path margins {#margins}

The main decoder selects `inflate_fast` in `LEN` when `have ≥ 6`, `left ≥ 258`, and `bits < 8`. It restores locals to the stream before calling and loads the returned state afterward. The helper derives:

```text
last = in  + (avail_in  - 5)
end  = out + (avail_out - 257)
beg  = out - (start - avail_out)
```

`beg` names the outer call's output start, even if that call produced bytes before entering this fast helper. The first body executes as a `do` loop, so entry margins must already hold. Later iterations use `in < last && out < end`.

A match writes at most 258 bytes. A complete length/distance token reads at most six input bytes. Summing individual refill maxima gives seven, but they cannot all occur together: earlier refills leave enough residual bits to prevent the last site from requiring its maximum. The [fast-decoder reference](/reference/docs/proof/inffast.html#bit-counts-and-the-six-byte-bound) develops that accounting.

## Sequential overlap {#overlap}

When the decoded distance is within the output already produced by the outer call, the source begins at `out - dist`. Each byte is read before the destination advances. A later step may therefore read a byte written by an earlier step of the same match.

<div class="zl-demo-mount"><zlib-demo kind="copy"><p>Starting from AB, a length-6 distance-2 match produces A, B, A, B, A, B. Newly written bytes become valid sources before the next copy step.</p></zlib-demo></div>

For distance two, the first two copies use the original A and B; the third reads the A just written by the first. Taking a snapshot of the original source interval would not express that behavior. Neither a disjoint `memcpy` nor a generic snapshot-style move is an adequate replacement for the repetition rule.

## Saved window and current output {#window}

Let `done = out - beg`. If `dist > done`, the missing history count is `op = dist - done`. The normal sane-distance check rejects `op > whave`; allocated window capacity alone is not evidence that those historical bytes exist.

Consider a teaching ring of size eight, full, with `wnext = 3`. Its physical cells contain `ABCDEFGH`, so chronological history is `DEFGHABC`. The current call has produced `DE`, and a match requests length six, distance six. Then `done = 2`, `op = 4`, and the first window index is:

```text
wsize + wnext - op = 8 + 3 - 4 = 7
```

Read `H` from cell 7, wrap, then read `ABC` from cells 0 through 2. Four bytes of window history are now exhausted. The remaining two match bytes come from this call's output: `DE`. The match contributes `HABCDE`, and the current output becomes `DEHABCDE`.

Eight cells illustrate ring arithmetic; they are not an admitted `windowBits` initialization size. The real cases are `wnext = 0`, `0 < wnext < op`, and `wnext ≥ op`. A partially filled ring additionally has `wnext = whave`; only valid retained history may be read. A preset dictionary can contribute history without becoming produced output.

## Unrolled execution {#unrolling}

The fast helper copies several bytes per loop body and handles a final one- or two-byte remainder. The direct-output `do` loop relies on the minimum match length of three. Window prefixes have separate positive counters. Their read/write order matters when the source overlaps the destination.

Table links likewise use backward jumps to `dolen` or `dodist`. Valid installed tables bound this linked lookup to one subtable level. Invalid length/distance symbols and unavailable history exit through error state; end-of-block exits through its prescribed mode. Fast means fewer repeated checks, not fewer error obligations.

## Byte backtracking and writeback {#writeback}

Before returning, the helper puts unused whole bytes back:

```text
whole = bits >> 3
in -= whole
bits -= whole << 3
hold &= (1U << bits) - 1
```

With 19 buffered bits, this returns two bytes and retains three. Entry with fewer than eight held bits ensures the returned bytes were pulled by this helper, rather than before its entry. The final epilogue updates exact cursors, availability counts, held bits and mode even on error exits.

This algorithm reading is **to confirm** through the execution argument. Small buffers must remain covered by slow dispatch, and fast-path premises must be derived at each actual call. The next chapter connects both routes to [one decoder argument](/sample/decode-proof.html). Full caller effects and defined error returns belong to the [`inflate` contract](/reference/functions/inflate.html), not to the happy-path animation.
