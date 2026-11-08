After [table lookup](/sample/decode-tables.html), the decoder has either a byte to output directly, an end marker, or a **match**: “copy this many bytes from this far back.” Its task is to turn that instruction into bytes while preserving the same meaning when input or output space runs out.

The inputs are decoded instructions, readable past bytes and the caller's writable output range. The result is an extended output and, if space runs out, saved work for the next call. A request for history that does not exist must take the appropriate error path. First follow a six-byte match; afterward we can see why zlib has an ordinary route and a faster route for the same operation.

## Sequential overlap {#overlap}

Start with output `AB`. A length-six, distance-two match asks for six more bytes, each copied from two positions behind its destination. The match appends `ABABAB`, making the full output `ABABABAB`.

| Step | Destination index | Source index | Byte read | Output after writing |
| --- | --- | --- | --- | --- |
| 1 | 2 | 0 | A | `ABA` |
| 2 | 3 | 1 | B | `ABAB` |
| 3 | 4 | 2 | A written at step 1 | `ABABA` |
| 4 | 5 | 3 | B written at step 2 | `ABABAB` |
| 5 | 6 | 4 | A written at step 3 | `ABABABA` |
| 6 | 7 | 5 | B written at step 4 | `ABABABAB` |

This is a teaching instruction, not a complete DEFLATE stream. The source is read one byte at a time, so later steps can read bytes written by this very match. In C, `out` points to the next destination, `dist` is the distance, and `from` is the source starting at `out - dist`.

<div class="zl-demo-mount"><zlib-demo kind="copy"><p>Starting from AB, a length-6 distance-2 match produces A, B, A, B, A, B. Newly written bytes become valid sources before the next copy step.</p></zlib-demo></div>

For distance two, the first two copies use the original A and B; the third reads the A just written by the first. Taking a snapshot of the original source interval would not express that behavior. Neither a disjoint `memcpy` nor a generic snapshot-style move is an adequate replacement for the repetition rule.

The actual direct-output branch of `inflate_fast` is in [pinned `inffast.c`, lines 250–256](https://github.com/madler/zlib/blob/757f0527154291bcf6bfbd6396ecde6bedd2db95/inffast.c#L250-L256):

```c
from = out - dist;
do {
    *out++ = *from++;
    *out++ = *from++;
    *out++ = *from++;
    len -= 3;
} while (len > 2);
```

`len` is the remaining match length. For our example, the first body performs steps 1–3 and changes it from six to three; the second performs steps 4–6 and changes it to zero. Crucially, the third assignment already reads the first assignment's A. The real loop is unrolled into three assignments, but their order preserves the byte-by-byte rule.

## Ordinary dispatch {#dispatch}

The ordinary decoder remembers its current job in a mode field. A mode is a place to resume, rather than an output byte. The slow path enters `LEN` (read a literal or length), looks up the literal/length entry, follows a subtable if needed, and consumes the entry's code bits. A literal changes mode to `LIT` (write that byte); an end marker changes to `TYPE` (read the next block type); an invalid entry selects `BAD` (report bad data). A length base continues through `LENEXT` to add any extra length bits, `DIST` to look up distance, `DISTEXT` to add extra distance bits, then `MATCH` to copy. A base is the fixed part from the table; extra bits select the value within that base’s range.

These modes store unfinished work explicitly. `LIT` checks output room before writing. `MATCH` limits each copy by remaining match length, available output room, and the contiguous portion of its source. For example, with only two output slots, our match writes `AB` and saves four remaining bytes. A later call resumes that match rather than decoding the instruction again. An exhausted buffer can therefore leave a positive remaining length for the next call. Other states handle stored blocks, dynamic-table descriptions and wrapper fields.

The translated [`inflate_LEN`](/reference/source/ZlibF/Zlib/inflate.c.html#L734) also contains the fast branch. Default configuration does not mean every call takes it: buffer sizes, held bits and the current mode select the route at run time.

## Saved window and current output {#window}

A match may reach farther back than the bytes written in this call. zlib then uses a saved **window**, a ring buffer retaining recent history. Its size is `wsize`; `whave` counts valid historical bytes, and `wnext` names the next slot to overwrite. Capacity and valid history are different quantities.

Here `beg` points to the outer call's output start. Let `done = out - beg` be this call's produced-byte count. If `dist > done`, the missing history count is `op = dist - done`; here `op` is a temporary count, rather than a table-entry operation. The normal strict-distance check (`sane`) rejects `op > whave`. Merely allocating a window cannot provide missing history.

Consider a teaching ring of size eight, full, with `wnext = 3`. Its physical cells contain `ABCDEFGH`, so chronological history is `DEFGHABC`. The current call has produced `DE`, and a match requests length six, distance six. Then `done = 2`, `op = 4`, and the first window index is:

```text
wsize + wnext - op = 8 + 3 - 4 = 7
```

Read `H` from cell 7, wrap, then read `ABC` from cells 0 through 2. Four bytes of window history are now exhausted. The remaining two match bytes come from this call's output: `DE`. The match contributes `HABCDE`, and the current output becomes `DEHABCDE`.

Eight cells illustrate ring arithmetic; they are not an admitted `windowBits` initialization size. The real cases are `wnext = 0`, `0 < wnext < op`, and `wnext ≥ op`. A partially filled ring additionally has `wnext = whave`; only valid retained history may be read. A preset dictionary can contribute history without becoming produced output.

## Fast-path margins {#margins}

The fast route checks enough room for an entire next instruction, then avoids repeating the same space checks at each small step. Here `have` counts unread offered bytes, `left` counts writable output slots, and `bits` counts saved input bits. The main decoder selects `inflate_fast` in `LEN` when `have ≥ 6`, `left ≥ 258`, and `bits < 8`. It restores locals to the stream before calling and loads the returned state afterward. The actual call site is [pinned `inflate.c`, lines 923–927](https://github.com/madler/zlib/blob/757f0527154291bcf6bfbd6396ecde6bedd2db95/inflate.c#L923-L927):

```c
case LEN:
    if (have >= 6 && left >= 258 && bits < 8) {
        RESTORE();
        inflate_fast(strm, out);
        LOAD();
```

`RESTORE` publishes local cursors and bits to the stream; `LOAD` reloads them after the helper. The excerpt ends inside the real branch. With two output slots our paused-match example cannot take it; with enough input and 258 output slots the decoder can enter it when ready to read another instruction.

At that call site, the main decoder's `out` is a saved available-output count, passed as the helper's `start` argument. Names change meaning across functions. Inside the helper, `in` and `out` are current pointers. `avail_in` and `avail_out` count remaining bytes, while `start` is the output capacity at the outer call's start. The limits `last` and `end` mark where another full instruction would lack the required input or output room. These teaching equations restate its pointer setup, rather than quote C:

```text
last = in  + (avail_in  - 5)
end  = out + (avail_out - 257)
beg  = out - (start - avail_out)
```

`beg` names the outer call's output start, even if that call produced bytes before entering this fast helper. The first body executes as a `do` loop, so entry margins must already hold. Later iterations use `in < last && out < end`.

A match writes at most 258 bytes. A complete length/distance instruction (a **token**) reads at most six input bytes. Summing individual refill maxima gives seven, but they cannot all occur together: earlier refills leave enough residual bits to prevent the last site from requiring its maximum. The [fast-decoder reference](/reference/docs/proof/inffast.html#bit-counts-and-the-six-byte-bound) develops that accounting.

## Unrolled execution {#unrolling}

The fast helper copies several bytes per loop body and handles a final one- or two-byte remainder. The direct-output `do` loop relies on the minimum match length of three. Window prefixes have separate positive counters. Their read/write order matters when the source overlaps the destination.

Table links likewise use backward jumps to `dolen` or `dodist`. Valid installed tables bound this linked lookup to one subtable level. Invalid length/distance symbols and unavailable history exit through error state; end-of-block exits through its prescribed mode. Fast means fewer repeated checks, not fewer error obligations.

## Byte backtracking and writeback {#writeback}

Before returning, the helper puts unused whole bytes back. Here is the actual `inflate_fast` epilogue at [pinned `inffast.c`, lines 291–294](https://github.com/madler/zlib/blob/757f0527154291bcf6bfbd6396ecde6bedd2db95/inffast.c#L291-L294). At this point `len` is reused for the whole-byte count; it is no longer a match length:

```c
len = bits >> 3;
in -= len;
bits -= len << 3;
hold &= (1U << bits) - 1;
```

With 19 buffered bits, this returns two bytes and retains three. Entry with fewer than eight held bits ensures the returned bytes were pulled by this helper, rather than before its entry. The final epilogue updates exact cursors, availability counts, held bits and mode even on error exits.

This algorithm reading is **to confirm** through the execution argument. Small buffers must remain covered by slow dispatch, and fast-path premises must be derived at each actual call. The next chapter connects both routes to [one decoder argument](/sample/decode-proof.html). Full caller effects and defined error returns belong to the [`inflate` contract](/reference/functions/inflate.html), not to the happy-path animation.
