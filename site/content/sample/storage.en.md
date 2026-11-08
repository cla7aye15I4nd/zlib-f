Block encoding has another easy-to-miss task: produce the right output while preserving input it has not yet read. Here each input record stores either a literal byte or a copy length and backward distance. The output is **pending bytes**: complete compressed bytes produced by the bit writer but not yet delivered to the caller. The default layout lets both share one allocation to save a separate symbol array. Safety depends on the order of reads and writes.

Start with the completed `ABABABAB` example before introducing general boundary formulas. The goal is more than “five output bytes fit”: every record must survive until the encoder reads it.

## How three records release their space {#example}

At the default memory level, symbols start at allocation offset 16384 and output starts at offset 0. The three records occupy `[16384,16387)`, `[16387,16390)` and `[16390,16393)`. A range includes its left endpoint and excludes its right endpoint.

| Execution point | Next unread record | Pending bytes already written | Bits still held in the register |
| --- | --- | --- | --- |
| After header | A at offset 16384 | None | 3 |
| After reading and encoding A | B at offset 16387 | None | 11 |
| After reading and encoding B | Match at offset 16390 | `73 74` | 3 |
| After reading and encoding the match | No unread records | `73 74` | 15 |
| After end code and final alignment | No unread records | `73 74 82 40 00` | 0 |

Before B is read, its three record bytes must keep their original values. Once read into local variables, that space may be reused. The same is true of the match record. Keeping writes behind unread records lets execution continue along this path. This short example has ample separation; we still need to handle many records whose codes are much longer.

## Two views into one allocation {#layout}

The layout is controlled by one scale: `B`, called `lit_bufsize` in the state. It determines both the record limit and the initial byte gap before the records; it is not the total allocation size. The initialization parameter `memLevel` chooses the memory budget. It sets `B = 1 << (memLevel + 6)`, meaning `2^(memLevel+6)`. Initialization allocates `4B` bytes for the output view `pending_buf` and places the symbol view `sym_buf` at byte offset `B`. The ordinary packed layout stores three bytes per symbol and stops tallying at `(B-1)*3` symbol bytes. Thus a block holds at most `B-1` records.

```text
allocation:  [0 ........................................... 4B)
output:      [pending bytes grow from the base ..............)
symbols:               [B, B+3) [B+3, B+6) ... [4B-6, 4B-3)
                       record 0  record 1       last record
```

Initialization in `deflateInit2_` creates these views. These are [`deflate.c:504–505`](https://github.com/madler/zlib/blob/757f0527154291bcf6bfbd6396ecde6bedd2db95/deflate.c#L504-L505); `ZALLOC` requests `B` elements through the stream allocator. The size of each element is `LIT_BUFS`, or 4 bytes in the ordinary layout; `s` points to the compressor state:

```c
s->pending_buf = (uchf *) ZALLOC(strm, s->lit_bufsize, LIT_BUFS);
s->pending_buf_size = (ulg)s->lit_bufsize * 4;
```

The first line allocates B elements of four bytes each. The second records `4B` bytes as pending capacity. After the allocation-failure check, the ordinary branch executes [`deflate.c:519–520`](https://github.com/madler/zlib/blob/757f0527154291bcf6bfbd6396ecde6bedd2db95/deflate.c#L519-L520):

```c
s->sym_buf = s->pending_buf + s->lit_bufsize;
s->sym_end = (s->lit_bufsize - 1) * 3;
```

The first line points the symbol view B bytes into that same allocation; it allocates nothing further. The second sets the record-byte limit to `(B−1)×3`. In our example B is 16384, placing the records exactly at the offsets in the trace above.

At the default `memLevel = 8`, `B` is 16384. The pending allocation has 65536 bytes, the first record starts at offset 16384, and at most 16383 records use 49149 bytes. These records are already inside the allocation; the design does not allocate another 49149-byte symbol array.

The source reserves the last record slot through `sym_end = (B-1)*3`. Its comment relates the choice to 16-bit wraparound and the stored-block size limit. The separate `LIT_MEM` layout uses different arrays and bounds; the diagram here describes the ordinary packed-symbol branch.

Before output begins, the first B bytes provide headroom. Later, consuming each record releases three more bytes. That is the mechanism that makes sharing possible; it does not by itself tell us how fast output will grow. Two boundaries move together. Reading a record extends the reusable region to the right; producing complete encoded bytes moves the write position right. The latter must stay behind records that are still needed. The next section expresses both boundaries as byte offsets in the same allocation so they can be compared directly.

## The moving read boundary {#boundary}

To avoid overwriting the next record, the encoder tracks how many symbol bytes it has already read. This byte offset is `sx` in `compress_block`; it starts at zero. A value of `sx = 6` means two complete three-byte records have been consumed. Each iteration reads both distance bytes and the literal/length byte, advancing `sx` by three before it calls the output helpers. A literal emits one code. A match emits a length code, any length extras, a distance code and any distance extras.

The read-before-write order is visible in [`compress_block`, trees.c:913–915](https://github.com/madler/zlib/blob/757f0527154291bcf6bfbd6396ecde6bedd2db95/trees.c#L908-L938):

```c
dist = s->sym_buf[sx++] & 0xff;
dist += (unsigned)(s->sym_buf[sx++] & 0xff) << 8;
lc = s->sym_buf[sx++];
```

The first line reads the low distance byte and advances `sx`. The second reads the high byte, shifts it and adds it to the distance. The third reads the literal/length offset and advances a third time. Reading match record `02 00 03` leaves local values `dist = 2`, `lc = 3`, and moves `sx` from 6 to 9. Only then does the source select the literal or match branch and emit codes. It may reuse the current record but must still preserve the next one.

Let `q` count complete records already consumed; it is a record count, so their byte count is `3q`. Call the next unread byte offset `R(q)`. It starts at

```text
R(q) = B + 3q
```

For the three-record example, the boundaries are `B`, `B+3`, `B+6`, and `B+9`. The writer produces the five bytes derived earlier, far behind even the first boundary at the default size. The point of a proof is to cover other symbol sequences too, including much longer codes.

During a fresh emission phase whose undelivered bytes start at the allocation base, let `P(q)` count the bytes written at the allocation base after the qth record has been emitted. Writes occupy a half-open interval `[0, P(q))`. Avoiding the unread suffix requires that those writes end no later than `R(q)` while unread records remain. The `ZLIB_DEBUG` build asserts the stronger, strict condition `pending < B + sx` after each record, leaving a margin. In a release build, `Assert` expands to no code: it does not check this condition or prevent a write at runtime. The argument must establish the bound before relying on it.

A strict bound is a convenient sufficient condition, not the definition of an overwrite. If the write ends exactly at the unread boundary, the half-open ranges still do not overlap. The proof must state which inequality it establishes and relate the counter to the actual stores. A pending count after a partial delivery is not automatically an offset from the base: the `pending_out` cursor and the entry state also matter.

## Output growth and prefix cost {#prefix}

Why might output catch up? A packed record costs three stored bytes, but a fixed match can require as many as 31 encoded bits: eight length-code bits, five length-extra bits, five distance-code bits and thirteen distance-extra bits. Three bytes are only 24 bits. The initial gap therefore matters.

For fixed blocks, a per-symbol worst-case bound can be accumulated with the three-bit block header, initial held bits, and register-to-byte rounding. This leads to a bound for **every prefix** of the symbol sequence. The permitted symbol count and the initial B-byte gap can then be used to show that the writing frontier stays behind unread input. The end code and final alignment need a final capacity argument after symbol consumption is complete.

Dynamic blocks add two complications. First, their tree description is written before record 0 is read, so that entire prefix must fit before offset B. Second, the code lengths come from the block's frequencies. A dynamic block may have expensive early symbols and cheap later symbols. Knowing that its whole-block cost beat the fixed candidate does not bound the cost of those early prefixes.

The dynamic argument therefore needs a relation between the actual constructed tree, the actual frequencies and emitted prefixes. Kraft validity checks whether code lengths can fit in a binary tree without one code being the prefix of another; it does not alone say how the costly symbols are distributed in this block. This is the point where the tree-construction analysis becomes relevant to memory reuse.

## A small counterexample to the total-only argument {#comparison}

The following teaching allocation uses `B = 8` and capacity 32, below the actual permitted B values. Both artificial plans fit in the allocation at completion. One emits many bytes immediately; the other spreads them across the records. Move one record forward and compare the write frontier with the unread boundary.

<div class="zl-demo-mount"><zlib-demo kind="overlay"><p>The teaching buffer has 32 bytes and symbols beginning at offset 8. The front-loaded plan overwrites unread symbols even though its final output fits. The diagram is a constructed comparison, not a zlib failure.</p></zlib-demo></div>

Once a write has changed an unread record, later cheap output cannot restore the original value. Even a later safe-looking boundary does not erase the earlier overwrite. The damaged distance can also lead to an invalid later table lookup, so preserving records supports the encoder's reads as well as its output writes.

Stored blocks have a different lifetime. After choosing the stored form, the implementation copies the original bytes and does not consume the symbol records. Their preservation obligation ends at that selection; output can then reuse their region subject to the stored branch's source, copying and capacity conditions.

We can now state the real question without introducing a new data structure: each helper must preserve the unread input that the next helper will use. [The proof chapter](/sample/proof.html) turns this execution story into the bit-sequence relation, storage invariant and composition steps.

The complete shared-storage composition proof is unfinished: emission-entry accounting, every dynamic prefix cost and the admitted call histories still need to be connected. The [overlay argument](/reference/docs/proof/trees.html#the-overlay-lemma-f9) records the exact obligations and historical scope; [current progress](/reference/docs/progress.html) records acceptance and open work. A constructed teaching plan is not evidence of an upstream bug.
