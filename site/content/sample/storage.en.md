The [bit writer](/sample/bits.html) produces bytes in pending storage. The [block encoder](/sample/blocks.html) obtains the values to encode by reading symbol records. It is tempting to picture these as two separate arrays. In the selected default layout, they are two views into **one allocation**.

The optimization uses a change in lifetime: once a symbol has been read into local variables, its record is no longer needed by `compress_block`. Output may reuse the space behind that read position. The implementation must keep its writes behind the records it still needs.

## Two views into one allocation {#layout}

Let `B = lit_bufsize`. Initialization sets `B = 1 << (memLevel + 6)`, allocates `4B` bytes for `pending_buf`, and places `sym_buf` at offset `B`. The ordinary packed layout stores three bytes per symbol and stops tallying at `(B-1)*3` symbol bytes. Thus a block holds at most `B-1` records.

```text
allocation:  [0 ........................................... 4B)
output:      [pending bytes grow from the base ..............)
symbols:               [B, B+3) [B+3, B+6) ... [4B-6, 4B-3)
                       record 0  record 1       last record
```

At the default `memLevel = 8`, `B` is 16384. The pending allocation has 65536 bytes, the first record starts at offset 16384, and at most 16383 records use 49149 bytes. These records are already inside the allocation; the design does not allocate another 49149-byte symbol array.

The source reserves the last record slot through `sym_end = (B-1)*3`. Its comment relates the choice to 16-bit wraparound and the stored-block size limit. The separate `LIT_MEM` layout uses different arrays and bounds; the diagram here describes the ordinary packed-symbol branch.

Before output begins, the first B bytes provide headroom. Later, consuming each record releases three more bytes. That is the mechanism that makes sharing possible; it does not by itself tell us how fast output will grow.

## The moving read boundary {#boundary}

`compress_block` starts with `sx = 0`. Each iteration reads both distance bytes and the literal/length byte, advancing `sx` by three before it calls the output helpers. A literal emits one code. A match emits a length code, any length extras, a distance code and any distance extras.

After q records have been consumed, the next unread record starts at

```text
R(q) = B + 3q
```

For the three-record example, the boundaries are `B`, `B+3`, `B+6`, and `B+9`. The writer produces the five bytes derived earlier, far behind even the first boundary at the default size. The point of a proof is to cover other symbol sequences too, including much longer codes.

During a fresh emission phase with the pending write base normalized, let `P(q)` count the bytes written at the allocation base after the qth record has been emitted. Writes occupy a half-open interval `[0, P(q))`. Avoiding the unread suffix requires that those writes end no later than `R(q)` while unread records remain. The `ZLIB_DEBUG` build asserts the stronger, strict condition `pending < B + sx` after each record, leaving a margin. In a release build, `Assert` expands to no code: it does not check this condition or prevent a write at runtime. The argument must establish the bound before relying on it.

A strict bound is a convenient sufficient condition, not the definition of an overwrite. If the write ends exactly at the unread boundary, the half-open ranges still do not overlap. The proof must state which inequality it establishes and relate the counter to the actual stores. A pending count after a partial delivery is not automatically an offset from the base: the `pending_out` cursor and the entry state also matter.

## Output growth and prefix cost {#prefix}

Why might output catch up? A packed record costs three stored bytes, but a fixed match can require as many as 31 encoded bits: eight length-code bits, five length-extra bits, five distance-code bits and thirteen distance-extra bits. Three bytes are only 24 bits. The initial gap therefore matters.

For fixed blocks, a per-symbol worst-case bound can be accumulated with the three-bit block header, initial held bits, and register-to-byte rounding. This leads to a bound for **every prefix** of the symbol sequence. The permitted symbol count and the initial B-byte gap can then be used to show that the writing frontier stays behind unread input. The end code and final alignment need a final capacity argument after symbol consumption is complete.

Dynamic blocks add two complications. First, their tree description is written before record 0 is read, so that entire prefix must fit before offset B. Second, the code lengths come from the block's frequencies. A dynamic block may have expensive early symbols and cheap later symbols. Knowing that its whole-block cost beat the fixed candidate does not bound the cost of those early prefixes.

The dynamic argument therefore needs a relation between the actual constructed tree, the actual frequencies and emitted prefixes. Kraft validity says the lengths describe a prefix code; it does not alone say how the costly symbols are distributed in this block. This is the point where the tree-construction analysis becomes relevant to memory reuse.

## A small counterexample to the total-only argument {#comparison}

The following teaching allocation uses `B = 8` and capacity 32, below the actual permitted B values. Both artificial plans fit in the allocation at completion. One emits many bytes immediately; the other spreads them across the records. Move one record forward and compare the write frontier with the unread boundary.

<div class="zl-demo-mount"><zlib-demo kind="overlay"><p>The teaching buffer has 32 bytes and symbols beginning at offset 8. The front-loaded plan overwrites unread symbols even though its final output fits. The diagram is a constructed comparison, not a zlib failure.</p></zlib-demo></div>

Once a write has changed an unread record, later cheap output cannot restore the original value. Even a later safe-looking boundary does not erase the earlier overwrite. The damaged distance can also lead to an invalid later table lookup, so preserving records supports the encoder's reads as well as its output writes.

Stored blocks have a different lifetime. After choosing the stored form, the implementation copies the original bytes and does not consume the symbol records. Their preservation obligation ends at that selection; output can then reuse their region subject to the stored branch's source, copying and capacity conditions.

We can now state the real question without introducing a new data structure: each helper must preserve the unread input that the next helper will use. [The proof chapter](/sample/proof.html) turns this execution story into the bit-sequence relation, storage invariant and composition steps.

The full derivation of emission-entry accounting, dynamic prefix costs and caller coverage remains **to confirm**. The [overlay argument](/reference/docs/proof/trees.html#the-overlay-lemma-f9) records the exact obligations and historical scope; [current progress](/reference/docs/progress.html) records acceptance and open work. A constructed teaching plan is not evidence of an upstream bug.
