# Fast decoding: margins, history and source bits

Source: `zlib/inffast.c`; translation: `ZlibF/Zlib/inffast.c.lean`.
The contract vocabulary is `I-if-*` in
[internal contracts](../design/internal-contracts.md). Table predicates come
from [table construction](inftrees.md). Window invariant W is explained in
[stream decoding](inflate.md).

This is an internal function. A theorem under `I-if-pre-*` does not prove that
all legal `inflate` calls establish those premises. A source-bit preservation
result also needs a bridge to the independent format semantics. See
[the overview](../overview.md) for the current scope of those results.

## Entry views and loop invariant

`I-if-pre-room` gives mode `LEN`, at least six input bytes and 258 output bytes,
and a readable earlier-output prefix of the outer `inflate` call in the same
output object. Input and output are disjoint. `I-if-pre-bits` gives `bits < 8`
and identifies `hold` with exactly those low buffered bits.
`I-if-pre-tables` supplies initialized, meaningful root/subtable entries.
`I-if-pre-window` supplies the valid history and the default sane-distance mode.

The source forms

```
last = in + (avail_in - 5)
end  = out + (avail_out - 257)
beg  = out - (start - avail_out)
```

Here `beg` starts the outer call's output, not necessarily this fast call's
output. The precondition must justify its pointer subtraction for the actual
buffer view. Write `in0`, `out0` for the fast-call cursors.

At each body entry, use these named invariants:

| Name | Content |
| --- | --- |
| I1 | `in0 ≤ in ≤ in0 + avail_in`; the loop margin gives six readable bytes at the cursor. |
| I2 | `out0 ≤ out`; the loop margin gives 258 writable bytes at the cursor. |
| I3 | `hold < 2^bits`, with body bit counts at most 30 and entry bits below 8. |
| I4 | `beg ≤ out`; the range `[beg, out)` has been produced by the outer call. |

The first body is reached by a `do` loop, so entry premises must supply its
margins directly. Later bodies use `in < last && out < end`.

## Bit counts and the six-byte bound

There are four refill sites for a length/distance pair.

| Site | Guard and read count | Useful bound |
| --- | --- | --- |
| R1, before length lookup | `bits < 15`: read two bytes | Refill leaves 16 to 30 bits. |
| R2, length extras | `bits < op`, `op ≤ 5`: read one byte | Refill leaves at most 12 bits. |
| R3, before distance lookup | `bits < 15`: read two bytes | Refill leaves 16 to 30 bits. |
| R4, distance extras | `bits < op`, `op ≤ 13`: up to two bytes | The guarded refills keep the count at most 28. |

If R1 or R3 is skipped, at least 15 bits are already available. Table meanings
bound a complete code, including its possible subtable lookup, by 15 bits.
R2 provides enough for at most five extras; R4 provides enough for at most 13.
Thus each `bits -= op` removes only available bits. Refills preserve I3, and
the associated shifts stay within their machine widths.

The independent maxima would allow seven input bytes. That combination is
impossible. Suppose R1, R2, R3 and R4 read 2, 1, 2 and 2 bytes. After R1 and a
length code of at most 15 bits, at least one bit remains. After R2 and at most
five length extras, at least `1 + 8 - 5 = 4` remain. After R3 and at most 15
distance-code bits, at least `4 + 16 - 15 = 5` remain. A second R4 byte requires
fewer than five before its first refill, because even that refill left fewer
than `op ≤ 13`. Contradiction.

Each body therefore reads at most six bytes. This is the reason for `last`'s
five-byte subtraction. A literal writes one byte; a match writes at most 258,
from the length table's base/extra interpretation. This justifies `end`'s
257-byte subtraction. The room bounds depend on table semantics, not merely on
allocated table capacity.

## Table reads

A root index `hold & ((1 << rootbits) - 1)` is below `2^rootbits`. T2 supplies
its initialized entry. A link supplies a bounded subtable interval; the masked
subindex lies inside that interval. The table predicate must also establish the
entry's operation, code length and base/extra ranges and that a second-level
entry is not another link. The `goto dolen`/`dodist` paths then terminate after
at most one linked lookup.

Reserved symbols reach the correct error exit. End-of-block reaches the mode
transition prescribed by the caller contract. These exits still require exact
cursor, bit-buffer and state effects.

## Match copies: F3 and F4

Let `done = out - beg`, `dist ≥ 1` be the decoded distance and `3 ≤ len ≤ 258`
the match length.

If `dist ≤ done`, the source starts at `out - dist ≥ beg`. The copy is
sequential: at step k its source is the already produced byte at relative
position `k - dist`. That byte precedes the destination even when source and
destination ranges overlap. This is the DEFLATE repetition rule; replacing the
loop by a disjoint-copy argument would lose it.

If `dist > done`, set `op = dist - done`. The sane-distance check rejects
`op > whave`. After the check, `1 ≤ op ≤ whave ≤ wsize`, so the allocated window
contains the required earlier history. Its three source shapes are:

| Condition | Initial window index | Boundary argument |
| --- | --- | --- |
| `wnext == 0` | `wsize - op` | Copy through the end of the ring. |
| `0 < wnext < op` | `wsize + wnext - op` | Copy `op - wnext` bytes through the end, then up to `wnext` from index 0. |
| `wnext ≥ op` | `wnext - op` | Copy before the current ring cursor. |

Each piece copies only the smaller of its history count and the remaining match
length. If the match outlasts the window contribution, its remaining source is
in output already produced by this call, where the sequential-copy argument
applies. Prove the exact unrolled loop counts, including the positive initial
count for every `do … while (--op)`.

F4 says `whave < wsize` implies `wnext = whave`. In a partial ring, only the
third shape is possible; its source lies in initialized history. In a full ring,
all bytes are history and the wrap shapes are valid. The stronger functional
invariant must identify those bytes with the suffix of the logical output and
dictionary history.

## Rollback and final writeback

The exit returns speculative whole input bytes:

```
len = bits >> 3
in -= len
bits -= len << 3
hold &= (1U << bits) - 1
```

If B bytes were read by this fast call, the accounting invariant gives
`bits ≤ bits_entry + 8B < 8 + 8B`. Hence `len ≤ B` and rollback never precedes
`in0`. The result has fewer than eight buffered bits, so the final mask shift is
valid. The function then writes exact remaining input/output counts and cursors,
`hold`, `bits` and the reached mode back to the stream.

`bits_entry < 8` is essential. Without it rollback could return bytes that this
fast call never read. **to confirm**: the main decoder establishes that premise
on every actual transition/call into this fast path, including resumed calls and
fixed/dynamic table installation. A general observation about refill/drop
macros is insufficient without checking those paths and buffer views.

## From safety to decoding

The functional loop invariant must identify the consumed low bits with the
original source stream and relate emitted literals/matches to independent
format symbols. Preserve that relation through length/distance selection,
extra-bit reads, all copy shapes, linked tables, end and error exits, rollback
and final writeback. The source relation must survive whole-body and whole-call
composition, rather than only a successful local token.

Internal source-origin lemmas can establish exact selected bits for their
stated domains. Connecting them to init-established state, installed tables,
all legal caller views and independent output semantics is a separate
refinement obligation. Speculative lookahead is not automatically justified by
the bytes supporting a decoded symbol; the causal distinction is explained in
[inflate](inflate.md).

For termination, a body writes at least one byte or exits on end/error. The
finite output range bounds the number of continuing bodies. Copy loops and
linked lookups also have bounded measures. Translate those bounds into the
actual fuel budget and preserve the frame on every exit. No allocation occurs
here; ownership of the existing state/window remains unchanged.
