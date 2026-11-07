# Decode tables: from lengths to initialized entries

Source: `zlib/inftrees.c`; translation: `ZlibF/Zlib/inftrees.c.lean`.
The internal vocabulary is `I-it-*` in
[internal contracts](../spec/internal-contracts.md). The mathematical target is
the canonical-code relation `F-code-*` in the
[format guide](../spec/format/README.md).

The central proof has three layers: code lengths describe a canonical prefix
code; the construction writes a bounded table; the actual heap entries implement
that code, including invalid markers. Only the last layer justifies the table
predicates used by `inflate` and `inflate_fast`. The argument below is a proof
strategy; [the overview](../overview.md) records which connections are accepted.

## Domain and outcomes

`I-it-pre-lens` provides readable lengths in `0..15`. For `CODES`, lengths are at
most 7 and the requested root width is at least 7. `I-it-pre-codes` bounds the
symbol count by 19, 288 or 32 for `CODES`, `LENS` or `DISTS`.
`I-it-pre-work` supplies writable disjoint scratch. `I-it-pre-table` supplies
writable table/root-width cells and a disjoint table region of 128, 852 or 592
entries for the respective types.

The safety target, called **T1** in earlier notes, is termination and no fault
under those internal premises, on every return: 0 for success, -1 for invalid
lengths and 1 for insufficient table capacity. The exact contract must describe
partial writes and parameter-cell effects on each return. A failure is not a
promise that the heap is unchanged.

The successful-table target, **T2**, gives coverage of root/subtable entries,
bounded links and the meaning of each reached entry. All-zero lengths and the
permitted single-symbol incomplete code need explicit cases. A caller also
needs the actual pointer advancement and returned root width.

## Counting and Kraft checks: F1 and F2

Let `c_l` count symbols of positive length `l`, `m = Σ c_l`, and let `min` and
`max` be the first and last occupied lengths when `m > 0`. Clamping the requested
root gives `min ≤ root ≤ max ≤ 15`.

Define the first canonical code of length `l` by

```
B_l = Σ_{1 ≤ j < l} c_j 2^(l-j)
B_1 = 0
B_(l+1) = 2 (B_l + c_l)
left_l = 2^l - B_l - c_l
```

The signed Kraft loop maintains `left_0 = 1` and
`left_l = 2 left_(l-1) - c_l`. It rejects when the result is negative. Passing
therefore gives `B_l + c_l ≤ 2^l`, so every assigned length-l code fits in l bits.
The proof must bound the signed intermediates too.

The final incomplete-code check permits a positive remainder only when the type
is not `CODES` and `max = 1`. Then a nonempty incomplete code has exactly one
symbol of length 1. This exception is essential for coverage reasoning; it is
not a complete Kraft partition.

The counting offsets start at `offs[1] = 0` and satisfy
`offs[l+1] = offs[l] + c_l`. Symbol i of length l is written to
`work[Σ_(j<l) c_j + i]`, with `i < c_l`. That index is below `m ≤ codes`.
Distinct symbols occupy distinct slots, so `work[0..m)` is initialized and sorted
by `(length, symbol)`. This is **F2**. It supplies both the index bounds and the
meaning of later `work[sym]` reads.

## The reversed-code walk

Let `rev_l(v)` reverse the l bits of v. The main loop invariant identifies
`huff = rev_len(B_len + i)` for the current symbol, and gives `huff < 2^len`.

At the first positive length, the first canonical code is zero. For a successor
of the same length, the descending mask clears the leading ones of the reversed
word and sets its next zero, which reverses ordinary binary increment. If the
word is all ones, it wraps to zero. When the next occupied length is larger,
the canonical recurrence appends low zero bits to the ordinary code. Those are
high zero bits after reversal, so `huff` retains the right value at the new
width.

For a complete code, the last ordinary code is `2^max - 1`; the final reversed
increment is zero. For the one-symbol exception it is 1. These facts determine
whether the tail invalid-marker write occurs.

## Replication and subtable size

For a root-table entry with `len ≤ root`, the fill loop writes indices

```
huff + (2^root - 2^len), …, huff + 2^len, huff
```

Since `huff < 2^len`, all are below `2^root`. The fill count is a multiple of
`2^len`, so the decrements finish at zero without wrapping. These are exactly
the indices whose low len bits match the reversed code.

For `len > root`, a root prefix p groups consecutive ordinary canonical codes.
The sizing loop starts with `curr = len - root` and `left = 2^curr`, subtracts
remaining counts at the current depth and doubles free slots when it descends.
If fewer codes remain at that depth than free slots under p, those codes all
belong to p. If the codes fill the slots, the prefix is complete at that depth.
The loop also stops at `max`. This counting argument must establish that every
code under p has `len - root ≤ curr`.

With `drop = root`, replication then uses increments `2^(len-drop)` inside a
`2^curr` table. Divisibility and `huff >> drop < 2^(len-drop)` give the same
bounds as for root replication. The look-ahead count may include codes for
later prefixes at its final depth; the proof must justify that its stopping
condition is still sufficient for the current prefix.

## Capacity and pointer formation

`used` starts at `2^root` and increases by each subtable's `2^curr`. The current
`next` pointer is the table base plus the capacity of earlier tables. The
`LENS`/`DISTS` checks reject a capacity above 852/592 before the new subtable is
written or linked. Pointer formation and arithmetic before the check still
need their own one-past bounds from the previous reservation.

`CODES` has no such capacity check. Its stronger length/root premise ensures
`max ≤ 7` and `root = max`, so it opens no subtables and uses at most 128 entries.
The guard argument for the other types does not replace this caller premise.

The constants 852 and 592 were chosen using exhaustive table-size analysis.
The explicit checks suffice for safety of the selected construction, provided
all operations before them are safe. Showing that every valid format code is
accepted requires a separate bound: a safe capacity refusal alone proves no
such completeness property.

A root link uses `low = huff & (2^root - 1) < 2^root` and stores the subtable
width and offset `next - base`. Show that this offset fits its 16-bit field and
that the linked interval is inside the reserved table.

## Coverage and meaning: T2

For a complete code, the leaf intervals of widths `2^-len` partition the code
space. A root entry either lies under one short leaf, whose replication writes
it, or contains longer leaves, whose first member creates and links its
subtable. Apply the same interval argument inside that subtable. Disjoint leaf
intervals prevent different symbols from giving one entry conflicting meanings.

For the one-symbol incomplete code, `root = 1`: the loop writes entry 0 and the
tail writes entry 1 as invalid. For no coded symbols, the separate branch writes
two invalid entries, returns width 1 and advances the table pointer by two.
Neither case may be justified by pretending the code is complete.

Coverage alone is insufficient. Prove the `op`, `bits` and `val` interpretation:
literal, length/distance base plus extra bits, end of block, invalid marker or
subtable link. Establish the total code-length bound across a link and the fact
that a second-level entry is not another link. Fixed tables installed by
`inflate_fixed` require the same reader predicate, including their reserved
invalid symbols.

## Other local side conditions

These are the components of T1/T2, not a second progress register.

| Operation | Fact required |
| --- | --- |
| `count[lens[sym]]` | Length is at most 15. |
| `count[curr + drop]` | The sizing-loop condition bounds the sum by `max ≤ 15`. |
| Next `work[sym]` and `lens[work[sym]]` | A remaining symbol exists whenever the loop continues; F2 bounds and initializes its slot. |
| `LENS` base/extra access | The relevant symbol is at least 257 and at most 287, within the 31-entry arrays. |
| `DISTS` base/extra access | Symbol is at most 31, within the 32-entry arrays. |
| `CODES` null base/extra pointers | The branch selecting them is never reached for symbols `0..18`. |
| Shift counts | Positive code lengths and bounded root/subtable widths justify each `1 << k`, including `len - 1` and `len - drop`. |
| Loop termination | Counting/sorting loops have fixed ranges; the main loop consumes one of m symbols; mask descent and subtable look-ahead have bounded bit/depth ranges. |
| Frame | Only authorized scratch, output entries and parameter cells change; static base/extra arrays remain read-only. |

Pure canonical-code lemmas belong in `ZlibF/Math/`. Their connection to the
translated stores, all exits and the installed decoder invariant belongs in the
execution proof. [The method](method.md) describes how callers must discharge
these premises without assumed callee contracts.

## C correspondence checks

### Decode tables and flags

`code` has byte fields `op`, `bits` and a 16-bit `val`. Default table capacity is
`ENOUGH_LENS = 852`, `ENOUGH_DISTS = 592`, total 1444. Code lengths are at most 15.
The code-length permutation is `16,17,18,0,8,7,9,6,10,5,11,4,12,3,13,2,14,1,15`.

| Entry | Meaning |
| --- | --- |
| `op = 0` | literal |
| `op = 1..15` | subtable link; low bits give its index width |
| `op = 16 + e` | length or distance base with `e` extra bits |
| `op = 96` | end of block; both bits 32 and 64 are set |
| `op = 64`, `68` or `193` | invalid symbol |

Flag order matters. The slow literal/length decoder tests end-of-block before invalidity.
The fast decoder tests literal, length, link, then end-of-block/invalid exits in source order.
An arbitrary safety-shaped table does not justify interchanging these tests. Semantic
bridges require compatible leaf flags from actual construction or fixed tables.
`DIST` lacks the `op != 0` guard used by `LEN`; only a distance-table invariant makes that
safe. `CODELENS` reads `val` without checking `op`. An all-zero alphabet produces two
invalid entries with `val = 0`; decoding eventually fails the missing-end-of-block check.

The fixed tables are copies of `inffixed.h`: 512 literal/length entries and 32 distance
entries, with roots 9 and 5. Reconstructing them through `inflate_table` changes four
literal/length entries, indices 99, 227, 355 and 483. The generated invalid flags are 68 or
193; the header uses 64. All reject the reserved symbols, but byte-for-byte fidelity requires
the header values. The older reference to tables inside `fixedtables` in `inflate.c` was stale.
The base/extra arrays and permutation are indexed constants. Error messages remain readable,
read-only string blocks because callers can inspect `strm->msg`.

#### `inflate_table`

Keep the counting, Kraft check, sorting, table fill and tail in source order.
Lengths within `0..15`, sufficient `lens`/`work` space and table capacity are internal
premises that callers must establish; the function does not validate every index itself.
The no-symbol case writes two invalid entries and updates both out-parameters before
returning success. Oversubscribed and disallowed incomplete alphabets return `-1`.
Capacity exhaustion returns `1`, possibly after table entries have been written.

The translation passes `*table` and `*bits` by value and returns their new values.
An error preserves those two scalar values, but does not undo entry writes. Callers must
preserve that distinction on every return path. In `CODELENS`, `lencode` is assigned before
the length-table call, and `distcode` is assigned from the advanced `next` before the distance
call. Reordering either assignment changes the heap history.

Keep these arithmetic details:

- `count` and `offs` are 16-bit arrays with C promotion and narrowing.
- `left` is signed, including its shifts and subtractions. The later `1 << curr` is a
  signed expression; the earlier `1U << root` is unsigned.
- The variable `min` changes meaning at `min = fill`: it now holds the current table size.
- `fill -= incr` and the final `while (copy--)` in the caller retain unsigned behavior.
- Root links store a pointer difference narrowed to 16 bits. Their index and shift bounds
  depend on the canonical-code construction, **to confirm** against the written heap.

#### Slow lookup and malformed lookahead

A root lookup can select an entry before its nominal root width is available, provided the
selected entry's own consumed length fits the available prefix. The needed property is
stability under future suffix bits. A link requires the corresponding second-level lookup
and both consumed lengths. Memory bounds alone do not establish symbol meaning.

Pulled input and checked input differ. A decoder can pull malformed future bits while
already having enough checked bits to justify a literal or match. Requiring every pulled
byte to have a valid continuation is false. The causal model instead uses a checked bit
prefix with a valid completion, and requires the output to agree with every compatible
completion and every still-permitted dictionary. An unknown wrapped dictionary cannot be
silently replaced by the empty dictionary. This is a specification distinction, not permission
to alter refill order. See [API contracts](../spec/api/README.md) and [proof notes](README.md).

The earlier fixed eight-byte error-detection lag also has a counterexample. It cannot be used
as a source invariant or repaired by merely increasing the constant. Current status belongs
in [overview](../overview.md).
