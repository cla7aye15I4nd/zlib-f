[The input reservoir](/sample/input-bits.html) exposes low bits efficiently. A decoding table turns them into a literal, a length or distance base, an end marker, an invalid marker, or a link to another table. Before the decoder can use it, `inflate_table` has to construct that array from the supplied code lengths.

We will follow the construction itself before discussing its proof. The four-symbol code `A=0`, `B=10`, `C=110`, `D=111` remains a small teaching alphabet. Actual DEFLATE calls use the code-length, literal/length, or distance alphabets, with different meanings and limits.

## Length counts and occupied space {#counts}

[`inflate_table`](/reference/source/ZlibF/Zlib/inftrees.c.html#L243) clears `count`, then increments `count[lens[sym]]` for each input symbol. Zero means unused. The nonzero lengths determine `min` and `max`; the requested root width is clamped into that occupied range.

The constructor then checks whether the lengths can fit. Starting with one available root slot, each depth doubles the free slots and subtracts the symbols placed there:

```text
left = 1
for each length l from 1 through 15:
    left = 2 * left - count[l]
```

A negative result is oversubscription and returns `-1`. A positive remainder describes an incomplete code. The source does not accept all such codes: outside the separately handled empty case, a positive remainder is permitted only for non-`CODES` input with maximum length one. The accepted nonempty incomplete case has a single one-bit symbol.

## Offsets and stable symbol order {#ordering}

Lengths alone determine how many codes belong at each depth. Symbols still need a deterministic order within each depth. `offs[1] = 0`, and `offs[l+1] = offs[l] + count[l]` gives each length's starting slot in scratch array `work`.

For lengths `[1,2,3,3]`, the relevant counts are `[1,1,2]`, and starting offsets are `0,1,2`. Scanning symbols in numerical order writes A at 0, B at 1, C at 2, then D at 3. Each store increments that length's offset. C and D retain symbol order because the scan is stable; no comparison sort is needed.

If lengths arrive in a different symbol order, the same counting process groups them by length while preserving numerical order within each group. The later main loop walks this initialized `work` prefix. Confusing the incremented offsets with their original starting values would lose that connection.

## Entry fields and meanings {#entries}

The main loop tracks a reversed canonical code `huff`, its `len`, the current table width `curr`, and the root bits already dropped. For each symbol it constructs a `code` entry with three fields:

| Field | Interpretation |
| --- | --- |
| `bits` | Number of bits consumed at this table level |
| `op` | Literal/direct value, base plus extra bits, end, invalid, or subtable operation |
| `val` | Symbol value, length/distance base, or subtable offset |

For a literal, `op = 0` and `val` is its byte. A length or distance base uses the operation flags and low extra-bit count. End-of-block and invalid markers have distinct flag patterns. A link uses `op` for its subtable index width and `val` for the offset from the original table base.

Thus, a table entry is not simply a symbol number. Its fields direct both parser control flow and bit consumption. A correctly bounded lookup with the wrong fields can still decode the wrong stream.

## Root replication {#replication}

With root width two, A's one-bit code must occupy both low-bit indices `00` and `10`. B occupies `01`. C and D share `11`, which will become a link. Each A entry consumes one bit, despite the two-bit lookup.

The fill loop accomplishes replication by stepping through indices whose low `len` bits equal `huff`. It counts down in multiples of `2^len` across the `2^root` region. The code walk advances the reversed representation directly; it does not repeatedly reverse the whole input.

<div class="zl-demo-mount"><zlib-demo kind="lookup"><p>In the fixed four-symbol teaching table, AD first uses root slot 10 for A, consuming one bit; then root slot 11 and a one-bit subtable yield D.</p></zlib-demo></div>

## Subtable construction {#subtables}

When `len` exceeds the root width, the constructor looks ahead in remaining length counts to determine a subtable width. It counts free slots under the current root prefix, subtracting codes and doubling when it descends. This avoids allocating a full maximum-depth tree for every prefix.

It advances `next` past earlier tables, increases `used` by `2^curr`, and installs a root link containing the new width and offset. Inside the subtable, replication works after dropping the root's bits. For our example, one extra bit distinguishes C from D.

The root and subtable are parts of one contiguous reservation. Their pointers, offsets, initialized cells, and returned root width must agree. The next caller uses what this call actually returned, not its originally requested width.

## Empty inputs, errors and reservations {#limits}

All-zero lengths take an early branch: write two one-bit invalid entries, return root width one, and advance the table pointer by two. Success here means a table was constructed; trying to decode through it produces an invalid-code result. The accepted one-symbol case similarly requires an explicit invalid slot alongside its valid slot.

For `LENS` and `DISTS`, capacity checks guard reservations of 852 and 592 entries. The inflate state reserves their sum, 1444, in `codes`. These are table-entry counts, not byte counts or alphabet sizes. A separate bound is needed to show every valid format code is accepted; a safe capacity refusal proves only that the constructor can refuse safely.

The `CODES` call has stronger length/root premises: lengths at most seven and a requested root of at least seven leave no subtables and need at most 128 entries. The other types' checks cannot replace those premises. Actual helper domains also include reserved symbols; they must receive the proper invalid interpretations.

This source route is **to confirm** through corresponding execution proofs. Invalid lengths, capacity failure and partial writes remain in scope. Continue with [slow and fast decoding](/sample/decode-copy.html), then [the proof connection](/sample/decode-proof.html#table-content). The [complete table reference](/reference/docs/proof/inftrees.html) states the finer domains and obligations.
