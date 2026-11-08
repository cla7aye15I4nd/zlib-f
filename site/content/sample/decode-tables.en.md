[The bit-reading example](/sample/input-bits.html#trace) decoded `AD` with a small table: root index `10` returned A and consumed one bit; `11` led to a subtable, where one more bit selected D. Now follow the implementation question left open there: where does that table come from, and how does it agree with the encoder?

In a dynamic block, the encoder sends a [code-length description](/sample/huffman-lengths.html#description). The decoder reads each symbol's length and reconstructs the assignment using the shared **canonical coding** rule: shorter lengths first, then numerical symbol order within each length. Fixed blocks instead use the format's predefined assignment. This chapter develops construction of lookup arrays from lengths; [decoder execution](/sample/decode-copy.html#dispatch) then consumes the entries actually built.

The optimization avoids branching once per code bit. A short code can resolve immediately; a long code can identify a shared prefix before continuing in a smaller subtable. Entries must say both “what is the result?” and “how many bits does this consume?” Otherwise even a lookup that finds A can delete D's first bit.

## First build the small example {#example}

Take symbols A, B, C, D in that numerical order with lengths `[1,2,3,3]`. Canonical assignment gives `A=0`, `B=10`, `C=110`, `D=111`. These are teaching symbols, not a complete DEFLATE block. Request two bits for the first lookup, called the **root** lookup. A longer code will continue in a **subtable**.

Construct the table in this order:

1. Count one symbol of length one, one of length two and two of length three. They exactly fill a binary code tree.
2. Visit A, B, C, D in length order. Give them successive canonical codes.
3. Place A in both root slots whose next bit is 0. The second inspected bit belongs to later input, so either value must give A and consume only one bit.
4. Place B in its root slot. C and D share a root slot; use its third bit to distinguish them in a two-entry subtable.

The [input chapter](/sample/input-bits.html) stores the next bit in the lowest position. Consequently the root indices below are integer spellings, with the next bit on the **right**:

| Root index | Result | Bits consumed here |
| --- | --- | --- |
| `00` | A | 1 |
| `01` | B | 2 |
| `10` | A | 1 |
| `11` | Continue in the subtable | 2 |

Subtable index `0` gives C and `1` gives D, each consuming one further bit. Thus `AD` uses root `10` for A, then root `11` and subtable `1` for D. Now follow how C produces this result, rather than supplying it by assumption.

The input to `inflate_table` is a code length for each symbol, an alphabet kind, a requested first-lookup width, and caller-provided table and scratch storage. Its output is the filled table, the actual first-lookup width, an advanced table pointer and a return code. A zero length means a symbol is unused. An **alphabet** is the set of symbols that this particular table can return. The source labels a table of code-length-description symbols `CODES`, a table of literal/length symbols `LENS`, and a table of distance symbols `DISTS`. The first helps describe the other two tables in a dynamic block. A literal is a byte to output directly; a length and distance describe a history copy.

## Length counts and occupied space {#counts}

[`inflate_table`](/reference/source/ZlibF/Zlib/inftrees.c.html#L243) uses `lens` for input code lengths and `count` for the number of symbols at each length. It clears the counts, then increments `count[lens[sym]]` for each symbol index `sym`. Zero means unused. The shortest and longest nonzero lengths, measured in bits, become `min` and `max`. The first-lookup bit count is called `root`. For our lengths, `min = 1`, `max = 3`, and the requested `root = 2` already lies between them. A request outside that occupied range is moved to its nearest endpoint. A root width of two means four table entries, not two entries.

The constructor then checks whether the lengths can fit. Starting with one available root slot, each depth doubles the free slots and subtracts the symbols placed there. The following is teaching pseudocode for that check, not a C excerpt. Here `l` is a candidate code length in bits, `count[l]` is the number of symbols using that length, and `left` counts unused tree positions at that depth. The maximum depth is 15 because DEFLATE permits at most 15 bits per literal/length or distance code.

```text
left = 1
for each length l from 1 through 15:
    left = 2 * left - count[l]
```

For our example the free counts are `2 - 1 = 1`, then `2 - 1 = 1`, then `2 - 2 = 0`; deeper counts stay zero. Three one-bit symbols would instead give `2 - 3 = -1`: no binary prefix code can fit them.

A negative result is oversubscription and returns `-1`. A positive remainder describes an incomplete code. The source does not accept all such codes: outside the separately handled empty case, a positive remainder is permitted only for non-`CODES` input with maximum length one. The accepted nonempty incomplete case has a single one-bit symbol.

## Offsets and stable symbol order {#ordering}

Lengths alone determine how many codes belong at each depth. Symbols still need a deterministic order within each depth. The scratch array `work` will hold this order; `offs` records the next available position for each length. `offs[1] = 0`, and `offs[l+1] = offs[l] + count[l]` gives each length's starting slot in scratch array `work`.

For lengths `[1,2,3,3]`, the relevant counts are `[1,1,2]`, and starting offsets are `0,1,2`. Scanning symbols in numerical order writes A at 0, B at 1, C at 2, then D at 3. Each store increments that length's offset. C and D retain symbol order because the scan is stable; no comparison sort is needed.

For an input that needs rearranging, lengths `[3,1,3,2]` place B first, D second, then A and C: `work = [B,D,A,C]`. The same counting process groups symbols by length while preserving numerical order within each group. The later main loop walks this initialized `work` prefix. Confusing the incremented offsets with their original starting values would lose that connection.

## Entry fields and meanings {#entries}

Each written cell must tell the consumer both what to do and how much input to remove. Follow A at the root first. Its code is `0`, its full length is one bit, this lookup examines two bits, and no root bits have been removed yet. The main loop names these four quantities `huff = 0`, `len = 1`, `curr = 2`, and `drop = 0`. Here `huff` stores the code with the next input bit in its lowest position; `len`, `curr` and `drop` all count bits. In a subtable, `drop` counts the root bits already accounted for, so the remaining code width is `len - drop`. For each symbol it constructs a `code` entry with three fields:

| Field | Interpretation |
| --- | --- |
| `bits` | Number of bits consumed at this table level |
| `op` | Literal/direct value, base plus extra bits, end, invalid, or subtable operation |
| `val` | Symbol value, length/distance base, or subtable offset |

For a literal, `op = 0` and `val` is its byte. Length and distance codes can identify a range: `val` is its minimum, called the **base**, and extra input bits select an offset above it. For example, base 11 plus one extra bit of value 1 gives length 12. The entry’s `op` carries flag 16 plus the extra-bit count. End-of-block uses `op = 96`. Invalid entries set flag 64 without the end flag 32; other bits can vary for reserved symbols. The empty-table marker is exactly 64. The entry’s `bits` is the code-consumption count, distinct from the reservoir’s total held-bit count. In a `CODES` table, a direct entry instead returns a code-length symbol in `val`. A link uses `op` for its subtable index width and `val` for the offset from the original table base.

Thus, a table entry is not simply a symbol number. Its fields direct both parser control flow and bit consumption. A correctly bounded lookup with the wrong fields can still decode the wrong stream.

## Root replication {#replication}

With root width two, A's one-bit code must occupy both low-bit indices `00` and `10`. B occupies `01`. C and D share `11`, which will become a link. Each A entry consumes one bit, despite the two-bit lookup.

To fill all equivalent lookup indices, the constructor needs a stride in **entries**. Fixing `len - drop` low bits leaves indices spaced by `2^(len-drop)`; the source calls that stride `incr`. The current table has `2^curr` entries; `fill` starts at this size and walks backward by the stride. `here` is the prepared entry and `next` points to this table's first cell. Here is the actual fill loop in `inflate_table`, from [pinned `inftrees.c`, lines 238–244](https://github.com/madler/zlib/blob/757f0527154291bcf6bfbd6396ecde6bedd2db95/inftrees.c#L238-L244):

```c
incr = 1U << (len - drop);
fill = 1U << curr;
min = fill;
do {
    fill -= incr;
    next[(huff >> drop) + fill] = here;
} while (fill != 0);
```

`here` is the completed entry and `next` points to the current table. For A, `len=1`, `drop=0`, `curr=2`, `huff=0`: `incr=2`, `fill=4`. The two iterations store at index 2 (`10`) and index 0 (`00`). Both stores use the same entry consuming one bit. `min` temporarily saves this table's size for advancing to the next table; it no longer means the minimum code length. The code walk then advances the reversed code directly, without repeatedly reversing input.

<div class="zl-demo-mount"><zlib-demo kind="lookup"><p>In the fixed four-symbol teaching table, AD first uses root slot 10 for A, consuming one bit; then root slot 11 and a one-bit subtable yield D.</p></zlib-demo></div>

## Subtable construction {#subtables}

First consider the C and D still unresolved in our example. Each has a three-bit code and shares the first two bits. The root has already inspected those two bits, leaving just the final bit. A two-entry subtable distinguishes them with `0` and `1`; this prefix does not need a table that examines all 15 possible code bits.

In general, a complete code length `len` greater than the root width requires a subtable. The constructor looks forward through the remaining length counts. Each extra bit doubles the free branches; codes at that depth occupy some of them. It chooses enough subtable bits for the codes under this prefix instead of reserving maximum depth for every prefix.

Here `used` counts all entries reserved so far, including the root; it does not count input bits or symbols. The constructor advances `next` past earlier tables, increases `used` by the new table's `2^curr` entries, and installs a root link containing the new width and offset. Inside the subtable, replication works after dropping the root's bits. For our example, one extra bit distinguishes C from D.

Make the addresses concrete for our four-symbol example. The two-bit root occupies `2^2 = 4` entries, at offsets 0 through 3 from the original table base. The one-bit subtable needs `2^1 = 2` entries, so it starts at offset 4 and occupies offsets 4 and 5. After reserving it, `used = 4 + 2 = 6`.

The link must be installed in the root slot selected by the root bits. `mask = (1U << root) - 1` keeps exactly those low bits of `huff`; the resulting root index is named `low`. For `root = 2`, the mask is binary `11`. The constructor installs the root link with these actual statements from `inflate_table`, [pinned `inftrees.c`, lines 290–293](https://github.com/madler/zlib/blob/757f0527154291bcf6bfbd6396ecde6bedd2db95/inftrees.c#L290-L293):

```c
low = huff & mask;
(*table)[low].op = (unsigned char)curr;
(*table)[low].bits = (unsigned char)root;
(*table)[low].val = (unsigned short)(next - *table);
```

Here `*table` still points to the original base; `next` points to the subtable. For the shared C/D prefix, `low = 3` (binary `11`), so these assignments write root entry 3. Its `op = 1` requests one subtable-index bit, its `bits = 2` consumes the root's two bits, and its `val = 4` locates the subtable four entries after the original base. After consuming the root bits, index `0` selects absolute offset `4 + 0 = 4` for C; index `1` selects offset `4 + 1 = 5` for D. Each leaf consumes the final one bit.

The root and subtable are parts of one contiguous reservation. Their pointers, offsets, initialized cells, and returned root width must agree. The next caller uses what this call actually returned, not its originally requested width.

## Empty inputs, errors and reservations {#limits}

All-zero lengths take an early branch: write two one-bit invalid entries, return root width one, and advance the table pointer by two. Success here means a table was constructed; trying to decode through it produces an invalid-code result. The accepted one-symbol case similarly requires an explicit invalid slot alongside its valid slot.

For the default configuration, `LENS` and `DISTS` capacity checks guard reservations of 852 and 592 entries. The inflate state reserves their sum, 1444, in `codes`. These are table-entry counts, not byte counts or alphabet sizes. The pin also has `PKZIP_BUG_WORKAROUND` values 854 and 594; the default constants must not be generalized to that configuration. See [pinned `inftrees.h`, lines 37–57](https://github.com/madler/zlib/blob/757f0527154291bcf6bfbd6396ecde6bedd2db95/inftrees.h#L37-L57). A separate bound is needed to show every valid format code is accepted; a safe capacity refusal proves only that the constructor can refuse safely.

The `CODES` call has stronger length/root premises: lengths at most seven and a requested root of at least seven leave no subtables and need at most 128 entries. The other types' checks cannot replace those premises. Actual helper domains also include reserved symbols; they must receive the proper invalid interpretations.

One specific obligation is that the helper assumes every input length is in `0..15` before indexing `count`; it does not check this itself. The caller must establish that bound. Malformed compressed descriptions remain in the public safety domain, while rejected code sets, capacity failure and partial writes need their precise helper outcomes. The installed table now passes to [decoder execution](/sample/decode-copy.html#dispatch): entry operations select a literal, length or end, and consumption counts advance the same input bits. [The table-content argument](/sample/decode-proof.html#table-content) follows that handoff, connecting the cells read by the consumer to those actually written by construction. The [complete table reference](/reference/docs/proof/inftrees.html) states the finer domains and obligations.
