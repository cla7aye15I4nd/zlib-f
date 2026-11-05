# `inflate_table`

Source: `zlib/inftrees.c`. Specification: `I-it-*` in [../spec/internal.md](../spec/internal.md)
and the canonical code rules `F-code-*` in [../spec/format.md](../spec/format.md).

This is the hardest function of the decoder for the proofs. It has seven loops, indexes arrays
with computed values, and writes a table whose size depends on the data. The argument is a
statement about numbers; it does not mention the heap.

## The idea in short

The table maps the next bits of the input to a symbol. A canonical Huffman code hands out codes in increasing order, so the code of each symbol is a number that fits in its length exactly when the lengths obey the Kraft inequality. The function checks that first. The decoder indexes the table with the code written backwards, and one counter, `huff`, walks through the backwards codes in order. A short code fills several entries of the first-level table. A long code gets a second-level table whose size is chosen so that every code below that prefix fits. Because the lengths form a complete code, every entry is written exactly once. The only table that could outgrow its space is guarded by an explicit size check, so no argument about the largest possible table is needed.

## 1. Set-up

Input: lengths `lens[0 .. n-1]` (here `n = codes`), each in `[0, 15]`; a table type
(`CODES`, `LENS`, `DISTS`); a requested root width `*bits`.

Definitions, for `l` from 1 to 15:

- `c_l` = the number of symbols with length `l`. `m = Σ c_l` is the number of coded symbols.
- `max` = the largest `l` with `c_l > 0`; `min` = the smallest. (`m = 0` is handled separately.)
- `root` = `*bits`, lowered to `max` if larger, then raised to `min` if smaller. So `min ≤ root ≤ max`
  and `1 ≤ root ≤ 15`.
- `B_l` = `Σ_{j<l} c_j 2^{l-j}`. Then `B_1 = 0` and `B_{l+1} = 2 (B_l + c_l)`. This is `code_start[l]`
  of the specification: the first canonical code of length `l`.
- `left_l` = `2^l − B_l − c_l`. This is the number of unused code values of length `l` after all
  codes of length at most `l`.

`rev_l(v)` is the bit-reversal of the `l`-bit number `v`.

The i-th symbol (counting from 0, in increasing symbol order) with length `l` has canonical
code `v = B_l + i`, an `l`-bit number, sent most significant bit first. A decoder that reads
bits least significant first indexes the table by `rev_l(v)`.

## 2. Statement

**Theorem T1 (safety).** Assume `I-it-pre-lens`, `I-it-pre-codes`, `I-it-pre-work`,
`I-it-pre-table`. Then `inflate_table` terminates, every array access is in bounds, no shift is
invalid, and no unsigned value is used in a way that wraps. It returns 0, -1 or 1. If it
returns 0, every write is inside `[*table, *table + used)` with `used` at most 128, 852 or 592
(`CODES`, `LENS`, `DISTS`).

**Theorem T2 (complete tables).** If it returns 0 and `m > 0`, then every entry of the root table
`[0, 2^root)` and every entry of every sub-table has been written, and every link in the root table
points to a sub-table that lies inside `[*table, *table + used)`.

T2 is what makes the later reads in `inflate` and `inflate_fast` safe: they index the table by
`hold & mask` without checking that the entry exists.

## 3. Lemma 1: what the two checks give

The Kraft check computes `left` for `l = 1 .. 15` and returns -1 if it becomes negative.
By induction `left` after step `l` equals `left_l` (the recurrence is `left_{l} = 2 left_{l-1} − c_l`,
`left_0 = 1`). So when the function goes on:

(a) `left_l ≥ 0` for every `l`, that is `B_l + c_l ≤ 2^l`: the last code of each length fits in
`l` bits. In particular canonical codes of length `l` are numbers below `2^l`.
(b) At the end, `left_15 = 0` (complete) or `left_15 > 0` (incomplete). The function returns -1 for
an incomplete code unless `type ≠ CODES` and `max = 1`. With `max = 1`, `c_1 ≤ 2` by (a) and
`c_1 ≥ 1`; `left_1 = 2 − c_1 > 0` means `c_1 = 1`. So the only incomplete code that survives is
**one symbol of length 1**.

## 4. Lemma 2: the sort writes inside `work`

`offs[1] = 0` and `offs[l+1] = offs[l] + c_l`, so `offs[l] = Σ_{j<l} c_j` (here for `j ≥ 1`). It is at most
`m ≤ n`. The sorting loop writes the i-th symbol of length `l` to `work[offs[l] + i]`, where
`i < c_l`, hence to an index below `offs[l] + c_l ≤ m ≤ n`. So all writes are inside `work`
(`I-it-pre-work`), and distinct symbols get distinct slots. After the loop `work[0 .. m-1]` holds
the coded symbols ordered by (length, symbol), and nothing else is read from `work` (Lemma 7).

## 5. Lemma 3: `huff` is the reversed canonical code

Claim: at the start of each iteration of the main loop, with current symbol `work[sym]` of length
`len`, the variable `huff` equals `rev_len(v)` where `v` is the canonical code of that symbol, and
`huff < 2^len`.

*Base.* `sym = 0`, `len = min`, `huff = 0`. The first code of length `min` is `B_min = 0`
(no shorter codes), and `rev(0) = 0`.

*Step, same length.* The update computes `rev_len(v + 1)` from `rev_len(v)`:
`incr` starts at bit `len − 1` (the top bit of `huff`, which is the lowest bit of `v`). The loop
`while (huff & incr) incr >≥ 1` walks down through the top bits of `huff` that are 1, which are
the trailing ones of `v`. If it stops at a position with `incr ≠ 0`, that bit of `huff` is 0 (a
trailing zero of `v`, the lowest zero bit). `huff &= incr − 1` clears everything above and at
that position, `huff += incr` sets it, giving the bits of `v + 1`. If it runs out (`incr = 0`), `v`
was all ones, `v + 1 = 2^len`, and `huff = 0`.

*Step, longer length.* The next symbol has length `len' > len` (all lengths between have count 0
as far as codes remaining are concerned). The canonical code of its first symbol is
`(v + 1) × 2^{len' − len}` (the recurrence `B_{l+1} = 2 (B_l + c_l)` applied repeatedly with zero
counts). Appending zeros to `v + 1` as low bits means putting zeros as the high bits of the
reversed number: `rev_{len'}((v+1) 2^{len'−len}) = rev_len(v + 1) = huff`. So `huff` keeps its value
and is now read as a `len'`-bit number. ∎

*Consequence (end).* After the last code of length `max` the loop stops. For a complete code the
last code is `B_max + c_max − 1 = 2^max − 1` (all ones), because `left_max = 0`. Then `huff` is
all ones, the increment runs out, and `huff = 0` at the exit. For the one-symbol incomplete code,
`v = 0`, `len = 1`, `huff` becomes 1 at the exit.

## 6. Lemma 4: root-table writes are in range

While `len ≤ root`, `drop = 0` and `curr = root`. A write is `next[huff + fill]` where `fill` runs
through `2^root − 2^len, 2^root − 2·2^len, ..., 0` (`incr = 2^len`, `fill` starts at `2^root`, and
`2^len` divides `2^root` since `len ≤ root`). With `huff < 2^len` (Lemma 3) each index is at most
`huff + 2^root − 2^len < 2^root`. So writes are inside `[next, next + 2^root)`, and
`next = *table` here. The first `used = 2^root` entries are the root table. The unsigned
subtraction `fill −= incr` never wraps, because `fill` is a multiple of `incr` and ends at 0. ∎

## 7. Lemma 5: sub-table sizing

When the next code has length `len > root` and a new root prefix, the function opens a
sub-table. Let `p = huff & mask` (the low `root` bits of `huff`, which are the first `root` bits of the
code, in reading order). Let `d = drop = root`. Canonical codes with the same prefix `p` are
consecutive in the sorted order (consecutive integers with the same top `root` bits), so they form a
block `T`.

Claim: the loop sets `curr` so that **every** code in `T` has length at most `d + curr`, and
`curr ≥ len − d`.

*Proof.* Let `l0 = len`. Before the loop, `curr = l0 − d` and `left = 2^curr`: the number of
tree nodes at depth `l0` below the prefix `p`. All shorter codes have been used (their `count` is 0
after they were entered), and `count[j]` for `j ≥ l0` is the number of remaining codes of length `j`.
Each pass subtracts `count[curr + d]`, the remaining codes at depth `curr + d`, from `left`. The
remaining codes of one depth are consecutive in the sorted order and start at the beginning of
`T`'s block. If there are fewer of them than free nodes (`left > 0` after the subtraction), they
all lie below `p`, so none of them belongs to a later prefix and `left` is still the exact number of
free nodes below `p`. The function then increases `curr` and doubles `left` (each free node has two
children at the next depth). The loop stops when `left ≤ 0`: the remaining codes at this depth are at least as many as the
free nodes, so every free node below `p` is a code of this depth, and nothing can be longer. Or it
stops because `curr + d = max`, and no code is longer than `max`. Either way, no code in `T` is
longer than `d + curr`. And the first code of `T` has length `l0 = d + (l0 − d) ≤ d + curr`. ∎

*Consequence.* For every code of `T`, `len − drop ≤ curr`. The write loop uses `incr = 2^{len − drop}`
and `fill = 2^curr`: `2^{len−drop}` divides `2^curr`, `fill` ends at 0 without wrapping, and every
index is `(huff >> drop) + fill ≤ (2^{len−drop} − 1) + 2^curr − 2^{len−drop} < 2^curr`, since
`huff < 2^len` gives `huff >> drop < 2^{len−drop}`. Writes are inside `[next, next + 2^curr)`.

## 8. Lemma 6: capacity

`used` starts at `2^root` and grows by `2^curr` for each sub-table. The pointer `next` always
equals `*table + (used before this table)`. So a table being written lies in `[*table, *table + used)`.

- `LENS`, `DISTS`: the function checks `used > ENOUGH_x` right after the root table is reserved,
  and again after every `used += 2^curr`, before any write to the new table and before the link is
  stored. If the check fails it returns 1. So whenever a write happens, `used ≤ 852` (`LENS`) or
  `≤ 592` (`DISTS`), which is what `I-it-pre-table` provides.
- `CODES`: no check. By `I-it-pre-lens` every length is at most 7, so `max ≤ 7`, and the caller
  requests `*bits = 7 ≥ max`. So `root` is lowered to `max`, and `len ≤ max = root` for every
  code. No sub-table is ever opened, `used = 2^root ≤ 128`, and every write is in the root
  table (Lemma 4). ∎

**Remark.** The numbers 852 and 592 come from an exhaustive search. That search shows that a
*valid* code never trips the check. The proof of safety does not need it: a table that would not fit
is rejected. The search matters for correctness (valid input is never rejected), not for safety.

The link written for a sub-table is `(*table)[low]` with `low = huff & mask < 2^root ≤ used`, an
existing root entry; its `val = next − *table ≤ used`, which fits in 16 bits.

## 9. Lemma 7: the other reads

- `count[lens[sym]]` in the counting loop: index `lens[sym] ≤ 15`, from `I-it-pre-lens`.
- `count[len]`, `count[curr + drop]`: `len ≤ 15`; `curr + drop < max ≤ 15` by the loop condition.
- `lens[work[sym]]` (after `sym++`, when `count[len]` reached 0 and `len ≠ max`): some remaining code has
  length greater than `len` (namely a code of length `max`), so `sym < m`, and `work[sym]` was written by Lemma 2.
  `work[sym]` at the top of the loop: each iteration handles one code, and the loop ends exactly
  after `m` iterations, so `sym < m` there too.
- `base`, `extra` tables: for `LENS` the branch that reads them has `work[sym] ≥ 257`, index
  `work[sym] − 257 ≤ 287 − 257 = 30`, and `lext`, `lbase` have 31 entries. For `DISTS`, index
  `work[sym] ≤ 31` and `dext`, `dbase` have 32 entries. Both use `I-it-pre-codes`. For `CODES` the
  branch is not taken because `work[sym] ≤ 18 < 19 = match − 1`, so the null `base` and `extra` are never
  dereferenced.
- Shifts: `1U << root`, `1U << len` with `root, len ≤ 15`; `1U << (len − 1)` with `len ≥ 1`;
  `1U << (len − drop)`, `len − drop ≥ 1` once `drop = root` and `len > root`; `1 << curr` with
  `curr ≤ 14`. None is invalid.
- Termination: the main loop does exactly `m` iterations; `while (huff & incr)` lowers `incr`
  at least by one bit per pass and stops at 0; the look-ahead loop raises `curr` while
  `curr + drop < max`; the counting, sort and Kraft loops run over fixed ranges.

## 10. Proof of T2 (complete tables)

Assume the function returns 0 and `m > 0`.

*Complete code.* By Lemma 1 (b) the Kraft sum is 1: the leaves, as intervals of the code space
`[0, 1)` (a code of length `l` takes an interval of width `2^{-l}`), partition `[0, 1)`.

- *Root table.* The root entry `p` (an interval of width `2^{-root}`) lies in exactly one leaf, or
  contains several. If a leaf of length `l ≤ root` contains it, the loop writes `p` while
  replicating that leaf (Lemma 4: the indices written are exactly those congruent to `huff` modulo
  `2^l`, which are the `2^{root−l}` entries whose first `l` bits equal the code). If instead
  the entry contains leaves longer than `root`, the sub-table for that prefix is opened (the test
  `(huff & mask) ≠ low` fires on the first such code) and the link is stored at `p`.
- *Sub-table.* Repeat the argument inside the sub-table for prefix `p`, with width `2^{-(root + curr)}`:
  by Lemma 5 every leaf below `p` has length at most `root + curr`, and the leaves partition the interval of `p`, so the
  `2^curr` entries are each inside exactly one leaf, which wrote them (Lemma 5, consequence).
- *No overlap,* so there is no write that is later overwritten with another meaning: leaves are
  disjoint.
- *No tail write.* `huff = 0` at the end (Lemma 3), so the final `if (huff ≠ 0)` does nothing.

*Incomplete code (one symbol, length 1).* `root = 1`, entry 0 is written by the loop, entry 1 by the
tail (`huff = 1`, index `1 < 2^root`), as an invalid marker.

*No symbols* (`m = 0`). The function stores two invalid entries, `*bits = 1`, and returns 0; the
table has two entries written. (T2 is then about those two entries.)

*Links.* A link `val = next − *table` and width `curr` describes the sub-table `[next, next + 2^curr)`,
which lies in `[*table, *table + used)` by Lemma 6. ∎

## 11. Status

Proved on paper. The Lean proof splits as follows: Lemmas 1, 3, 5 are statements about numbers
and live in `ZlibF/Math/` (no heap). Lemmas 2, 4, 6, 7 combine them with the runtime's access
rules. T2 is stated over the heap after the call and is used by the `inflate` proofs.
