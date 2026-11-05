# `inflate_fast` (inffast.c)

Specification: `I-if-*` in [../spec/internal.md](../spec/internal.md). Tables come from
[inftrees.md](inftrees.md) (Theorem T2). The window comes from [inflate.md](inflate.md) (invariant W).

## The idea in short

The fast loop is safe because of two margins that the C code chooses. It stops when fewer than 6 input bytes or fewer than 258 output bytes remain, and one trip around the loop never reads more than 6 bytes or writes more than 258. A case check on the bit count shows that a seventh read cannot happen. A copy from the window splits into three cases, according to where the ring buffer wraps. A check made just before the copy (the distance may not exceed the number of bytes the window holds) puts every index inside the window.

## 1. Set-up

On entry the function copies the stream into locals:

```
in   = next_in             last = in + (avail_in − 5)
out  = next_out            end  = out + (avail_out − 257)
beg  = out − (bytes this inflate() call has already produced)
hold = state.hold  (a 64-bit number)      bits = state.bits
```

By `I-if-pre-room`, `avail_in ≥ 6` and `avail_out ≥ 258`, so `last ≥ in + 1` and
`end ≥ out + 1`: forming these pointers is valid. `beg` is the start of the output buffer of the
current `inflate` call, which is also in the buffer. Write `in0`, `out0` for the entry values.
The loop is

```
do { …one symbol… } while (in < last && out < end);
```

## 2. Invariants of the loop

At the top of each iteration:

- **(I1)** `in0 ≤ in ≤ in0 + avail_in`. Moreover `in < last` means `in ≤ in0 + avail_in − 6`.
- **(I2)** `out0 ≤ out` and `out < end` means `out + 258 ≤ out0 + avail_out`.
- **(I3)** `hold < 2^bits` and `bits ≤ 30`, and `bits < 8` at the first iteration (`I-if-pre-bits`).
- **(I4)** `beg ≤ out` and everything in `[beg, out)` has been written by this call.

## 3. Lemma A: bit buffer bounds

There are four places that add bytes, each guarded:

| Site | Guard | Adds | `bits` afterwards |
| --- | --- | --- | --- |
| R1, start | `bits < 15` | 2 bytes | between 16 and 30 |
| R2, length extra | `bits < op` (`op ≤ 5`) | 1 byte | at most 12 |
| R3, before distance | `bits < 15` | 2 bytes | between 16 and 30 |
| R4, distance extra | `bits < op` (`op ≤ 13`), twice | 1 byte each | at most 28 |

So `bits ≤ 30` always, and `hold < 2^30` fits in 64 bits. Every shift `byte << bits` uses
`bits ≤ 30 < 64`. Every shift `hold >> k` and `1U << k` has `k ≤ 15`, because `k` is a code
length (at most 15), a first-level width (at most 9), or `op & 15`.

**No underflow of `bits`.** Subtractions `bits -= op` are safe if `bits ≥ op` at that point.

- Code lookup: after R1 `bits ≥ 15`; a whole code, first level plus second level, has length
  at most 15 (the maximum code length). So `bits ≥ code length`. The second lookup, for the
  distance code, is preceded by R3, which gives `bits ≥ 15` again.
- Length extra bits: after the code, `bits ≥ 0`. If `bits < op` then R2 adds 8, so
  `bits ≥ 8 ≥ 5 ≥ op`.
- Distance extra bits: after the code, `bits ≥ 0`. Two possible additions give `bits ≥ 16 ≥ 13 ≥ op`.

Without these facts an unsigned wrap would make `bits` huge and the next `byte << bits` undefined.
This is the reason the refills are written the way they are.

## 4. Lemma B: at most 6 bytes are read per iteration

Let `R1 ∈ {0,2}`, `R2 ∈ {0,1}`, `R3 ∈ {0,2}`, `R4 ∈ {0,1,2}` be the number of bytes read at the
four sites in one iteration. A priori `R1 + R2 + R3 + R4 ≤ 7`. We show that 7 cannot happen.

Suppose `R1 = 2`, `R2 = 1`, `R3 = 2` and `R4 = 2`.

1. After R1, `bits ≥ 16`. After the length code (at most 15 bits), `bits ≥ 1`.
2. `R2 = 1` needs `bits < op ≤ 5` at that point. After adding 8 and removing `op ≤ 5` extra
   bits, `bits ≥ 1 + 8 − 5 = 4`.
3. `R3 = 2` adds 16: `bits ≥ 20`. After the distance code (at most 15 bits), `bits ≥ 5`.
4. `R4 = 2` needs `bits < op ≤ 13` even after the first added byte, that is
   `bits + 8 < 13`, so `bits < 5`. This contradicts step 3.

So the total is at most 6. Since `in < last` gives `in ≤ in0 + avail_in − 6`, six reads at
`in, …, in + 5` are all inside `[in0, in0 + avail_in)`. **The margin `− 5` in `last` is exactly
tight.** ∎

## 5. Lemma C: at most 258 bytes are written per iteration

A literal writes 1 byte. A match writes `len` bytes with `len` = base + extra from the length table:
the maximum is 258 (code 285, no extra bits; every other code gives at most 257). By (I2),
`out + 258 ≤ out0 + avail_out`. ∎

## 6. Lemma D: table lookups are in range

`here = lcode + (hold & lmask)` where `lmask = 2^lenbits − 1` and the root table has `2^lenbits`
entries, all written (T2). An entry that is not a literal, a base value, an end of block or an invalid marker is a link to a
second level: `lcode + here->val + (hold & (2^op − 1))`. T2 says that the sub-table that `val` and
`op` describe lies inside the table and that all its entries are written. The same holds for `dcode`.
A `goto dolen` or `goto dodist` repeats the lookup at most once, since a second-level
entry is never a link.

## 7. Lemma E: the match copy

Let `done = out − beg`, the number of bytes produced by this `inflate` call so far; by (I4) they
are all written. Let `dist` be the decoded distance (at least 1) and `len` the length (3 to 258).

**Case 1: `dist ≤ done`.** Then `from = out − dist ≥ beg`. The loop copies `len` bytes,
`from[k] → out[k]` for `k = 0 … len−1`. The byte `from[k] = out[k − dist]` lies at index
`k − dist < k` of the output, so it has been written, either before the copy or at an earlier
step `k − dist` of this copy. Reads are valid, and writes are within Lemma C. The unrolled loop copies 3
bytes per pass while `len > 2` and then 1 or 2 bytes. The first pass runs with `len ≥ 3` (the
minimum length is 3), so no step runs past `len`.

**Case 2: `dist > done`.** Let `op = dist − done ≥ 1`: the number of bytes that lie before this call's output and so must come from
the window. The check `op > whave` sends the stream to `BAD` (the default build has `sane = 1`)
and leaves the loop. After it, `1 ≤ op ≤ whave ≤ wsize`. Because `whave ≥ 1`, the window is
allocated and has `wsize` bytes (`I-if-pre-window`). The code has three sub-cases.

| Sub-case | Condition | First source | Check |
| --- | --- | --- | --- |
| (i) | `wnext = 0` | `window + wsize − op` | index `wsize − op ≥ 0`. Copies `op` bytes up to index `wsize − 1` if `op < len`, else `len` bytes ending before `wsize` |
| (ii) | `0 < wnext < op` | `window + wsize + wnext − op` | index `≥ wnext ≥ 0` and `< wsize`. Copies `op − wnext` bytes to the end of the window; then, if bytes remain, copies from `window` index 0: `min(wnext, len)` bytes |
| (iii) | `wnext ≥ op` | `window + wnext − op` | index `≥ 0`. Copies `op` bytes ending before `wnext`, or `len` if shorter |

After the window part, the rest of the match comes from the output: `from = out − dist` at the new `out`
(= the old `out` plus `op` bytes copied) equals `beg`. By the same argument as Case 1, the
reads stay inside `[beg, out)`. The loops `do { … } while (--op)` run with `op ≥ 1`: in (i) and (iii) `op ≥ 1`;
in (ii) the loop count is `op − wnext ≥ 1` and the second count is `wnext ≥ 1`. No count is
zero, so `--op` never wraps. ∎

*Remark.* If `whave < wsize` then `wnext = whave` (`I-uw-inv`), so `op ≤ whave = wnext`, and only
(iii) occurs. Case (ii) needs a full ring (`whave = wsize`). This is not needed for safety, but it
confirms that every window byte read has been written.

## 8. The exit

```
len = bits >> 3;  in −= len;  bits −= len << 3;  hold &= (1U << bits) − 1;
```

Let `B` be the number of bytes read by this call, so `in = in0 + B`. Each read adds 8 bits and
the decoding removes bits, so the final `bits` is at most `bits_entry + 8B < 8 + 8B` by
`I-if-pre-bits`. Hence `len = bits >> 3 ≤ B`, so `in − len ≥ in0`: the pointer does not go
before the start of the input. Afterwards `bits < 8`, `1U << bits` is valid, and `I-if-post` holds.
If the caller's `bits` were 8 or more on entry, `len` could exceed `B` and `in` would point before the
buffer. That is the reason for `I-if-pre-bits`.

## 9. Termination

Each iteration writes at least one byte (a literal writes 1, a match at least 3) or leaves the
loop (end of block, error). `out < end` bounds the number of iterations by `avail_out`. ∎

## 10. What `I-if-pre-bits` requires of the caller

`inflate` calls `inflate_fast` in mode `LEN`, with `have ≥ 6` and `left ≥ 258`. It must keep
`bits < 8` in that mode. **To confirm.** The natural argument is that `NEEDBITS(n)` stops as soon
as `bits ≥ n`, so after the matching `DROPBITS(n)` fewer than 8 bits are left. That argument needs
the transitions into `LEN` (from `CODELENS`, `LENEXT`, `DISTEXT`, `MATCH`, and the entry from
`TYPE` for fixed blocks) to be checked one by one. This is the one step of this page that the Lean
proof must check against the mode transitions of `inflate()`.

## Status

Proved on paper. One step **to confirm** in Lean: the entry condition `bits < 8` (section 1.10 below), which needs a proof over all mode transitions of `inflate()`.
