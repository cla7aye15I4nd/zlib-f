# Pilot: does the object heap work?

Decision D1 in [overview.md](overview.md) asks which heap model to use. This page reports the first
experiment. The file is `ZlibF/Runtime/Pilot.lean`; it compiles in under half a second and has no
`sorry`. Its theorems are listed in `tests/audit/theorems.txt`.

## What was built

A heap with one table per kind of object, and C structs as Lean records.

| Part | What it is |
| --- | --- |
| `Heap` | three tables: `streams` (z_stream records), `dstates` (deflate_state records), `bytes` (byte arrays). A table maps a block number to an object or to nothing (free) |
| pointer | a byte pointer is a block number and an offset; a struct is referred to by its block number |
| read and write of a field | a read gives a field of the record; a write replaces the record. Nothing else changes |
| `padd` | pointer plus integer, a fault if the result leaves the block (one past the end is allowed) |
| `memcpyB` | a fault unless the two ranges are inside their blocks and the blocks differ |

The function is `flush_pending`: it copies `min(pending, avail_out)` bytes from the pending buffer to
the caller's output buffer and updates six fields in two structs.

## What was proved

> If the stream and its state are present, the output range lies inside the caller's block, the
> pending range lies inside the pending buffer, and the two blocks are different, then
> `flush_pending` runs without a fault. Afterwards the same conditions hold, no stream, state or
> byte block other than the ones it writes has changed, and only the output block changed among the byte blocks.

The invariant has four clauses (the two ranges, the two pointers into the same buffer, and the two
blocks being different). The theorem has seven conclusions: success, the new values of the two records, the invariant, and three frame
statements.

## Measurements

| | Object heap (pilot) | Earlier tagged-cell model |
| --- | --- | --- |
| Lines for the runtime, its lemmas, the translation, the invariant and the theorem | 208 | not comparable (the runtime is shared) |
| Lines of the theorem, with its proof | 74 (the proof body is 67) | `PendingFull.lean` 148 lines and `PendingFlush.lean` 408 lines (both files) |
| Hypotheses of the theorem | 3 (two lookups and the invariant) | 19, mostly "this cell holds this tagged value" |
| Heartbeat overrides | none | none |
| Compile time | 0.4 s | not measured |

Read the comparison with care. The pilot leaves out `_tr_flush_bits` (which the earlier proof
includes), null pointers, read-only blocks, and the allocation oracle. The earlier proof covers all of those.
The pilot shows the shape of the argument, not a final size.

## What the proof looks like

There are no lemmas about "other cells did not change". A write to a record replaces that record,
and the heap tables are updated by `upd`, with two rules: a read of the updated key gives the new value, a read of
any other key gives the old one. The proof is then a straight walk through the function: each step
has one lemma that says what it returns and which table it changes, and the rest is arithmetic on
offsets, closed by `omega`.

The one place that needed work is the arithmetic on `UInt32` and `UInt64` (a subtraction that is
exact only because the minuend is larger). That is the same work as in any model.

## Second function: `updatewindow`

The ring-buffer part of `updatewindow` (everything after the window has been allocated) is translated and
proved too. In the file it is `update2`, split into the two branches of the C code, `uw_big` (`copy ≥ wsize`) and
`uw_small` (the copy goes in one or two pieces).

The theorem `update2_ok` says: if the window invariant W holds (the one of [proof/inflate.md](proof/inflate.md):
`wbits` between 8 and 15, the window block has `2^wbits` bytes, `wsize` is 0 or `2^wbits`, `whave ≤ wsize`,
`wnext < wsize`, and `whave < wsize` implies `wnext = whave`), the caller's buffer is a different block, and
`copy` bytes are available before `end`, then the function does not fault and W holds again. Nothing outside the state record
and the window block changes.

| | Lines |
| --- | --- |
| Translation (`initWin`, `uw_big`, `uw_small`, `update2`) | 37 |
| Invariant W and its small lemmas (`initWin_inv`) | 37 |
| `cpy_step`: one `psub` plus `memcpy`, used three times | 20 |
| `uw_big_ok` | 28 |
| `uw_small_ok` (with `uadd`) | 95 |
| `update2_ok` | 27 |
| Everything for `updatewindow` in the file | 247 |

The proof of the hard branch is a case analysis on the values of `dist` and `copy − dist`, and the arithmetic is closed by
`omega`. The step "the copy and the byte buffer do not interfere" is one lemma, `cpy_step`, and is never repeated.
The invariant W (clause 4, `whave < wsize → wnext = whave`) is what makes the two-piece case and the last case go through, exactly as the
text proof says.

### The allocation of the window

The whole of `updatewindow` is now in the file, including the first part: if there is no window, `ZALLOC` is called, and
a failure returns 1. The heap has three new fields for this: the next unused block number, the number of allocation
calls so far, and an oracle that says which call fails. `alloc` takes the next block number, or fails when the oracle says so.
The extra fact `Fresh` says that no block from the next number on is in use, which is what makes a new block different from
every block the caller has.

`updatewindow_ok` says: if the state satisfies W, or satisfies the "no window yet" condition (`window = none`, `wsize = whave = wnext = 0`),
and the heap is `Fresh`, then the function does not fault and returns 0 or 1. Afterwards the state satisfies the same condition,
the heap is `Fresh` again, and a result of 1 means that the state is unchanged. Streams and all other states are untouched,
and every byte block that existed before and is not the window is unchanged. The caller's buffer is therefore never touched.
Both outcomes of the oracle are covered, since the theorem quantifies over the heap and so over the oracle.

This part is 115 lines. Together `updatewindow` is about 360 lines, the largest function so far.

What this still leaves out: the calls from `inflate` (which must establish the call condition), and the proof that the window
block is freed once by `inflateEnd` (the leak statement).

## Third function: `slide_hash` (a loop, over arrays of any content)

`slide_hash` rescales every entry of `head` and `prev`. `prev` is never cleared, so some entries are garbage; the theorem
`slide_hash_ok` says that for **every** content of the two arrays the function does not fault, applies `m ≥ wsize ? m − wsize : 0` to each
entry, and changes nothing else (the two arrays and the field `slid` only). The loop is a structural recursion on the count, and its
proof is an induction with the heap and the array generalised; `slideArr_ok` is the induction, about 40 lines. This is the case that
showed why "a read of uninitialised memory is a fault" is the wrong rule (`safety.md`, section 3).

## Pointers into a struct, and copying a struct

This was the biggest open risk of the object heap, and it is the part that `inflate_state` needs: an array that is a field of a struct
(`codes[1444]`), pointers into that array (`lencode`, `distcode`, `next`), pointers to static tables (`lenfix`, `distfix`), and
`inflateCopy`, which copies the whole struct and then moves the pointers into the copy.

| Part | How it is modelled |
| --- | --- |
| An array inside a struct | a field of the record (`codes : Array Code`). Copying the struct copies the array, as in C |
| A pointer into that array | a constructor `inState ref idx`: the struct and an index. There is no address |
| A pointer to a static table | `lenfix idx` or `distfix idx`. A store through it is a fault, so the tables are read-only by construction |
| `p + k` | `cadd`: a fault if the result leaves the array; `NULL + 0` is `NULL` |
| `*p`, `*p = c` | `ldC`, `stC`: a fault for null, out of bounds, a dangling struct, or a store into a static table |

Two theorems:

- `fillC_ok`: writing `n` consecutive entries through `inState r i` (the shape of the replicate loop of `inflate_table`) does not fault if
  `i + n` is inside the array, and changes only those entries. The rest of the state and every other state are untouched.
- `inflateCopy_ok`: copying a state does not fault; the copy has the same table; its three pointers point into its own table; and reading
  through them gives exactly what reading through the original pointers gives. The original and all other states are unchanged. The
  hypothesis is the representation-invariant clause "each table pointer is null, points into the state's own `codes`, or points to a static table".

Both went through with short proofs and no lemma about "other cells". The placeholders: the static tables hold dummy entries (only their
sizes matter here), and the copy leaves out the window.

## Decision D1

**Adopted: the object heap** (option (c) of `overview.md`), on the evidence of this pilot: struct fields and a caller
buffer (`flush_pending`), allocation, a ring buffer and an invariant with a case split (`updatewindow`), a loop over arbitrary content
(`slide_hash`), interior pointers and static tables (`fillC_ok`), and copying a struct (`inflateCopy_ok`). What is still open is not a reason to
doubt the choice but work to do: null pointers and read-only byte blocks in the byte tables, whole-struct `memcpy` as a primitive, the
allocation counter used for leak statements, and the `gz*` file functions (`FILE` descriptors, `read`, `write`, `lseek`).

## What this does and does not show

It shows that the object heap is workable for every kind of memory access that `inflate` and `deflate` make. It does not show how large the
proofs of `inflate()` and `deflate()` will be: the longest function so far is `updatewindow`, about 360 lines.

## Next

1. Done (phase C0): the runtime is `ZlibF/Runtime/` on the object heap; the tagged-cell remnants are gone.
2. Done (phase C0): the records and tables of every struct are generated into `Runtime/Schema.lean` ([runtime-schema.md](runtime-schema.md)). The pilot of this page now runs on those records; its theorems are the ones in `tests/audit/theorems.txt` under `Pilot`.
3. Translate every C file into the new runtime, with a differential test per file (`tests/`).
