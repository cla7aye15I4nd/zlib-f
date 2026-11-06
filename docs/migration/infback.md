# Moving the infback proofs of the earlier attempt

The earlier attempt proved parts of `inflateBackInit_`, `inflateBack` and `inflateBackEnd` on a different runtime:
typed blocks with cells, a byte-block model, a translation whose loop state was a record threaded through a
fuel-driven loop, and a heap that was compared as a whole. This note says what each family of old theorems states,
whether it moves over unchanged (pure) or has to be stated again on the table-based object heap and the present
translation (memory-dependent), the order of the move, and where it stands.

The honest summary comes first. Almost nothing in the old proofs is free of the old runtime. No old line is copied
unchanged. What is reused is the statement of each theorem and the shape of its proof. The old attempt never proved the
loop over the blocks: its last result was the exit when `in` has no input, and the cases `TYPE` and `STORED` as steps
of a loop that was not closed. It also had no function-level theorem for `LEN` or `TABLE`.

## What the old theorems state

| Old family | What it states | Kind |
| --- | --- | --- |
| Entry checks of `inflateBackInit_` (release string, stream size, parameters) | the three error codes and that nothing changes | memory-dependent, small |
| Memory error and success of `inflateBackInit_` | on allocation failure the state is untouched; on success the new state holds the seven fields the C writes and the stream points to it | memory-dependent |
| `inflateBackEnd` | the four exits: no stream, no state, no `zfree`, success (state freed, pointer cleared) | memory-dependent, small |
| Entry exits of `inflateBack` | no stream or no state gives the stream error | memory-dependent, small |
| End of input at the first pull | `in` returns 0: buffer error, `next_in` null, `avail_in` 0, `out` not called | memory-dependent, needs the call-back contract |
| Input macros (`PULL`, `PULLBYTE`, `NEEDBITS`, `BITS`, `DROPBITS`, `BYTEBITS`) | each refills or consumes bits without changing the remaining bit stream; the bit-buffer arithmetic | arithmetic part is pure; the rest is memory-dependent |
| `ROOM` and the output view | when the window is full it is handed to `out` and refilled; the output so far is unchanged | memory-dependent |
| Window write | storing new bytes at `put` extends the output view | memory-dependent |
| `STORED` | alignment, the length check against its complement, the copy loop in pieces, the exits | the length-field arithmetic and the match with the stored-block decoder are pure; the loop is memory-dependent |
| `TYPE` | reads one and then two bits and selects the next mode; fixed tables are installed | memory-dependent (needs the theorem for `inflate_fixed`) |
| `TABLE` header | the three counts, the range check, the message | memory-dependent |
| `TABLE` code lengths | the permutation table is a bijection of 0..18; the lengths read in order; the zero fill | the permutation facts and the list model are pure; the loops are memory-dependent |
| `TABLE` code-length code | the call of `inflate_table` for the code-length code and its rejection | needs the theorems of `inftrees.c` |
| `TABLE` symbols | decoding of the code-length symbols against the canonical decoder; repeat codes and their limits | the decoder model is pure; the loops are memory-dependent |
| Slow-path lookups | whenever the "fits" test passes, the table entry read agrees with canonical decoding of the real stream (root and sub-table) | pure (about three hundred lines), but stated on the old Huffman model |
| `LEN` | literal, end of block, length and distance decoding, window copy with wrap | not proved in the old attempt |
| `DONE`, `BAD`, default, dispatch | mode selection gives the result codes | memory-dependent, small |
| Safety loop driver | a generic loop lemma: with an invariant and a falling measure the dispatch loop ends without fault | partly pure (the measure argument), mostly tied to the old loop record |
| Leave block | the final `out` call with the rest of the window, the buffer-error rule, restoring `next_in` and `avail_in` | memory-dependent |
| Call-back contract and its witness | the old contract (own block sets, local invariants) and a witness | restated, see below |

## What was done in the order of the move

1. **Entry and exit functions.** Done. `inflateBackInit_`: release-string, size and parameter errors, memory error, success with
   the representation invariant, and a theorem that covers every outcome. `inflateBackEnd`: all exits. `inflateBack`:
   no stream and no state. These follow the proofs of `inflateInit2_` and `inflateEnd` in `inflate.c`, which already
   use the table-based heap. The old statements gave the shape; the proofs are new.
2. **Call-back contract and non-vacuity.** Done. The contract is a structure whose docstring quotes the text of
   `zlib.h`. Two concrete pairs of call-backs satisfy it, and the heap they run on is made by the real `inflateBackInit_`
   from a heap with all static tables.
3. **Exit when `in` has no input.** Done, on the new translation, with a witness on the real initialisation heap.
   This needed the rules for running the monad of the loop, which are reusable for the other cases.
4. **Pure facts.** Open. Bit-buffer arithmetic, the permutation of the code-length order, the stored-block length
   check, and the slow-path lookup lemmas have to be stated against the present format specification and the present
   canonical table theorems of `inftrees.c`, not against the old model. They are independent of the heap and can
   be done in parallel.
5. **Macros on the new heap.** Done: `PULL`, `PULLBYTE`, `NEEDBITS` with the call-back (module `infback.c.macros`) and `ROOM` (module `infback.c.room`). The bit algebra (`BitInv`, `PULLBYTE_succ`, `BITS_run`, `DROPBITS_run`, `BYTEBITS_run`, the loop rule) is the one landed for `inflate.c`; only what differs is new: `PULL` may call `in`, the chunk lives in a block of `in`, and `phi` (bits held, plus bytes left, plus what `in` can still deliver) never grows.
6. **The modes.** `TYPE` is done (module `infback.c.inv`: the loop invariant `LInv`, `TYPE_last`, `TYPE_more`, and the
   message helper `badMode_run`). Open: `STORED`, `TABLE`, `LEN`, then the dispatch loop with its measure (the termination
   measure is `phi`, which needs `InFinite`), the leave block, the safety theorem and the functional theorem. `TABLE` can use
   `inflate_table_safe` and `inflate_table_correct_ret`; `STORED` needs a run lemma for the byte copy.

## What blocks the rest

* **`inflate_fast`.** `LEN` calls it. The present rules allow a callee's specification only as a theorem about the
  translated callee, and no such theorem is listed yet. No assumption is made in its place. `STORED`, the exits and
  the table part do not need it.
* **Table contents.** The listed theorems of `inftrees.c` give safety and the return code, not the contents of the table.
  The slow path reads `table[last.val + ...]` where `last.val` comes from a link entry. Showing that this index is
  inside `codes` needs the shape of the built table. Safety of the lookups depends on a theorem of `inftrees.c` that says
  link offsets stay inside the array.
* **`inflate_fixed`.** Done: it only sets four fields of the state (`inflate_fixed_ok`), so `TYPE` no longer waits for it.
* **Window written by `inflate_fast`.** `inflateBack` passes the output pointer inside the window to `inflate_fast`;
  the specification of `inflate_fast` has to allow that case. The earlier attempt recorded this as the reason it did
  not finish.
* **Finding of the earlier attempt, to confirm.** The source of `case LEN` contains no update of `whave` before the call
  of `inflate_fast`. The earlier attempt reported that, with a window never flushed, `inflate_fast` then accepts
  distances up to twice the output so far and copies stale window bytes where the slow path would reject. This should be
  checked on the present source with a sanitiser before the functional theorem is stated, because it changes what
  "invalid stream gives a data error" can mean for this function.

## Restrictions of the statements, relative to `zlib.h`

* The allocator is the default one (`zcalloc`, `zcfree`) or null: the model has no other.
* The window is a byte block of the heap, with room for `2^windowBits` bytes from the given offset.
* The call-backs do not allocate or free heap blocks, and the input they return is in a byte block that only `in` may
  write. The documented requirement is only that the bytes stay valid and unchanged until the next call.
* For termination the input must be finite: the theorems that follow loops take a measure of what `in` can still deliver
  (`InFinite`). Without it a call-back that never reports the end of input makes `inflateBack` run for ever, which the
  model reports as running out of fuel. `zlib.h` does not promise that `in` ends.
* The call-backs are given by a heap invariant `R` that depends only on their own blocks; this is how "they do not touch
  the stream" is stated pointwise on the tables.

## Theorems that now exist

`inflateBackInit__safe`, `inflateBackInit__ok`, `inflateBackInit__nullstream`, `backInit_witness`,
`inflateBackEnd_ok`, `inflateBackEnd_refused`, `inflateBackEnd_nullstream`, `inflateBack_nullstream`,
`inflateBack_nostate`, `inflateBack_eof`, `inflateBack_eof_witness`, `PULLBYTE_run`, `NEEDBITS_run`, `inFinite_eof`, `ROOM_run`, `badMode_run`, `TYPE_last`, `TYPE_more`, and `inflate_fixed_ok` (in `Zlib.Inftrees.Proofs`), the others in namespace `Zlib.Infback.Proofs`
and listed in the audit file.

## Callee contracts

None is assumed. `inflateBack_eof` does not reach any callee. The theorems for `LEN` and `TYPE` will use the theorems
for `inflate_fast` and `inflate_fixed` once they are listed; until then those cases are not stated.
