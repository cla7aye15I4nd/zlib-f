# Migrating the proofs of `inflate()`: the table modes, the trailer and the epilogue

Companion of `inflate.md`. Modules: `inflate.c.main.check0` (helpers), `.check` (`LENGTH`, `CHECK`), `.table` (`TABLE`),
`.table2` .. `.table6` (`LENLENS`), later `.table7*` (`CODELENS`) and `.leave*` (`inf_leave`).

## What was reused from the earlier attempt

| old file | what | new |
| --- | --- | --- |
| `InflateTables.lean` (1161 lines) | the statement of `LENLENS`: `M = min (ncode - have) (|S| / 3)` groups of 3 bits, `lensRead`, `lensZero`, `Good3`, the two loops, the exits | same statement and loop structure re-proved on records (`ll1_run`, `lz_run`, `llTail_run`, `inflate_LENLENS_run`); `grp`, `lensRead`, `lensZero`, `Good3` re-stated on arrays |
| `InflateCheck.lean`, `InflateCheckStep.lean` | trailer: `total_out`, `total`, check update, byte-swap compare | `inflate_CHECK_run`, `inflate_LENGTH_run` |
| `InflateBits.lean` | macros | not needed: the sibling's `NEEDBITS_run` etc. are used |

The memory part is new: the heap is `setI h zs (record)`; results are exact heaps, never equalities of whole tables other
than through `setI` (`tcSetI_same` is used only to start a loop).

## Statements and preconditions

* `inflate_TABLE_run`: exact result, any state; error "too many length or distance symbols".
* `inflate_LENLENS_run`: needs `have <= ncode <= 19` and `Good3 lens have` (what earlier iterations stored); both are
  invariants of mode `LENLENS` established by `TABLE` (`ncode = BITS(4)+4 <= 19`) and by the loop itself.
  The `inflate_table(CODES)` call is covered by `inflate_table_safe` and `inflate_table_correct_ret`; the position of `next`
  and the value of `lenbits` after the call are left as `u <= 128` and `lb` (their relation to the table is the content theorem).
* `inflate_CHECK_run`: needs `StaticsOK` (crc tables) and, when the check is updated, that `put` addresses a byte block with the
  `out` bytes written by this call before it (`PutAt`). The Adler value is the specification's unless `out = 1` and the old check
  is not canonical.
* No theorem assumes `inflate_table_correct_table`.

## Open (what `CODELENS` and `LEN` need from the table content)

`CODELENS` reads `codes[BITS(lenbits)]`. Its safety needs `lenbits <= 10` and every root entry `bits <= 15` (else `NEEDBITS` /
`PULLBYTE` would shift by >= 64: a real fault of the model). That is exactly a consequence of `inflate_table_correct_table`
for the `CODES` table; `CODELENS` will be stated relative to that root bound as a mode invariant, and the composition
`LENLENS -> CODELENS` waits for the content theorem.
