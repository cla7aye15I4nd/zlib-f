# Search for an overlay violation in dynamic blocks (fact F9)

`pending_buf` holds the compressed output from offset 0 and the recorded symbols from offset
`lit_bufsize`. `compress_block` must never write a pending byte at or beyond the next unread
symbol (F9, `docs/proof/trees.md`). For fixed and stored blocks and for dynamic blocks at
`memLevel` 5 to 9 this is proved (`ZlibF/Proof/trees.c.universal-*.lean`). For dynamic blocks at
`memLevel` 1 to 4 no argument is known (`docs/progress.md`).

`run.sh` builds the patched zlib copy, adds two statements to its `trees.c` that record the gap
`lit_bufsize + sx - pending` (before the first symbol and after each symbol), and runs
`search.c`: simulated annealing over blocks of valid symbols, recorded with the real
`_tr_tally` macros and flushed with the real `_tr_flush_block`. A negative gap would be a symbol
overwritten before it is read. The upstream checkout is never modified.

```bash
ZLIB_SRC=$PWD/zlib bash tests/goals/overlay/run.sh 2000000 1
```

Results on 2026-11-11 (2,000,000 steps per memLevel, windowBits 15): smallest gap 58 bytes at
`memLevel` 1, 161 at 2, 404 at 3, 906 at 4. No violation. This is evidence about the blocks
visited, not a proof.
