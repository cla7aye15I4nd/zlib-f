# deflateCopy after deflateResetKeep: longest_match follows an uninitialised prev slot

Status: reproduced on the pinned C with AddressSanitizer (arm64 macOS; x86_64 Linux is still to be
run). A memory error: `longest_match` reads outside the window. It needs a direct call of
`deflateResetKeep`, which `zlib.h` lists among the undocumented functions. Not reported upstream.

Mechanism, in the pinned source:

1. `deflateResetKeep` keeps the window and the hash and drops the lookahead. The positions
   `strstart - 2` and `strstart - 1` stay chain heads (see
   [deflate-resetkeep-stale-hash](../deflate-resetkeep-stale-hash/README.md)).
2. A following `deflate(Z_BLOCK)` sets `insert = 2`: those two positions now wait for insertion.
3. `deflateCopy` copies `prev` only below `strstart - insert` (`deflate.c:1383`). The `prev` slots
   of the two heads are fresh, uninitialised memory in the copy.
4. On the copy, `deflateParams(Z_RLE)` and a `deflate(Z_SYNC_FLUSH)` with no input end in
   `deflate_rle`, which sets `insert = 0` (`deflate.c:2177`). `fill_window` re-inserts the waiting
   positions only while `insert` is nonzero, so the two slots stay uninitialised.
5. After `deflateParams(Z_DEFAULT_STRATEGY)`, an input that starts with the three bytes at
   `strstart - 2` makes `deflate_slow` insert `strstart` under the same key and call
   `longest_match` on the old head. The loop reads the uninitialised `prev` slot as the next
   candidate and compares the window at that position.

`repro.c` (the same driver as [tests/regression/deflate-copy-pending-prev](../../../tests/regression/deflate-copy-pending-prev/README.md))
fills fresh memory with the 16-bit value 1030, so the candidate lies just past the 1024-byte window
(`windowBits` 9) and AddressSanitizer reports the read (`deflate.c:1511`). With other memory
content the candidate is whatever the slot holds: up to 65535, far outside a small window.

Without step 1 no head waits for insertion in the histories inflate batch 1 checked (4.6 million
states, evidence, not proof). Without step 3 the slots hold the values written when the positions
were inserted. Without step 4 `fill_window` inserts the two positions, and so rewrites their slots,
before any `longest_match`.

Effect on the proof: the exclusion of a direct `deflateResetKeep` from the deflate stream domain
(`docs/deviations.md`) cannot be removed: with it, `deflate` can read outside the window. A
positional hash-chain invariant that admits `deflateResetKeep` is false after step 4.
