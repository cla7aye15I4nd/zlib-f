# deflateCopy after deflateResetKeep: longest_match follows an uninitialised prev slot

Status: confirmed on the pinned, unmodified C on x86_64 Linux: AddressSanitizer reports the read
outside the window, and valgrind reports the use of the uninitialised `prev` slot with the default
allocator ([report](../../../tests/regression/deflate-copy-pending-prev/report.txt)); the same
AddressSanitizer report on arm64 macOS. A memory error: `longest_match` reads outside the window.
It needs a direct call of `deflateResetKeep`, which `zlib.h` lists among the undocumented
functions. Not reported upstream.

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
content the candidate is whatever the slot holds: up to 65535, far outside a small window. With the
default allocator (`repro plain`) valgrind reports the uninitialised value in the loop test of
`longest_match` (`deflate.c:1555`).

Without step 1 no chain head waits for insertion: this is a theorem of the deflate invariant `DInv`
(`DInv.heads_inserted` and, at level 0 with one pending slide, `DInv.slid_heads_inserted`,
`ZlibF/Proof/deflate.c.universal-heads.lean`): every nonzero `head` entry is below
`strstart - insert`. `DInv` holds after every history of the deflate stream domain, which has no
direct `deflateResetKeep` (`reachable_inv`, under the hypotheses of
`Goal.deflate_sequence_safety`). With two or more pending slides (level 0) the invariant says nothing
about the tables, and `deflateParams` clears them before a nonzero level runs. Inflate batch 1's
real-C checker agrees on 4.6 million states (evidence, not proof). Without step 3 the slots hold the values written when the positions
were inserted. Without step 4 `fill_window` inserts the two positions, and so rewrites their slots,
before any `longest_match`.

Releases. Both ingredients are recent upstream changes. `deflateCopy` copies `prev` only below the
frontier since commit 8404590 ("Copy only the initialized deflate state in deflateCopy",
2026-01-10), first released in 1.3.2; 1.3.1 copies all `w_size` entries. `deflateResetKeep` drops the
lookahead since commit 1e4178b ("Fix deflateResetKeep() when used in the middle of a stream",
2026-11-02), first released in 1.4. With this driver (AddressSanitizer, arm64 macOS) the report
appears on 1.4 and on the pinned `develop`, and not on 1.3.1 or 1.3.2, where `deflate(Z_BLOCK)`
after `deflateResetKeep` still compresses the kept lookahead and leaves no head waiting for
insertion.

Effect on the proof: the exclusion of a direct `deflateResetKeep` from the deflate stream domain
(`docs/deviations.md`) cannot be removed: with it, `deflate` can read outside the window. A
positional hash-chain invariant that admits `deflateResetKeep` is false after step 4.
