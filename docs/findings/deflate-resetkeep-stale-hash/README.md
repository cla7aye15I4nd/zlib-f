# deflateResetKeep: stale hash entries can produce a wrong match

Status: reproduced on the pinned C; the intended use of `deflateResetKeep` is not documented in
`zlib.h` (it is listed among the undocumented functions), so whether this is a zlib bug is **to
confirm** with upstream. It is a data error, not a memory error.

`deflateResetKeep` keeps the window and the hash ("Keep the window and the hash, but drop what
was left unfinished"): `strstart` stays, `lookahead` becomes 0. The hash still holds the positions
`strstart - 2` and `strstart - 1`, inserted with keys of three bytes that reached into the dropped
lookahead. The next `deflate` call writes new input from `strstart` on. `longest_match` does not
compare the third byte of a candidate (it relies on equal hash keys), so a stale candidate can be
accepted with a wrong third byte.

Reproduction: `repro.c` compresses data A without flushing, calls `deflateResetKeep`, compresses
data B to the end, and decodes the second stream with the kept window `window[0 .. strstart)` as
the dictionary. Within the first 41 completed histories, 3 decode to data different from B
(seeds 13, 35, 40). With `CLEAR_HASH(s)` added after `s->lookahead = 0;` none of 200000 differs.

Effect on the proof: `DInv`'s hash-chain clause does not hold after `deflateResetKeep`
(`docs/progress.md`, deflate). Safety does not depend on the hash keys (`longest_match` reads only
window bytes below `strstart`).
