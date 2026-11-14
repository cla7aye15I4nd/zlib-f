# Statement test: `Goal.deflateCopy` and `Goal.deflateCopy_safety`

`run.sh` builds the pinned zlib with its patches under AddressSanitizer and
UndefinedBehaviorSanitizer (LeakSanitizer as well on Linux) and runs `harness.c`. Each case builds
a source stream with a level, a strategy, a window (15, 9 or gzip), a memory level, and an input of
0 to 90000 bytes deflated with `Z_NO_FLUSH`, `Z_SYNC_FLUSH` or `Z_BLOCK`. It then calls
`deflateCopy` into a destination record filled with a byte pattern, while a counting `zalloc`
fails any chosen subset of the five allocations of the copy (all 32 subsets).

The program checks the clauses it can observe:
- The return is `Z_OK` or `Z_MEM_ERROR`, and the source record is unchanged.
- On `Z_MEM_ERROR`, an allocation of the copy really failed, `dest->state` is `NULL`, the other bytes
  of the destination record are unchanged, and no block of the copy is still allocated.
- On `Z_OK`, exactly five blocks are added. The copy then compresses the same next input to the same
  bytes as the source, and `deflateEnd` on both leaves no block allocated.

It also hands `deflateCopy` three inconsistent sources (no state; a null `zfree`; a null `zalloc` with a
live state) and checks `Z_STREAM_ERROR`, `dest->state == NULL`, the other destination bytes unchanged
and nothing allocated.

Result on 2026-11-13: 144000 cases, 4500 `Z_OK`, 139500 `Z_MEM_ERROR`, 3 refusals, no violation and no
sanitizer report. This is evidence, not proof.
