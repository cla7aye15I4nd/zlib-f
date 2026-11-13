# Statement test: `Goal.inflate_back_sequence_safety`

`run.sh [first-seed] [count]` builds the pinned zlib with its patches under AddressSanitizer and
UndefinedBehaviorSanitizer (LeakSanitizer as well on Linux) and runs `harness.c`. Each case draws a
stream (raw deflate of random data at any level, strategy, memory level, window and flush pattern;
mutated or truncated; with a garbage tail; or random bytes), a window of exactly `1 << windowBits`
bytes for `windowBits` 8 to 15, and one to three `inflateBack` calls on the same state, then
`inflateBackEnd`.

The call-backs are adversarial within the documented contract: `in` hands out pieces of 1, 1 to 7,
1 to 4096 bytes or all at once, each in a fresh buffer of exactly that size that is freed at the next
`in` call, and may stop early by returning 0; `out` checks that it gets the window and at most the
window size, reads every byte, and returns 0, fails on its first call, fails at random, or returns an
arbitrary nonzero value. The library's own allocations are counted through `zalloc`/`zfree`.

The program checks the clauses of the safety goal it can observe: no sanitizer report, a return of
`Z_STREAM_END`, `Z_DATA_ERROR` or `Z_BUF_ERROR`, `inflateBackEnd` returning `Z_OK`, and no allocation
left after it. As a sanity check it also compares the output of an unmodified stream with the input
when the window is at least the encoder's (zlib.h's precondition: with a smaller window the output can
be wrong, which is a functional matter outside the safety goal; the sanitizers stay silent there).

Result on 2026-11-12, seeds 1 to 30000: no report; 13030 `Z_STREAM_END`, 16463 `Z_DATA_ERROR`,
30469 `Z_BUF_ERROR` (over all calls), 6049 round trips equal. This is evidence, not proof.

`bits8.sh [first-seed] [count]` tests a loop invariant the proof needs: when `inflateBack` takes the
fast path (`have >= 6 && left >= 258`), fewer than 8 bits are held. `inflate_fast` lists
`state->bits < 8` among its entry assumptions; `inflate.c` checks it before the call, `infback.c`
does not. The script builds a copy whose fast path traps on `bits >= 8` and runs the same harness.
Result on 2026-11-12, seeds 1 to 30000 and 30001 to 60000: no trap. This is evidence, not proof.
