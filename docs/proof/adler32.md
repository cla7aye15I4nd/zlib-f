# `adler32_z`

Source: `zlib/adler32.c`, with the upstream fix that checks for a null buffer at function entry
(`patches/0003-adler32-null-one.patch`). Specification: [../spec/format.md](../spec/format.md)
section 5.

Notation: `B = 65521` is the largest prime below 2^16. `NMAX = 5552`. A call is
`adler32_z(adler, buf, len)`.

## The idea in short

Adler-32 keeps two running sums. The machine adds bytes without reducing them. That is safe as long as at most 5552 bytes pass between two reductions, because the sums then stay far below 2^64. A sum that has not been reduced is still equal to the true sum modulo 65521, so one reduction at the end (and one every 5552 bytes) gives the exact value. Memory safety is bookkeeping: each loop reads exactly as many bytes as it subtracts from the length, so it never reads past the end.

## The function

```
if buf == NULL: return 1
sum2  = (adler >> 16) & 0xffff;   adler = adler & 0xffff
if len == 1:                                   -- case A
    adler += buf[0];  if adler >= B: adler -= B
    sum2  += adler;   if sum2  >= B: sum2  -= B
    return adler | sum2 << 16
if len < 16:                                   -- case B
    while len--: adler += *buf++; sum2 += adler
    if adler >= B: adler -= B;  sum2 %= B
    return adler | sum2 << 16
while len >= NMAX:                             -- case C
    len -= NMAX
    repeat 347 times: 16 steps (adler += buf[i]; sum2 += adler), buf += 16
    adler %= B;  sum2 %= B
if len:
    while len >= 16: len -= 16; 16 steps; buf += 16
    while len--: adler += *buf++; sum2 += adler
    adler %= B;  sum2 %= B
return adler | sum2 << 16
```

All variables are `unsigned long`, 64 bits.

## Theorem A1 (safety)

For every `adler`, every pointer `buf` into a live array `a` at index `off`, and every `len` with
`off + len ≤ size(a)`: `adler32_z` returns without undefined behaviour and does not change memory.
For `buf = NULL` it returns 1.

**Proof.** The only operations that can be undefined are the byte reads `buf[i]` and the pointer
increments.

1. Null: the first test handles it, and nothing else is evaluated.
2. Case A: one read `buf[0]`, valid because `off + 1 ≤ size`.
3. Cases B and C: every read is at index `off + k`, where `k` counts the bytes consumed so far.
   Each loop consumes exactly the number of bytes subtracted from `len`: the 347-fold loop consumes
   `347 × 16 = 5552 = NMAX`; the 16-chunk loop 16 per `len -= 16`; the byte loop one per `len--`.
   So after consuming `k` bytes, `len = L - k` and `k ≤ L`, hence `off + k ≤ off + L ≤ size`. Reads
   happen at `off + k` with `k < L`, so they are valid. The pointer after the last chunk is at most
   one past the end, which is valid to form.
4. Termination: each `while` strictly decreases `len` (by `NMAX`, 16 or 1), and `len < 2^64`, so
   the number of iterations is below 2^64. The fuel bound is never reached. ∎

## Theorem A2 (correctness)

Let `s1, s2` be the two components of the Adler-32 of `bytes` continuing from the start value
`(adler & 0xffff, (adler >> 16) & 0xffff)`, per the definition in the specification. If
`len ≠ 1`, or if `(adler >> 16) & 0xffff < B`, the result equals `s2 × 65536 + s1`, where the
start components are first reduced modulo `B`.

**Proof.** Write `(a, s)` for the machine pair and `(α, σ)` for the pair of reduced values of
the specification. Step 1 gives the invariant; step 2 says that overflow cannot happen between
reductions; step 3 finishes.

*Step 1. One byte.* The specification updates `α' = (α + b) mod B`, `σ' = (σ + α') mod B`. The
machine updates `a' = a + b`, `s' = s + a'`. If `a ≡ α` and `s ≡ σ` modulo `B`, then `a' ≡ α'`
and `s' ≡ σ'`, since `s' = s + a + b ≡ σ + α + b`. So after any number of unreduced steps, the
machine pair is congruent to the specification pair.

*Step 2. No wrap.* Between two reductions the machine takes at most `NMAX` bytes. Define
`j` = steps since the last reduction. Claim: `a ≤ 65535 + 255 j` and `s ≤ 65535 + j (65535 + 255 × 5552)`.
At the start (`j = 0`) both are at most 65535, because the start components are 16-bit values or are
reduced (below `B`). One step adds at most 255 to `a`, and adds the new `a` to `s`, which is at most
`65535 + 255 × 5552` while `j ≤ 5552`. Evaluating at `j = 5552` gives `a ≤ 1 481 295` and
`s ≤ 8 224 215 375`. Both are below `2^64`, so no addition wraps. (For case B, `j < 16`
and the bounds are far smaller.)

*Step 3. Reduction.* `a %= B` and `s %= B` turn congruent values into the exact reduced values.
In case B and in case A the code uses `if a ≥ B then a -= B`. This is exact when `a < 2B`: in
case B, `a ≤ 65535 + 15 × 255 = 69360 < 2B`; in case A, `a ≤ 65535 + 255 = 65790 < 2B`. For
`sum2` in case A the single subtraction is exact only if `sum2 + a < 2B`. With the start value
`sum2 < B` (the hypothesis) and the reduced `a < B`, `sum2 + a < 2B`. If the start `sum2` is
65535 or more, `sum2 + a` can still be at least `2B`, and the result is not reduced. That is why
Theorem A2 needs the hypothesis for `len = 1`. Example: `adler32_z(0xFFFFFFF0, "\0", 1)`. Here
`adler = 65520`, `sum2 = 65535`, the byte is 0, so `sum2 + adler = 131055`; one subtraction leaves
`65534`, which is not below `B`. The call returns `0xFFFEFFF0`, while the specification gives a
high half of 13. Theorem A1 (safety) holds for this input; only the value differs.

*Step 4. Composition.* The three loops of case C cover the bytes in order; the 347-block reduces
after every `NMAX`; the tail reduces once at the end. Applying Step 1 to each byte and Step 3 at
each reduction proves that the final pair is exactly `(σ, α)` packed as `α | σ << 16`. ∎

## Remark: the null check

Before the upstream fix, case A read `buf[0]` before the null test, so a call with `buf = NULL`
and `len = 1` was undefined, although `zlib.h` says that a null buffer returns the start value.
Theorem A1 is true only for the patched source.

## Status

Proved on paper. A Lean proof exists in the earlier attempt and moves into the proofs change of
this series.
