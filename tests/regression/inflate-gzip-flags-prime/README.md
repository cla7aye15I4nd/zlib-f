# Inflate gzip flags word after inflatePrime

A history on the real C where `state->flags` is not a 16-bit word.

1. `inflateInit2(&strm, 31)` and `inflate` on the two gzip magic bytes. The decoder waits in
   `FLAGS` with an empty bit buffer.
2. `inflatePrime(&strm, 16, 0x0008)` and `inflatePrime(&strm, 16, 0x0001)`. `inflatePrime` checks
   no mode, so the bit buffer now holds 32 bits: `hold = 0x10008`.
3. `inflate` on four more bytes. `case FLAGS` runs `NEEDBITS(16)`, which reads nothing, and then
   `state->flags = (int)(hold)`. The method byte is 8 and no reserved flag is set, so the header
   is accepted, and `flags` is 65544.

The sanitizers report nothing: the wider word is defined behaviour. zlib.h says that
`inflatePrime` "should only be used with raw inflate", but the library does not enforce it.

Consequence for the proof: the clause "a gzip header dispatch writes `flags` only as a 16-bit
word" is false without a premise on the entry bit buffer. The proved form is
`inflate_dispatch_gzip_header_flags_leave_word`
(`ZlibF/Proof/inflate.c.gzip-header-dispatch.lean`): the word fits in 16 bits when the entry bit
buffer held 0, 8 or 16 bits. Confidence: high (reproduced on the pinned source). Scope: callers that
use `inflatePrime` on a gzip stream before its flags are read.

```bash
ZLIB_SRC=$PWD/zlib bash tests/regression/inflate-gzip-flags-prime/run.sh
```

The same history refutes `InflatePhase.flags`, which stated that `flags` is -1 or a 16-bit word on
every reachable state. That clause and the 16-bit range of `FlagsOrigin` were removed; no proof
used them (`tests/verification/regressions/inflate-gzip-flags-prime.lean`).
