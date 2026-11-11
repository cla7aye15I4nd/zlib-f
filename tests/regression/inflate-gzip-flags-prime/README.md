# Inflate gzip flags wider than 16 bits

After `inflateInit2(&strm, 31)` and the two gzip magic bytes, `inflate` is in `FLAGS` with no
bits held. Two `inflatePrime(&strm, 16, v)` calls are accepted (`state->bits + bits <= 32`), so
`hold` holds 32 bits. `FLAGS` runs `NEEDBITS(16)`, which reads nothing, and stores
`state->flags = (int)(hold)`. With `hold = 0x00010008` the method byte is 8 and no reserved flag
is set, so decoding goes on with `flags == 65544`; with `hold = 0x80000008`, `flags` is negative.
The rest of the header and an empty stored block decode to `Z_STREAM_END`. AddressSanitizer and
UndefinedBehaviorSanitizer report nothing: the state is reachable and defined (the conversion of
a value above `INT_MAX` is implementation-defined, modulo 2^32 on the selected platform).

`InflatePhase` used to state that `flags` is -1 or a 16-bit word. That clause was false on this
history and was removed, with the 16-bit range of `FlagsOrigin`
(`tests/verification/regressions/inflate-gzip-flags-prime.lean`). No proof used the range.
This is not a zlib defect.

`run.sh` builds the pinned source with the sanitizers and checks both values.
