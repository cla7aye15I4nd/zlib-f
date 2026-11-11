# Inflate with input and output in one block

`shared.c` inflates a 200000-byte zlib stream with the input range and the
output range in one heap block. The ranges are disjoint at the call. It runs
both orders: input before output, and output before input.

Result under ASan and UBSan: both orders decode the right bytes, and there is
no sanitizer report. `zlib.h` says nothing against this layout, and the C has
no `restrict` on these pointers. So this layout is defined behaviour and inside
the public domain (`StreamBuffers` asks only for separate ranges).

Consequence for the proofs: the fast decoder environment (`Env`,
`ZlibF/Proof/inffast.c.env.lean`) asks for distinct blocks (`ib ≠ ob`). That
premise may not be lifted into a public goal as a deviation. A public result
that goes through `inflate_fast` must cover one shared block. **Open.**

Run:

```bash
ZLIB_SRC=zlib bash tests/regression/inflate-shared-block/run.sh
```
