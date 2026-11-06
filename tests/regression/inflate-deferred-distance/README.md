# Inflate call sequence regression

This reproduces one raw fixed-block sequence with the actual C and translated
functions. It does not import the API model or prove that a byte prefix is valid.
The test supports review of the model's consumed-input condition. It is finite
execution evidence, not a library safety finding or a proof.

The input is `73 04 42 00`. The three block-header bits are `1,1,0`.
The following canonical Huffman codes are emitted most significant bit first,
then packed into bytes in least significant bit order:

| Symbol | Code value | Width |
| --- | --- | --- |
| Literal 65 (`A`) | 113 | 8 |
| Length 257 (length 3) | 1 | 7 |
| Distance 1 (distance 2) | 1 | 5 |
| End of block 256 | 0 | 7 |

There are 30 meaningful bits and two padding bits. No preset dictionary exists.
The literal provides one history byte; the following distance requests two.

The first call has exactly one output byte. It returns `Z_OK`, writes `41`, and
consumes three complete source bytes: `73 04 42`. It stops in `MATCH`, with
`hold=0`, `bits=1`, `length=3`, `offset=2`, and `whave=1`. The next call changes
only the caller's output capacity to eight. It returns `Z_DATA_ERROR`, consumes
no additional input, writes no additional output, and enters `BAD`. The test
observes both calls and the successful `inflateEnd`; it never sets an internal
decoder mode. The entire destination buffer is also compared.

`run.sh` requires an existing patched library build and the default LP64 target.
The sanitizer run requires a library built with ASan and UBSan as well as the
instrumented test driver. Leak detection remains enabled.

```sh
ZLIB_BUILD=tests/build/zlib bash tests/regression/inflate-deferred-distance/run.sh
SAN=1 ZLIB_BUILD=tests/build/zlib-san bash tests/regression/inflate-deferred-distance/run.sh
```

The runner rebuilds its imported translation modules, requires all three rows,
compares C and Lean output byte for byte, and checks the recorded consumption,
output and return codes. Artifacts are in `tests/build/inflate-deferred-distance/normal/`
and `tests/build/inflate-deferred-distance/san/`. Test-owned buffers are released after the
actual end call. A failed initialization or end is reported, not repaired.
