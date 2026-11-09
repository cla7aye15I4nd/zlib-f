# Configured dictionary window

The default build leaves INFLATE_STRICT undefined. Default initialization
keeps a 32768-byte window when the input header announces 256 bytes.

The sample uses a dictionary of 512 bytes of value 65. Its complete input is
`083c4a9e820103060000018900c4`. Its first fixed-block token copies three
bytes at distance 257. The actual library requests the dictionary, accepts
it and returns STREAM_END with output `414141`.

From the repository root, compile against the pinned source:

```sh
cc -O1 -I zlib tests/regression/inflate-configured-window/check.c zlib/inflate.c zlib/inffast.c zlib/inftrees.c zlib/zutil.c zlib/adler32.c zlib/crc32.c -o inflate-configured-window-check
./inflate-configured-window-check
```

The native execution is finite evidence of C behavior. Independent Lean
proofs in `ZlibF/Math/inflate-dictionary-window-rejection.lean` exclude every
output under the unchanged RFC relation. The corresponding acceptance
module proves that the configured-window relation accepts exactly this
input and output, including dictionary identifier and trailer checksum.
Neither mathematical proof executes the translated C.

The approved specification repair changes only the arbitrary-input END
acceptance clause. The RFC format, valid-input prefixes and completion
requirements retain their original definitions.
