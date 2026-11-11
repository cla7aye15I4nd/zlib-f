# Statement test of the inflate format meaning

`late-rejection.c` shows three reachable decoder states that `ParseMeaning`
(`ZlibF/Proof/inflate.c.meaning.lean`) cannot describe. zlib rejects these dynamic block headers
only after it has read a whole part of the header. One raw `inflate` call with `Z_NO_FLUSH` stops
inside the header with `Z_OK`, not in `BAD`, but the consumed bits have no valid completion:

- A: the first three code-length-code lengths (for symbols 16, 17, 18) are 1, so that code is
  over-subscribed. Result: `LENLENS`, `have` = 5.
- B: the code-length code is empty. `inflate_table(CODES)` accepts it, and `CODELENS` reads each
  bit as length 0. Result: `CODELENS`.
- C: 257 zero lengths are read, so symbol 256 has length 0. Result: `CODELENS`, `have` = 257.

Build against the patched copy made by `tests/build-zlib.sh`:

```bash
cc -I<build>/z tests/goals/inflate-meaning/late-rejection.c <build>/z/libz.a -o late && ./late
```

This is evidence from the real C on three inputs, not a proof.
