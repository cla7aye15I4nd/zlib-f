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

`data-error-then-mem.c` shows that a raw stream can be in `MEM` while the last `inflate` result
is `Z_DATA_ERROR`: after a rejected block type with no window yet, a raw `inflateSetDictionary`
whose window allocation fails returns `Z_MEM_ERROR` and enters `MEM`. `ParseMeaning` therefore
allows `MEM` after a data error for raw streams only.

## Stream-side state test

Step 1 of the proof workflow (`AGENTS.md`) for the stream side of `ParseMeaning`
(`ZlibF/Proof/inflate.c.meaning*.lean`): the wrapper header, the dictionary request, the trailer
and the end.

`driver.c` is `tests/goals/inflate/driver.c` restricted to protocol sessions
(`InflateProtocolTrace`), with a line of private `inflate_state` fields after every `inflate` and
`inflateSetDictionary` call. On every prefix of a valid source with a full window, `check.py`
computes the parse position of the consumed bits from the format specification
(`tests/goals/inflate/check.py`, not zlib) and checks the facts listed in its docstring:
configuration fields, header byte positions, the header CRC accumulator, `DICTID` in `check`,
`havedict` against a pending request, the flags word, fewer than 8 held bits at a block boundary,
`total` and `check` against the output, the trailer positions, and an empty bit buffer at `DONE`.

```bash
ZLIB_SRC=$PWD/zlib bash tests/goals/inflate-meaning/run.sh 2000 1
```

Evidence on finitely many histories, not a proof. Result on 2026-11-10: no fact violated in 6000
sessions (seeds 2 to 4); three mutated facts are each caught.
