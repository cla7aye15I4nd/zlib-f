# Statement test of the decoding side of the inflate format meaning

Step 1 of the proof workflow (`AGENTS.md`) for the body modes of `ParseMeaning`
(`ZlibF/Proof/inflate.c.meaning.lean`). The stream side and the late-rejection reproduction are
in `../inflate-meaning`.

`driver.c` makes raw and zlib streams with the real deflate (every level and strategy, window
widths 8 to 15, preset dictionaries, many and empty blocks) and inflates them with random input
and output splits and flush values. After every call it prints zlib's internal decoder state.
`check.py` parses the stream with a decoder written from `ZlibF/Spec/Format`, lists the parse
positions of `DeflateParsed` by bit offset, and checks each state in a body mode (`TYPE` to
`LIT`) against them: `HeldBits`, `BodyMatches`, the proposed `DynamicMatches` (dynamic header
fields and the code-length table), fewer than 8 held bits at a block boundary, `WindowMeaning`
with the proposed `wsize = 0 -> dict ++ out = []`, `CheckMeaning`, and the delivered output.

It also checks one proposed grammar step, `storedPad`. `inflate_STORED` drops the pad to the
byte boundary before it waits for `LEN` and `NLEN`, so a call can stop in `STORED` with the pad
already consumed. The grammar before the correction has no position there.

```bash
ZLIB_SRC=$PWD/zlib bash tests/goals/inflate-meaning-body/run.sh 800 1
```

Result on four seeds of 800 sessions: no clause violated in about 56,000 body-mode states.
This is evidence about finitely many histories, not a proof.
