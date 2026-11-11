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

`far-match.c` reproduces correction P12. `case MATCH` leaves for want of output room before it
checks the distance, so a match whose distance reaches beyond the history can wait in `MATCH`
while the call returns `Z_OK`: a raw inflate of `03 02` (one fixed-block match of length 3 at
distance 1, no history) with no output room stops there, and the next call with room reports
"invalid distance too far back". `PendingParsed` at `.copy` admits such a match with nothing
written and no history bound; `MATCH` then rejects it. The Lean regression is
`tests/verification/regressions/inflate-unchecked-match.lean`.
