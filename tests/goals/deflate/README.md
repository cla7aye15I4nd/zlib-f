# Statement test of the deflate goals

Step 1 of the proof workflow (`AGENTS.md`): check a goal against the real C before proving it.

`driver.c` runs random histories on the real `libz.a` (the pinned `zlib/` plus `patches/`, built by
`tests/build-zlib.sh`). A history has the shape of `DeflateDataTrace`: `deflateInit2_` with every
kind of parameter (including refused ones), up to three preset dictionaries, `deflateBound`, then
`deflate` calls with random input and output chunks and every flush value, including invalid
flushes and NULL buffers. Each call is printed with the state the goals mention.

`check.py` checks these clauses on every call:

| Goal | Clauses |
| --- | --- |
| `Goal.deflate` | accounting and totals; result codes; `Z_STREAM_ERROR` iff `DeflateRefuses`; an invalid flush changes nothing; `Z_STREAM_END` facts; the exact `Z_BUF_ERROR` characterization; progress of `Z_FINISH`; `msg`; `data_type` |
| `Goal.deflate_sequence` | a finished stream decodes to the accepted input (`DecodesFor`); a completed sync or full flush consumed all input and ends at a flush point (`FlushedFor`); after a full flush the rest decodes without earlier data; `adler` after a successful call; `deflateBound` before data equals the model bound |
| `DeflateCompletes` | a `Z_FINISH`-only history with bound room ends the stream |

The decoder in `check.py` follows `ZlibF/Spec/Format/*.lean` (`Blocks`, `Body`, `Symbols`,
`CodeLens`, `Acceptable`, `OpenBlocks`), not zlib. This is evidence about finitely many histories,
not a proof.

```bash
ZLIB_SRC=$PWD/zlib bash tests/goals/deflate/run.sh 400 1
```

`ops.c` is a safety test of the history domain (`StreamReachable` with `StreamArguments`): random
sequences of every stream operation, including `deflateTune` with any values, `deflateParams`,
resets, copies, dictionaries, queries, refused calls, and `deflatePrime` and `deflateSetHeader`
in the documented order, on the C under ASan and UBSan. With the order rules removed it finds
the cases of `tests/regression/deflate-history-domain` within a few hundred sessions.

The run takes a few minutes. The second pass (`FOCUS`) draws the tight `deflateBound` cases:
`memLevel` 1 to 3, the default 15/8 configuration, `Z_FIXED`, incompressible data, `Z_FINISH`
only. The third pass runs the C under ASan and UBSan.

`invariant.c` checks the scalar fields of the universal invariant `DInv`
(`ZlibF/Proof/deflate.c.universal-invariant.lean`) at every call boundary of random histories of
the real C, reading the state through `deflate.h`: block span, level-0 shape, lazy match state
(with the unsigned match distance, which may equal `MAX_DIST`), bit bound, pending cursor, symbol
room, slide count, cleared block costs. It found that a pending match can sit exactly at
`MAX_DIST`, so the invariant states that distance in `uInt` arithmetic.

## Ledger

`ledger.c` prints, at every call boundary of random histories (`deflate` with every flush and
small output buffers, `deflateParams`, `deflateSetDictionary`, `deflatePrime`, `deflateTune`,
raw, zlib and gzip with a `deflateSetHeader` record), the emitted bits (delivered output,
pending bytes, held bits), the open block (`sym_buf`, `block_start`, `strstart`, `lookahead`,
`match_available`), a CRC of the window, the accepted input and the dictionaries.
`ledger_check.py` checks the ledger claims with the decoder of `check.py`:

- L1: in a header state, the emitted bits are a prefix of the wrapper header; afterwards they
  are the header followed by complete blocks with no leftover bits, no final block before
  `FINISH_STATE`, and after the final block only zero padding and, once `wrap < 0`, the trailer.
  With `deflatePrime` before a wrapper, the full prime bytes come first, then the header, then
  the remaining prime bits held in `bi_buf`.
- L2: the complete blocks decode to `input[0..k)`, with the dictionaries as history, the history
  reset at each full flush, and distances at most `2^windowBits`.
- L3: level > 0: the recorded symbols replay to `input[k..k+r)`, with
  `k + r + match_available + lookahead = accepted` and `strstart - block_start = r + match_available`.
  Level 0: `window[block_start..strstart] = input[k..k+span)` and `k + span + lookahead = accepted`.
- L4: the window is the suffix of the history, where each `deflateSetDictionary` call contributes
  only its last `w_size` bytes.
- L5: after `Z_STREAM_END` everything is delivered and decodes to the input with the trailer.

```bash
clang -O2 -I zlib tests/goals/deflate/ledger.c zlib/{adler32,crc32,deflate,trees,zutil}.c -o ledger
python3 tests/goals/deflate/ledger_check.py --run ./ledger 20000 0 8
```

Each claim is reported separately with the smallest failing history. Evidence, not proof.
