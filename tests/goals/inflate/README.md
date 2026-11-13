# Statement test of the inflate goals

Step 1 of the proof workflow (`AGENTS.md`): check a goal against the real C before proving it.

`driver.c` runs random sessions on the real `libz.a` (the pinned `zlib/` plus `patches/`, built by
`tests/build-zlib.sh`). Each session initializes inflate with a random `windowBits`, including
refused values, 0, gzip and automatic detection. The source stream is made by the real deflate:
raw, zlib with or without a preset dictionary, or gzip with a random `gz_header` (extra field,
name, comment, header CRC). A quarter of the sources are damaged, and junk may follow them. The
session then calls `inflate` with random input and output splits, every flush value (also invalid
ones), NULL buffers, and `inflateSetDictionary` after `Z_NEED_DICT` (sometimes with a wrong
dictionary).

There are two kinds of session:

- A protocol session uses only init, `inflate` and `inflateSetDictionary`, so it has the shape of
  `InflateProtocolTrace`. A wrapped dictionary call without a pending request leaves the protocol;
  the rest of that session is checked like a free session.
- A free session also calls every other stream operation: `inflateGetHeader` with random record
  limits, `inflateSync`, the three resets, `inflatePrime`, `inflateValidate`, `inflateUndermine`,
  `inflateCopy` and the queries.

`check.py` checks these clauses:

| Goal | Clauses | Sessions |
| --- | --- | --- |
| `inflateInit2_` | `Z_OK` exactly when `Api.inflWbits` accepts the argument | all |
| `Goal.inflate` | result codes; accounting; `Z_OK` means progress and not `Z_FINISH`; `Z_STREAM_ERROR` iff a NULL output, NULL input with input pending, or `SYNC`; a refusal changes neither the stream nor the state; `Z_BUF_ERROR` only without progress or under `Z_FINISH`; progress with input and output space unless `Z_BLOCK`/`Z_TREES`; the mode after `Z_STREAM_END`, `Z_NEED_DICT`, `Z_DATA_ERROR`, `Z_MEM_ERROR`; totals | all |
| `Goal.inflate_sequence` | a finished single-dictionary epoch consumed a stream that `Api.Layer.InflateAccepted` accepts; on a prefix of a stream that `Api.Layer.Decodes` accepts with a full window: output prefix, no `Z_DATA_ERROR`, exact end | protocol |
| `InflateCompletes` | a probe call with all the remaining source, enough room and flush `Z_NO_FLUSH`, `Z_SYNC_FLUSH` or `Z_FINISH` ends the stream or asks once for a missing zlib dictionary | protocol |

The decoder in `check.py` follows `ZlibF/Spec/Format/*.lean` and `ZlibF/Spec/Api/Basic.lean`,
not zlib. The second pass runs the C under ASan and UBSan; it checks memory safety of every
history the driver makes. This is evidence about finitely many histories, not a proof.

```bash
ZLIB_SRC=$PWD/zlib bash tests/goals/inflate/run.sh 400 1
```
