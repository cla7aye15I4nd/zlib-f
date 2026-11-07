# Historical evidence register

This page preserves observations made during earlier translation and contract work. It is not
a list of newly confirmed defects in the current pin. Old notes include proposed patches,
source readings and reported runs with different levels of evidence. Their labels must not be
promoted by repetition.

A current confirmed upstream issue requires an allowed input, a retained reproduction and a
sanitized run of the real C. It belongs in the root README with its scope and confidence, and a
reproduction under `docs/findings/`. This register does not invent missing reproduction files.
[Overview](overview.md) is the sole list of current investigations and remaining work.

## Earlier library observations

The table records what earlier work reported. When a full reproduction or its logs are absent
from the retained tree, the linked analysis is evidence of the report, not a rerunnable confirmation
against today's source. Readings of C still awaiting proof are **to confirm**.

| Observation | Retained source and confidence | Reported scope |
| --- | --- | --- |
| `gzsetparams` can record a change that the inner compressor did not accept | Earlier findings text reported two independent runs: 16640–16660 random bytes at level 6, a request for level 0, then 200000 zero bytes produced a still-compressed file of about 16.9 KB. The [gz analysis](translation-notes/gz-side.md) and [translation notes](translation-notes/gz-files.md) retain the mechanism but label it a candidate. That inconsistent historical status is not current confirmation. | Normal parameter changes; valid data can still be produced. The [contract review](checking/contract-review.md) requires a successful valid change to reach the inner compressor. |
| `crc32_combine_op` may not terminate for an arbitrary operator | Earlier findings text reported two timeout runs for `1UL << 32`; the [compressor-side analysis](translation-notes/deflate-side.md) records `crc32_combine_op(1, 2, 1UL << 32)` as run. No standalone reproduction is retained here. | An operator not produced by `crc32_combine_gen`. The documented generated-operator domain is distinct; this is not evidence of failure within that domain. |
| `gz_fetch` can retain a stale source pointer after a partial read followed by failure | The [gz analysis](translation-notes/gz-side.md) records an earlier address-sanitizer overread and a submitted fix. The short [translation account](translation-notes/gz-files.md) retains the cause. Historical sanitizer report; not independently rerun by this rewrite. | Read error after some data. The ordinary file-world model does not cover every such external read sequence. |
| `gzseek` after `gzungetc` at position zero can overflow signed position arithmetic | The [gz analysis](translation-notes/gz-side.md) records an earlier undefined-behaviour-sanitizer run and proposed bounds checks. Historical sanitizer report; no retained standalone reproduction is linked. | A negative logical position and large seek arithmetic. It cannot justify restricting the broad seek target. |
| Clearing an error after failed `gzflush(..., Z_FINISH)` can precede lost output | Earlier findings text reported further writes and a successful close with an empty file. The [gz analysis](translation-notes/gz-side.md) provides source context; the former long function narrative containing the reproduction is no longer present. Reported observation only. | Error recovery and writer lifetime. This does not alter the separately proved clearing effect of `gzclearerr`. |
| `inflateCopy` compares pointers into unrelated objects | The [inflate analysis](translation-notes/inflate-side.md) records the fixed-table versus state-table comparison, a pointer-comparison sanitizer run and 17 differential discrepancies. Historical source and execution report; current reachability and C definedness are **to confirm**. | Copying a stream stopped inside a fixed block. Practical intended behaviour does not settle pointer-comparison definedness. |
| `gzseek` past end can disagree with `gztell` and retain EOF | Earlier findings text reported a five-byte gzip file: seeking five bytes forward returned 10 while telling returned 5 and EOF stayed set; a transparent file differed. The [gz analysis](translation-notes/gz-side.md) retains position and pending-skip context. Reported API quirk; no standalone retained reproduction. | Logical position after end of input. Whether this violates the public contract needs separate review. |
| Small inflate windows can make success depend on output splitting | Earlier findings text reported a 20000-byte stream accepted with enough output room in one call but rejected with 100-byte calls for smaller windows. The [inflate API](api/inflate-stream.md) states the window domain. Historical observation of documented small-window limits, not an upstream defect. | A window smaller than the stream needs. It cannot be used to claim arbitrary small windows decode every valid stream. |

## Caller-domain questions recorded earlier

The [compressor-side analysis](translation-notes/deflate-side.md)
and [inflate analysis](translation-notes/inflate-side.md) record these cases. Their classification
depends on what the public API permits; none is promoted here to a confirmed defect.

| Case | Historical question and evidence boundary |
| --- | --- |
| Null length pointers in `compress2` and `uncompress2` | Compatibility wrappers read scalar cells before the `_z` checks. A null-read witness is now retained in the [allocation regression](../tests/regression/compress-allocation/README.md). A diagnosed null read does not establish that the caller was permitted to pass NULL. |
| `deflateCopy(&s, &s)` | Reported loss of the old owned state; whether identical source and destination are admitted requires contract review. |
| `inflateGetHeader(strm, NULL)` | Reported null dereference; the null-header caller domain needs review. |
| `deflateSetDictionary` and `total_in` | Dictionary bytes contribute to the counter. The earlier interpretation of “input bytes” may have excluded them; documentation meaning and operational refinement must be distinguished. |
| Late `deflatePrime` and `deflateSetHeader` | C may accept calls outside the documented order; a later header dereference can then be invalid. Acceptance alone does not make the sequence documented use. |
| `deflateResetKeep` and preset-dictionary output | A retained history can make the next stream request a dictionary. This needs the documented reset semantics, not an assumption that every reset is a fresh history. |

## Model and specification evidence

These records concern the formalisation or its interpretation. They are not library safety findings.
The tests linked below are retained execution or diagnostic evidence; this page does not assert
that they were rerun for the documentation change.

| Record | Retained evidence | Meaning |
| --- | --- | --- |
| Late inflate memory failure can follow output | The [allocation regression](../tests/regression/compress-allocation/README.md) records a truncated zlib prefix returning `Z_MEM_ERROR` with one output byte and both stored counts. Earlier runs also recorded advanced pointers but unchanged stream totals and checksum when window allocation failed. | A memory error does not imply empty output. The [contract review](checking/contract-review.md) records the corrected utility relation and distinct init-failure versus late-failure scalar effects. |
| Consumed lookahead need not all describe a valid stream | The [deferred-distance regression](../tests/regression/inflate-deferred-distance/README.md) retains raw bytes `73 04 42 00`: one call emits `A`, and the next rejects an impossible distance without consuming more input. | The former whole-lookahead specification was too strong. The reviewed supporting-prefix condition is a model correction, not a zlib bug. |
| Negative priming values keep their low bits | The [priming regression](../tests/regression/inflate-prime/README.md) compares actual calls across signed values and boundary bit counts. | Mapping a negative value to zero was a specification error. Finite agreement is not a general refinement proof. |
| Automatic compressor storage must not consume allocation failure | The [allocation regression](../tests/regression/compress-allocation/README.md) retains failure-index, buffer and live-block observations and a mutation of the old translation. | The extra allocation was a translation bug. Null-destination pointer subtraction remains a separate C definedness question. |
| Static CRC input now has a represented address | The [positive regression](../tests/verification/regressions/crc-static-address.lean) retains the former counterexample's valid 47-byte static-table read and checks both CRC entries. | The translation-model rejection is repaired without reducing the checksum caller domain. This is not an upstream defect; general ABI and aliasing limits remain. |
| Gz state can retain a pointer into a caller buffer | The [gz analysis](translation-notes/gz-side.md) records arithmetic by zero after direct decompression and possible caller freeing. No sanitizer diagnosis was reported. | Pointer lifetime and the model's dangling-pointer checks need separate reasoning. An old proposed patch is not applied source or confirmed evidence. |

The [runtime review](checking/runtime-review.md) records additional representation gaps, including
model-null fresh pointers and fixed garbage values. The [trusted base](trusted-base.md) states
the current obligations. Historical review conclusions do not constitute independent baseline
approval or complete safety and correctness proofs.
