# Earlier arguments and reference sources

The main source snapshot is
[zlib-formal at `0f1428677ebf5b1614ff77f4702bbb382b2bf3c6`](https://github.com/cla7aye15I4nd/zlib-formal/tree/0f1428677ebf5b1614ff77f4702bbb382b2bf3c6).
The reference review read its source and audit documents. It did not rebuild the snapshot or
establish its results in this repository. This is a reuse record; [progress](../progress.md)
owns current work and [checking](../checking/README.md) defines acceptance.

## Ideas adapted

| Reference source | Adaptation here | Boundary |
| --- | --- | --- |
| `Spec/Api/InflateApi.lean`: `Call`, `exec` | Closed public-call alphabet and direct dispatch in `ZlibF/Spec/Public/Calls.lean` | Entry coverage does not prove each entry or a sequence |
| `translation_map.py` | Inventory checks public names, defining files and manual sections | This is not a full preprocessed syntax comparison |
| `check_imports.py` | Check the transitive root import closure and missing source files | A source module in the closure need not prove its public goal |
| `final_check.sh` | Distinguish development, specification readiness and final acceptance | A fast build is not final acceptance |
| `Spec/crc32.lean`, `Spec/adler32.lean` | Independent bit/register and modular-sum checksum specifications | Retain noncanonical seeds and the distinct one-byte Adler behaviour |
| `check_axioms.py` | Reject empty/duplicate registries; avoid checks disabled by optimisation; inspect declarations beyond registered names | Registration alone cannot validate a statement's domain or translation fidelity |
| `Witness/`, `CONTRACT_AUDIT.md` | Init-domain targets and non-vacuity requirements beside sequence goals | Actual init must establish the same invariant used by calls |

The table uses paths relative to the reference's `lean/` directory. The tables below map the function families and changed representations.

## What does not transfer

The reference heap uses typed cells and byte blocks. The present heap uses object records and
tables. Heap statements and proof terms need adaptation. Pure arithmetic, bitstream relations,
loop measures and decomposition can retain their meaning only after their definitions and
domains are compared.

The reference sequence theorem `Zlib.Api.seq_safe` takes `ApiContract` as a hypothesis. Its
contract audit records instances with false preconditions and false strategy contracts. The call
alphabet and induction structure are useful. A conditional sequence theorem does not establish
safety here: every library callee needs a theorem about its actual translation, and actual init
must establish the invariant. Unrelated witnesses cannot supply that connection.

The reference's `ub.patch` policy and enabled patches differ. Its build configuration and proof
status do not transfer. This repository verifies its own upstream pin plus reviewed patches,
under its own public domains and acceptance rules.

```mermaid
flowchart LR
    R[Pinned reference] --> M[Extract mathematics and argument structure]
    M --> T[Restate for the present source and heap]
    T --> K[Kernel check, audit and mutants]
    K --> C[Accept only evidence for this repository]
```

The tables below locate reusable argument families. [Component proof guides](README.md)
explain the present argument structure. Neither a reference link nor a historical
reported test is a new validation run.

## Reusing an earlier argument

Earlier heaps used tagged cells and byte blocks. Current heaps use records and
object tables. Pure arguments transfer only after definitions and domains agree.
Heap-level proofs require new execution, frame and ownership arguments. Earlier
callee-contract hypotheses cannot replace theorems about actual translated callees.

## Deflate engine sources

| Source family | Mathematical or operational content | Present source family |
| --- | --- | --- |
| `EngineChains` | Rolling-hash forgetting after three updates; masked-key bounds; agreement of the third byte when keys and first two bytes agree | `deflate.c.engine.hash` |
| `EngineChains`, `Spec/deflate/Engine` | Ring-slot arithmetic; chain reachability; preservation by insertion and sliding; decreasing chain positions | `deflate.c.engine.chains` |
| `EngineFillSlide`, `EngineFill` | Slide threshold, read count, insertion count, `high_water` and disjoint slide-copy ranges | `deflate.c.engine.window` |
| `EngineMatch`, `matchChain_spec`, `innerLoop_spec` | First mismatch, the eight comparisons per round, maximal length 258 and result clamping | `deflate.c.engine.match`, `.lminner`, `.lmcond`, `.lmbody`, `.lmmain` |
| `PendingPut`, `DeflatePut`, `Hash`, `LmInit` | Pending-byte order, hash updates, insertion stores and clearing | `deflate.c.engine.macros` |
| `EngineSlide` | Every hash entry becomes `m >= w_size ? m - w_size : 0`; exact frame | `deflate.c.engine.slide` |
| `EngineReadBuf` | Copy `min(avail_in, size)` bytes, advance input counters and update the selected checksum | `deflate.c.engine.readbuf` |
| `PendingFlush` | Flush tree bits, copy pending bytes, advance output counters and reset an empty pending pointer | Pending-byte copy and the tree bit-buffer proof |

## Deflate lifecycle sources

| Earlier source | Content retained | Present source family |
| --- | --- | --- |
| `Inv`, `Inv7`, `Heap` | Back-pointers, buffer separation, ranges, store preservation and frames | `deflate.c.base` |
| `StateCheckQuick`, `End` | Null and invalid-stream refusals; exact state-check result | Base checking lemmas |
| `TuneQuick`, `HeaderQuick`, `UsedQuick`, `PendingQuick`, `Simple` | Four tuning stores; gzip-only header store; optional output stores; pending-count overflow | `deflate.c.life.check` |
| `Bound` | Wrapper length, low 16 bits of `extra_len`, terminated strings and the bound arithmetic | `deflate.c.life.bound`, including `boundTail` and `WrapLen` |
| `InitParams`, `Init*` | Parameter normalisation, powers of two, buffer sizes and configuration-table ranges | Arithmetic supporting init and the base invariant |
| `End` | Exact status-dependent result, five frees and clearing the stream state pointer | `deflate.c.life.end` |
| `LmInit`, `Reset*`, `ResetTr` | Hash clearing, tuning table, counters, wrapper status and tree reset | `deflate.c.life.reset` |
| `InitFail*`, `InitOk*`, `InitMem`, `InitFresh` | Each failing allocation and its cleanup; exact successful state | Initialisation argument structure |
| `Prime*`, `PrimeArith` | Move pending bytes; preserve their bit value; append the low requested bits | Priming arithmetic and execution decomposition |
| `Copy*` | Refusals, failure cleanup, independent buffers and rebased tree pointers | Copy argument structure |
| `DictGet`, `GetDictQuick` | Return `min(strstart + lookahead, w_size)` bytes from the end of the window | `deflate.c.life.getdict` |

## Inflate sources

| Earlier family | Content | Present source family |
| --- | --- | --- |
| `natBits`, `bytesBits`, shift and mask lemmas | Low-bit lists, byte append, bit dropping and format bit order | `inflate.c.main.bits` |
| `InflateBits` | `PULLBYTE`, `NEEDBITS`, `BITS`, `DROPBITS`, `BYTEBITS`, `INITBITS`; preserve held bits followed by unread bytes | `inflate.c.main.macros` |
| `InflateTopLoop`, `InflateLoop` | Decreasing measure and every loop exit | `inflate.c.main.xloop` |
| `SpecStored`, `SpecStoredCopy`, `Copy*` | Stored length/complement check and unchanged copied bytes | `inflate.c.main.stored`, `.stored2` |
| `InflateHead`, `InflateHdr*`, `InflateName` | Header checks, field lengths, optional header writes and CRC | Mode arguments and header arithmetic |
| `InflateTable`, `InflateTables`, `InflateCodeLens*` | Dynamic counts, code-length order, repeats and table installation | `inflate.c.main.table` through `.table6`; see companion record |
| `InflateLen*`, `InflateDist*`, `InflateMatch*` | Slow lookup, subtables, distance checks and window/output copy | Symbol, lookup and copy argument structure |
| `InflateCheck`, `InflateCheckStep` | Totals, checksum update and trailer comparison | `inflate.c.main.check0`, `.check` |
| `InflateCases1`, `InflateUpd`, `InflateFixed` | Simple modes, dispatch, refusals and fixed-table selection | Simple/type modules and fixed-table theorem |
| `infLeave_ok`, `leaveTail_ok`, `updatewindow_frame` | Register writeback, window update, counters and return-code rules | Epilogue composition argument |

## Table and trailer sources

| Earlier source | Reusable argument | Present source family |
| --- | --- | --- |
| `InflateTables` (about 1,161 lines) | `LENLENS` reads `min(ncode - have, available_bits / 3)` groups; order permutation, `lensRead`, `lensZero`, `Good3`; read and zero-fill loops | `inflate.c.main.table` through `.table6` |
| `InflateCheck`, `InflateCheckStep` | Output totals, checksum update and byte-swapped zlib comparison | `inflate.c.main.check0`, `.check` |
| `InflateBits` | Refill and consume bits without changing the represented stream | Shared `inflate.c.main.macros` results |

## Callback sources

| Earlier family | Reusable content | Present source family |
| --- | --- | --- |
| Init checks and allocation | Version, size and parameter refusals; memory failure; exact fields stored on success | `infback.c.init` |
| End and entry exits | Invalid stream/state refusals; state free and cleared pointer | `infback.c.end`, `.back` |
| First input exhaustion | No bytes from `in`, buffer error, input fields restored, no output callback | `infback.c.back` |
| Callback contract and witness | Own block sets and local invariants; a concrete initialised example | `infback.c.callbacks` |
| Input macros | Refill/consume bits, callback transition and remaining-input measure | `infback.c.pull`, `.macros` and shared inflate bit lemmas |
| Output room and window writes | Flush a full window to `out`, preserve prior output and extend the output view | `infback.c.room`, `.stored` |
| `TYPE`, fixed tables and bad modes | Last-block decision, block type, fixed-table fields and error messages | `infback.c.inv` and `inflate_fixed_ok` |
| Stored block and length order | Alignment, complement check, bounded piecewise copy; order permutation | `infback.c.pure`, `.stored` |
| Dynamic tables and slow lookup | Counts, repeats, constructor calls and canonical root/subtable agreement | Earlier argument structure to restate against present table semantics |
| Dispatch and leave | Falling loop measure; last output callback; exact result and input writeback | Present loop rule and composition argument |

## Gzip sources

| Earlier family | Reusable content | Present source family or boundary |
| --- | --- | --- |
| `Basic` | Field layout and tags | Replaced by record access and stream references |
| `Simple` | Buffer setting, EOF, tell, error query and integer limits | `gzlib.c.simple` |
| `Error`, `ErrorMsg` | Free old message; store code; allocate and format `path: text`; allocation failure | `gzlib.c.error` covers the null-message path; formatted messages need exact formatting semantics |
| `Reset`, `Rewind` | Reset fields and errors, refusal rules, file seek and input-adjusted offsets | `gzlib.c.error`, `.rewind` |
| `SeekParts`, `SeekRaw`, `SeekFwd`, `SeekBack`, `SeekTail`, `SeekMain`, `SeekCor` | Target arithmetic and raw, forward and backward branches | `gzlib.c.seek` |
| `SeekNeg`, `SeekNegUb`, `SeekFault`, `SeekWitness` | Negative positions and signed-overflow paths | Conditional exact-fault lemmas, not a public safety theorem |
| `OpenMode`, `OpenParts`, `OpenRest` | Mode-character fold and cleanup on `+` | `parseMode` and the opening argument structure |
| `OpenPath`, `OpenDesc`, `OpenFinish`, `OpenEff*`, `GzopenEff*`, `Dopen*` | Path copy, descriptor flags, append/truncate effects and failure cleanup | Exact formatting, file effects and ownership must compose |
| `Close`, `Dispatch` | Reader/writer dispatch and live-block accounting | `gzclose.c`; actual reader/writer cleanup belongs to their files |

## Historical short-distance check

The earlier record reported an experiment on a candidate missing-`whave` update before the fast
path. Raw fixed-Huffman streams used one to three literals followed by a length-three match at
distance one to four. The matrix included fast calls with at least six input bytes and 258 output
bytes of room, input split one byte at a time, and two-call decoding with a fresh output buffer.
The record reports agreement between paths, the expected “invalid distance too far back” error,
and no sanitizer finding.

That experiment refuted the candidate only for those ordinary-`inflate` cases. It did not cover
long distances, full or wrapped windows, other window sizes, or the callback decoder. It is
historical test evidence, not a kernel proof or a newly repeated validation run.

## Evidence boundary

The earlier review recorded 8000 randomized compressor sessions with sanitizers
and round-trip comparison. It varied levels, strategies, memory levels,
wrappers, chunk sizes down to one output byte, flush modes, parameter changes
and copying. It reported no mismatch or sanitizer diagnostic in those sessions.
Dictionary setting, priming and custom gzip headers were outside that run. The
one-byte-window stored path was also excluded.

These observations do not prove safety for all inputs, initialization history,
overlay capacity, other configurations or the C assumptions above. Focused
reproducible evidence belongs with its regression. Acceptance rules belong in
[checking](../checking/README.md). [Progress](../progress.md) records current
unresolved items and proof acceptance.

## Historical gzip seek observation

The earlier record reported reading five bytes to EOF, then seeking five bytes
relative to the current position. Seek returned ten while tell remained five.
Its interpretation was that forward seek retained `past`; an older abstract
relation instead required the target position and a cleared flag. This was not
rerun for this revision. The source interpretation remains **to confirm**, and
the observation does not establish an operational refinement or a new finding.
