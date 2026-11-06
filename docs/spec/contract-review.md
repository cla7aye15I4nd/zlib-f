# Public contract review

The inventory fixes 95 default-build entries and eight family targets. Each names a closed
proposition about the translated implementation. The exact `gzclearerr` and `inflateCodesUsed`
targets now have proofs.
Source review of a definition is separate from independent approval of the semantic baseline.

## The three specification layers

| Directory | Meaning |
| --- | --- |
| `ZlibF/Spec/Format` | Legal DEFLATE, zlib and gzip bytes, their decoding and checksums |
| `ZlibF/Spec/Api` | Heap-free models of API behaviour; some older models cover only documented call patterns |
| `ZlibF/Spec/Public` | Fixed implementation targets: actual execution, caller domain, results, frame and ownership |

A proof about the format or an abstract API model alone does not verify a public function.
The actual translated call is fixed in `Calls.lean`. The public targets cannot substitute an
empty execution relation or assume that a library callee obeys its contract.

```mermaid
flowchart LR
    F["Format: bytes and decoding"] --> M["API: observable behaviour"]
    M --> T["Public targets"]
    C["Actual translated functions"] --> T
    T --> K["Exact registered theorem, kernel check and locked definitions"]
```

## Review boundaries

| Group | Target modules | Properties checked in the statements |
| --- | --- | --- |
| Checksums and queries | `Checksums`, `Queries` | Null-buffer conventions, all scalar values, signed combine lengths, immutable heap and constant tables |
| Init and reset | `Initialisation`, `Lifecycle`, `Domains` | Version/error ordering, every signed parameter, default allocation failures, exact cleanup, established invariant and concrete nonempty domains |
| Stream operations | `StreamQueries`, `Streams`, `Copy` | Clean refusals, counters and partial output, dictionary windows, bit insertion, bounds, independent copied storage and failure cleanup |
| Buffer utilities | `Utilities` | Distinct compatibility wrappers, scalar-cell rules, trailing input, partial output on memory failure, exact stored lengths and temporary cleanup |
| Callback inflate | `Back` | Actual callbacks, finite returning protocol, adaptive input, shared-allocation descriptors, raw decoded output and caller-owned window |
| Gz handles | `GzState`, `GzOpen`, `GzControl`, `GzRead`, `GzWrite`, `GzClose` | Lazy allocation, inactive dangling fields, error recovery, positions, whole-item counts, borrowed messages, accepted bytes, seek zeros and descriptor cleanup |
| Lifecycles | `Sequences`, `GzTrace` | Every admitted next call returns, init-established invariants, exact live-allocation changes, end/close, ordinary byte-format epochs and complete writer output |

Source readings outside the named checked theorems remain **to confirm** by implementation proofs.
The public function manuals
give the parameter tables and the source-level details. Their historical run notes are evidence;
their proof-status paragraphs do not override the registry and CI on a named commit.

## Corrections made during review

`Uncompress2` now permits output before a late memory failure. It shares its data relation with
the concrete utility targets. Buffer exhaustion no longer claims that unused trailing bytes
must extend a valid compressed stream. Concrete targets distinguish unchanged init-failure
length cells from the counts stored after a later failure.

Stream queries include null and clean invalid-state refusal. Priming uses the source's zero,
negative and overflow order. Optional output cells remain independently optional.

The pinned `gz_look` initially checks four header bytes. A wrong method, wrong flags or a file
shorter than four bytes can be transparent input. Later members are sent directly to inflate.
The default gz buffer is 8192 bytes; `gzbuffer` clamps to eight and rejects doubling overflow.
Formatting refusal returns a stream error, separately from an empty or oversized result.

The header does not promise that `gzsetparams` refuses every invalid scalar argument. The
target records that source behaviour. For valid parameters a successful call must also update
the inner compressor; changing only the outer handle fields is insufficient.

Callback descriptors may share an allocation with the window. Callbacks preserve the window
slice; their observation invariant ignores only that slice. The whole-function claim is
universal over those observation invariants, so a loose invariant cannot establish the target.

## Independent counterexample review

The follow-up review uses `a655458` as the immutable old specification. It changes no public
caller domain, translated function or runtime operation.

| Counterexample | Cause | Correction and checked evidence |
| --- | --- | --- |
| Raw `73 04 42 00`, one output byte | The first call returns `Z_OK` and `A` after pulling the impossible distance. Whole-lookahead validity rejects this actual result. | A supporting bit prefix must have a valid completion, and every compatible completion must extend the output. A kernel proof rejects the old condition and checks the model witness. The paired regression compares actual C and translated calls, including the next `Z_DATA_ERROR`. |
| Valid gz reader with an allocated message and an empty read-only table | The old `dropWindow` resized the read-only table when writing its default value. Actual `freeB` leaves that table unchanged. | Remove only the byte block. The generic free theorem covers every `WindowAllocation`; the complete public `gzclearerr` theorem checks the corrected target. |
| A model state with `2^63` decode-table slots | The query view omitted the C field's fixed array layout, so pointer subtraction need not fit `ptrdiff_t`. Such an array is impossible for C `codes[ENOUGH]`. | Require the actual 1444-entry layout in this query's representation condition. A kernel counterexample freezes the old question, and the corrected public query has an exact proof. |

The first correction also requires causal output evidence in the shared `Uncompress2` relation.
Universal determinacy alone could be vacuous after malformed lookahead. Neither clause assumes
that the rest of that lookahead is valid. The unchanged final decoder-model question still
requires a separate proof about actual decoder execution.
The separate legacy detection-lag clause has a confirmed counterexample. It is explicitly
excluded from any claim that this abstract model is an approved implementation refinement.

The shared cleanup helper occurs in `inflateReset`, `inflateReset2`, `gzrewind` and
`gzclearerr`. Their allocated blocks are writable, and each use requires the same byte removal.
The generic theorem establishes this helper effect. Complete proofs of the other callers are
**to confirm**. This is a specification representation error, not an upstream bug.

The query layout follows `inflate.h`'s `codes[ENOUGH]` and `inftrees.h`'s 852+592 bound.
The existing `Good` invariant entails it. Init and every actual stream transition must establish
and preserve that invariant; the sequence target requires this as a conclusion. The correction
adds no caller scalar limit and does not use an arbitrary bound to hide a reachable C failure.

The deflate target also fixes the converse of its stream-error classification. Under the
existing live-state premise, that error occurs exactly for invalid flush values, invalid null
buffers, or a non-finish call after finishing began. Enumerating an allowed error code alone
would permit spurious refusal of valid calls. The source's message-writing refusal remains
distinct from the earlier invalid-flush return; only the latter promises an unchanged heap.

The proof boundary also has regression checks. Removing causal evidence, restoring the old
lookahead condition, or dropping the input-prefix requirement must fail in the model proof.
Omitting error clearing or retaining either EOF flag must fail in the `gzclearerr` proof.
Differential tests remain execution evidence, not proof.

## Scope of the sequence claims

Safety and cleanup cover all admitted stream operations, including reset, copy and recovery.
Ordinary data epochs connect actual accepted and produced bytes to the independent format.
Their finish claims include sufficient-room completion. Eligibility markers are computed by
trace constructors; a proof cannot choose them or clear them at will.

One initial dictionary suffices for an ordinary RFC stream. Replacing a raw decoder dictionary
midstream changes that context. The marker records that change explicitly; its per-entry
window effect and sequence safety remain required. Other advanced effects, such as priming,
header capture and recovery, retain their concrete operation targets. The target set does not
yet constitute a completed operational refinement of every advanced combination.

Gz writer histories record actual calls, accepted input and consumed seek zeros. Final close
must produce gzip members decoding to that data, or the same bytes in transparent mode.
Existing file prefixes and tails are accounted for. This prevents position-only write
contracts from being mistaken for data correctness.

## Approval

Proposed changes during proof work need an immutable old/new statement, a source/manual
comparison and an explanation of the failure. Distinguish a proof technique problem, a wrong
specification, a translation mismatch and an upstream defect. A counterexample to an internal
invariant does not justify narrowing a public precondition. Init and the actual earlier calls
must establish any replacement invariant. Library callee contracts remain proved results.

Independent review checks the proposal before integration. A confirmed specification error is
corrected in its own change with regression evidence and regenerated locks. An ordinary build
or a proof author's approval alone does not establish that the specification is correct.

The readiness gate checks presence, compilation, fresh kernel replay and matching locks.
It does not decide semantic completeness. Independent review must approve these targets,
their representation limits and the trusted runtime before the commit becomes an authority
baseline. [../overview.md](../overview.md) is the only remaining-work list.
