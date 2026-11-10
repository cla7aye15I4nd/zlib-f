# Project status and remaining work

[Documentation](README.md) · [API](api/README.md) · [Checking](checking/README.md)

**Work in progress. Full zlib verification is not complete.**
This is the single current-status and remaining-work page.
The first target is the default LP64 Linux static build with the default allocator.
Other upstream configurations remain goals. Compiler/OS correctness and performance
are outside the proof.

<!-- proof-progress:start -->
## Proof progress graph

**103 public API targets.** Registered proofs: 50 ·
locally checked but not registered: 0 ·
not proved without a recorded blocker: 52 ·
blocked: 1.
These are local snapshot counts, not final verification or a percentage of effort.

[Open the public API graph and proof references](progress.md).
The scope is the public API manifest, including call sequences and initialization domains.
[Supporting proofs](supporting-proofs.md) lists the other 78 audit targets
and their module dependencies. They do not change the public API counts.
🟩 **Registered proof** · 🟦 **Locally checked, not registered** · ⬜ **Not proved** · 🟥 **Blocked**.
Red groups contain a blocked target. Other mixed groups use blue when they contain
checked results; counts show what remains. Work on other targets can continue.
Solid arrows show calls from the called entry to its caller. Dotted arrows show
proof or target-definition references. [Status details](progress.md#status-key).
Final acceptance still requires the full audit and CI on a named commit.

### Blockers

| Blocked targets | Reason and next step |
| --- | --- |
| [inflateInit2_](./progress.md#target-zlibf-spec-public-goal-inflateinit2) | [Inflate initialization cleanup](./overview.md#inflate-initialization-cleanup) |

```mermaid
flowchart LR
  queries["Library queries<br/>6 targets · 6 registered · 0 local"]:::registered
  checksums["Checksums<br/>11 targets · 11 registered · 0 local"]:::registered
  inflate["Inflate streams<br/>18 targets · 14 registered · 0 local · 1 blocked"]:::blocked
  deflate["Deflate streams<br/>17 targets · 8 registered · 0 local"]:::local
  back["Callback decoding<br/>3 targets · 2 registered · 0 local"]:::local
  gzip["Gzip files<br/>32 targets · 7 registered · 0 local"]:::local
  buffers["Whole-buffer operations<br/>8 targets · 0 registered · 0 local"]:::open
  lifecycle["Lifecycles and call sequences<br/>8 targets · 2 registered · 0 local"]:::local
  back -.-> lifecycle
  checksums --> deflate
  checksums --> inflate
  deflate --> buffers
  deflate --> gzip
  deflate -.-> lifecycle
  gzip -.-> lifecycle
  inflate --> buffers
  inflate --> gzip
  inflate -.-> lifecycle
  queries --> buffers
  queries --> deflate
  click queries href "https://github.com/cla7aye15I4nd/zlib-f/tree/dba8cbbdde28e0ddcfeae060d8ce3005d73210d7/ZlibF/Spec/Public" "Open specifications" _blank
  click checksums href "https://github.com/cla7aye15I4nd/zlib-f/blob/dba8cbbdde28e0ddcfeae060d8ce3005d73210d7/ZlibF/Spec/Public/Checksums.lean" "Open specifications" _blank
  click inflate href "https://github.com/cla7aye15I4nd/zlib-f/tree/dba8cbbdde28e0ddcfeae060d8ce3005d73210d7/ZlibF/Spec/Public" "Open specifications" _blank
  click deflate href "https://github.com/cla7aye15I4nd/zlib-f/tree/dba8cbbdde28e0ddcfeae060d8ce3005d73210d7/ZlibF/Spec/Public" "Open specifications" _blank
  click back href "https://github.com/cla7aye15I4nd/zlib-f/blob/dba8cbbdde28e0ddcfeae060d8ce3005d73210d7/ZlibF/Spec/Public/Back.lean" "Open specifications" _blank
  click gzip href "https://github.com/cla7aye15I4nd/zlib-f/tree/dba8cbbdde28e0ddcfeae060d8ce3005d73210d7/ZlibF/Spec/Public" "Open specifications" _blank
  click buffers href "https://github.com/cla7aye15I4nd/zlib-f/blob/dba8cbbdde28e0ddcfeae060d8ce3005d73210d7/ZlibF/Spec/Public/Utilities.lean" "Open specifications" _blank
  click lifecycle href "https://github.com/cla7aye15I4nd/zlib-f/tree/dba8cbbdde28e0ddcfeae060d8ce3005d73210d7/ZlibF/Spec/Public" "Open specifications" _blank
  classDef registered fill:#dcfce7,color:#166534,stroke:#166534
  classDef local fill:#dbeafe,color:#1e40af,stroke:#1e40af
  classDef open fill:#e5e7eb,color:#374151,stroke:#374151
  classDef blocked fill:#fee2e2,color:#991b1b,stroke:#991b1b
```

Arrows aggregate actual implementation calls and proof/definition references.
An isolated node has no displayed links; it still needs its own proof. Helper and runtime
dependencies are detailed in [Public API proof readiness](./overview.md#public-api-proof-readiness).
Green requires checked, registered proofs for every
target in a group. Readiness labels identify reviewed next work without changing proof
status. Unreviewed prerequisites remain explicit. See the [representation limits](./trusted-base.md).

Click a group to open its specifications. If diagram links are disabled, use the
[group index](progress.md#clickable-index). [The detailed graph](progress.md) shows every
public API target separately, with links to its contract, statement and proof evidence.
Diagram links use the fixed GitHub snapshot `dba8cbb` and survive merges
and branch deletion. Table links remain relative to this document.
Refresh with `python3 scripts/proof-progress.py` after proof changes.
<!-- proof-progress:end -->

## Reading this status

The generated graph above records registered targets for this checkout. A local
build or a theorem for a restricted domain is not acceptance of the full API.
Results in other branches require integration and checks on their exact commit.

[Archived checkpoints](history/proof-checkpoints.md) preserve the earlier
per-module reports, measurements and publication history. They are not a second
current-status page. Do not append build transcripts or release diaries here.

## Remaining work

### Public API proof readiness

The table names the remaining public obligations in this checkout. Internal
results are useful only when their conclusions establish the next caller's
premises on the same execution. Narrower domains must stay explicit.

<!-- proof-readiness:start -->
| Public targets | Proof work shown in graph | Next work and missing prerequisite |
| --- | --- | --- |
| `gzopen`, `gzopen64`, `gzdopen`, `gz_initialisation_domain`  | Start: open and cleanup | <a id="readiness-gzopen"></a> **Start:** common mode loop, allocation outcomes, path formatting/copy, descriptor effects, `OpenState` and witnesses. Entry/failure branches are locally checked above. |
| `gztell64`, `gztell`  | Needs: position history | <a id="readiness-gztell64"></a> **Compose:** derive `PosInv` from reads, writes, seeking and pushback; then reuse the existing arithmetic execution proof. |
| `gzclose_r`  | Needs: resource history | <a id="readiness-gzclose-r"></a> **Start:** initialized-buffer cleanup and its ownership producer over histories. Unbuffered execution and frame are locally checked; `inflateEnd` alone is insufficient. |
| `gzclose_w`, `gzclose`  | Needs: flush and cleanup | <a id="readiness-gzclose-w"></a> **Compose:** actual zero-fill/final compression and file writes, all cleanup/error paths, then dispatch using both complete close results. |
| `gzseek64`, `gzseek`  | Needs: seek and history | <a id="readiness-gzseek64"></a> **Start:** position/pointer history invariants, buffered and transparent paths, exact error frames. Negative-position reachability and historical overflow reports remain **to confirm**. |
| `gzdirect`, `gzread`, `gzfread`, `gzgetc`, `gzgetc_`, `gzgets`, `gzungetc`  | Needs: reader path proofs | <a id="readiness-gzdirect"></a> **Start:** common lazy setup, transparent reads and buffer/history invariants. **Compose:** actual decoder execution for compressed paths, then EOF/count/pushback/error clauses. `gzdirect` needs detection and init, not the full data-decoding loop. |
| `gzwrite`, `gzfwrite`, `gzputc`, `gzputs`, `gzvprintf`, `gzprintf`, `gzflush`, `gzsetparams`  | Needs: writer path proofs | <a id="readiness-gzwrite"></a> **Start:** buffering, formatting, transparent writes and failures. **Compose:** actual compressor execution for compressed output and parameter changes. |
| `deflateInit2_`, `deflateInit_`, `deflate_initialisation_domain`  | Start: init and allocation | <a id="readiness-deflateinit2"></a> **Start:** parameter normalization, five allocations, all failure cleanup, actual `DGood`/tree establishment and witnesses. Reset proofs require the invariant; they do not establish it for fresh storage. |
| `deflatePrime`  | Start: compaction and bits | <a id="readiness-deflateprime"></a> **Start:** pending-byte compaction, checked shifts, bit insertion/flush and invariant/frame preservation. Refusal branches are locally checked; accepted counts remain open. |
| `deflateBound_z`, `deflateBound`  | Start: bound and header review | <a id="readiness-deflatebound-z"></a> **Start:** connect existing execution formulas to the saturated mathematical bound, including header strings and extra lengths. The historical extra-length report is **to confirm**, not a newly confirmed blocker. |
| `deflateSetDictionary`  | Start: window and hash | <a id="readiness-deflatesetdictionary"></a> **Start:** window fill, hash-chain insertion, saved-input restoration, then checksum and exact state/frame effects. Green checksum calls cover only that part. |
| `inflateCopy`, `deflateCopy`  | Start: copy and relocation | <a id="readiness-inflatecopy"></a> **Start:** allocation failures, buffer copies, pointer relocation and independent ownership. Resolve the recorded copy/history investigations before claiming the full domain; do not add silent premises. |
| `deflateParams` | Needs: block flush and parameter state | <a id="readiness-deflateparams"></a> **Compose:** actual old-block flushing, return-code handling and canonical tuning-row updates. Check exact state preservation on refusal before full closure. |
| `inflateSync`  | Needs: scan and history | <a id="readiness-inflatesync"></a> **Start:** compose existing first/resume scans, held bits, marker search, reset and accounting/frame results. Derive window/reset premises from histories. |
| `compress2_z`, `compress2`, `compress_z`, `compress`  | Needs: compressor execution | <a id="readiness-compress2-z"></a> **Start:** arguments, scalar lengths and cleanup. **Compose:** actual init/compress/end with exact output, then wrappers. Abstract roundtrip is insufficient. |
| `uncompress2_z`, `uncompress2`, `uncompress_z`, `uncompress`  | Needs: decoder execution | <a id="readiness-uncompress2-z"></a> **Start:** scalar results, insufficient space and cleanup. **Compose:** actual init/decompress/end, exact consumption/output, then wrappers. |
| `inflate`, `deflate`  | Needs: dispatch invariants | <a id="readiness-inflate"></a> **Compose:** decoder-table or hash-chain meaning, dispatch invariants, loop termination and output/accounting. Green checksums do not establish these premises. |
| `inflate_sequence`, `deflate_sequence`, `inflate_back_sequence`, `gz_sequence`  | Needs: execution and format | <a id="readiness-inflate-sequence"></a> **Compose:** actual per-call safety, history preservation, independent format refinement and completion across input/output splits. |
| `inflateBack` | Needs: tables, window and callbacks | <a id="readiness-inflateback"></a> **Compose:** compressed TABLE/LEN execution, output inside the window, public callback ownership, loop termination and exact input/output accounting. Existing stored and entry paths can progress independently. |
| `inflateInit2_`  | Blocked: cleanup contract | <a id="readiness-inflateinit2"></a> The confirmed cleanup-contract counterexample is [recorded below](#inflate-initialization-cleanup). Successful init and independent targets can proceed. |
<!-- proof-readiness:end -->

### Stream proof route

Use [stream composition](proof/stream-composition.md) for the producer/consumer
interfaces. Fix the target and boundary relation first. Every new branch result
must name its producer and its next consumer. A missing connection is an explicit
proof obligation, not evidence that a public target has been proved.

### Inflate

Compose initialization, entry, actual mode dispatch, bounded loops and all exits
under one persistent relation. Derive table and pending-state facts where the
code establishes them. Cover the public byte views, partial copies, window
allocation failure and every admitted history operation. Finish independent
format refinement and completion over those same executions.

The existing restricted default results must retain their stated buffer,
wrapper and history scope. They do not prove the unrestricted public target.
[Earlier evidence and interface details](history/proof-checkpoints.md#inflate-route-readiness)
remain available for reuse.

### Deflate

Complete the initialized engine relation, strategy loops, output/symbol overlay
bound and encoded-output history. Connect each restricted result to the public
buffer and operation domain. Default level 6 and memory level 8 results do not
cover all accepted parameters. Compose counter, frame and ownership effects on
the same run before claiming the full public contract.

[Earlier default-route evidence](history/proof-checkpoints.md#default-memory-overlay-route)
records reusable components and their precise limitations.

### Trees

Finish tree-description decoding, full bit-cost refinement and block emission.
Derive every output-room premise from actual caller state and the overlay bound,
including small memory levels. Existing constructor and sender results are
internal execution results, not public deflate acceptance.

### Other APIs

Finish callback compressed blocks and callback histories, buffer utilities,
gzip open/read/write/seek/close and their allocation-failure paths. The readiness
table above records the entry-specific work. Independent paths can proceed
without waiting for the complete ordinary stream engines.

### Specification review

#### Gzip seek mode
<!-- proof-blocker: ZlibF.Spec.Api.Goal.gz_seek_read -->

The abstract seek relation permits a read handle to change mode. The
[counterexample](../tests/verification/counterexamples/gz-seek-mode.lean)
requires contract review. This is a model issue, not a confirmed source defect.

#### Inflate initialization cleanup
<!-- proof-blocker: ZlibF.Spec.Public.Goal.inflateInit2_ -->

The current `inflateInit2_` goal is false for an invalid window parameter. Its
`SameObjects` postcondition requires a structurally unchanged state table, but allocation
followed by free expands that table. The [checked counterexample](../tests/verification/counterexamples/inflate-init2-table-shape.lean)
uses a valid caller heap and proves the sizes are four and zero. Review the contract and
model before proving this goal. This is not a confirmed zlib issue.

This counterexample uses `windowBits = 1`. The default `inflateInit_`
entry fixes it to 15 and has an existing checked public contract, including
allocation failure. Continue the selected default-entry route without
waiting for a correction to the invalid-window target. Successful
initialization at other accepted parameters also has independent proof
evidence; it does not require this false error-path postcondition.
The local `inflate_init2_valid_public` now retains the full existing contract
at every accepted argument, including allocation failure and entry refusals.
Fresh kernel replay of that module passes. Three direct initialization
mutants are rejected in the original initialization function proofs: changed
default window bits, changed ABI size and changed allocation-error return.
The default-entry boundary and its concrete platform witness also pass fresh
kernel replay. The root build, zero-placeholder scan and allowed-axiom
inspection pass locally.
These local checks do not establish CI acceptance of the new results.

Review the corrected shared `Uncompress2` relation independently. The deferred-distance and
exact-free corrections have independent counterexamples and checked regression proofs;
implementation refinement remains open. Its former empty-output clause on memory failure and
extension clause on buffer error have been removed using the existing paired counterexample.
Complete the older abstract gz and dictionary models before using them as complete operational
refinements; the concrete public targets do not assume their callee contracts.


### Integration and acceptance

Integrate existing proof sources in small batches. Run checks asynchronously on
fixed commits; keep their results and logs outside this status page. Do not
regenerate locks for every local lemma. Semantic lock changes still require the
existing independent review. Final acceptance still requires the required CI on
the named commit. Differential tests are evidence of fidelity, not proof.

### Historical reports to recheck

Recheck the retained gzip arithmetic, recovery, seek and parameter reports
against the current source pin. Establish concrete reachability before claiming
a source defect. The callback history report remains unconfirmed. See
[findings](findings.md), [patches](../patches/README.md) and the
[archived investigation details](history/proof-checkpoints.md#historical-reports-to-recheck).

## Objectives

| ID | Required property |
| --- | --- |
| P1 | Safety and no leaks. |
| P2 | Termination without fuel exhaustion. |
| P3 | Frame: only permitted storage changes. |
| P4 | Invariants and ownership across legal call sequences. |
| P5 | Functional correctness against independent specifications. |
| P6 | Coverage of every upstream CI configuration. |
| C1 | Checksum updates and combinations match their definitions. |
| C2 | Decoding produces justified prefixes, completes under stated conditions and safely reports detected invalid data; memory failure and incomplete input remain explicit. |
| C3 | Completed compression encodes accepted input; compatible decoding recovers it across permitted parameters, splits and flushes. |
| C4 | Header capture and dictionary checks have exact API effects; checksum equality is not dictionary byte equality. |
| C5 | Output-bound adequacy under its documented conditions, separately from numeric equality. |
| C6 | Independent copied ownership and matching continuation; specified reset behaviour. |
| C7 | Gzip data, positions and cleanup across read/write/seek/close histories. |

## Working rules

| ID | Rule |
| --- | --- |
| R1 | Prove actual callees; never assume their contracts. |
| R2 | Init establishes the shared invariant; top-level claims also need witnesses. |
| R3 | Carry safety and functional history through the same actual states. |
| R4 | Connect execution, translation and independent specifications by refinement. |
| R5 | Allowed axioms only; no placeholders or unchecked proof shortcuts. |
| R6 | State narrower domains explicitly and record them in deviations. |
| R7 | Correct translation mismatches for fidelity, never to ease a proof. |
| R8 | Retain C naming/source correspondence; separate heap-free mathematics. |

## Acceptance

Fix the questions, review the baseline, prove exact targets with init/non-vacuity
and proof mutants, then pass final checks on a named commit. The
[checking guide](checking/README.md) defines each stage. Tests are finite evidence.
Read [design](design/README.md), [proof method](proof/method.md),
[safety](safety.md), [trusted base](trusted-base.md) and [limits](deviations.md)
for the full requirements.

## Archived section links

Old section links lead to the preserved checkpoint record below.

<a id="callback-decoder-prerequisites"></a>
[Archived: callback decoder prerequisites](history/proof-checkpoints.md#callback-decoder-prerequisites)

<a id="checked-table-clause-composition"></a>
[Archived: checked table clause composition](history/proof-checkpoints.md#checked-table-clause-composition)

<a id="copy-and-borrowed-header-investigations"></a>
[Archived: copy and borrowed header investigations](history/proof-checkpoints.md#copy-and-borrowed-header-investigations)

<a id="crc-address-model"></a>
[Archived: crc address model](history/proof-checkpoints.md#crc-address-model)

<a id="decode-tables"></a>
[Archived: decode tables](history/proof-checkpoints.md#decode-tables)

<a id="default-memory-overlay-route"></a>
[Archived: default memory overlay route](history/proof-checkpoints.md#default-memory-overlay-route)

<a id="differential-harness"></a>
[Archived: differential harness](history/proof-checkpoints.md#differential-harness)

<a id="end-to-end-claims"></a>
[Archived: end to end claims](history/proof-checkpoints.md#end-to-end-claims)

<a id="inflate-back"></a>
[Archived: inflate back](history/proof-checkpoints.md#inflate-back)

<a id="inflate-causal-model"></a>
[Archived: inflate causal model](history/proof-checkpoints.md#inflate-causal-model)

<a id="inflate-route-readiness"></a>
[Archived: inflate route readiness](history/proof-checkpoints.md#inflate-route-readiness)

<a id="integration"></a>
[Archived: integration](history/proof-checkpoints.md#integration)

<a id="next-work-for-every-unfinished-public-target"></a>
[Archived: next work for every unfinished public target](history/proof-checkpoints.md#next-work-for-every-unfinished-public-target)

<a id="open-query-and-close-prerequisites"></a>
[Archived: open query and close prerequisites](history/proof-checkpoints.md#open-query-and-close-prerequisites)

<a id="proof-mutants"></a>
[Archived: proof mutants](history/proof-checkpoints.md#proof-mutants)

<a id="public-contracts"></a>
[Archived: public contracts](history/proof-checkpoints.md#public-contracts)

<a id="recorded-checkpoint"></a>
[Archived: recorded checkpoint](history/proof-checkpoints.md#recorded-checkpoint)

<a id="translation-review"></a>
[Archived: translation review](history/proof-checkpoints.md#translation-review)
