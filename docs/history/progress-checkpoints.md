# Progress checkpoints (historical)

These narrative checkpoints used to follow the generated block of
[progress](../progress.md). They are kept unchanged as a historical record. Counts and
"locally checked" results here describe the state when each entry was written. The current
status and counts are only in the generated block of [progress](../progress.md).

## Recorded checkpoint

The current source includes the following advances. The evidence index above
keeps the exact registration state and input range for each fixed target.

| Area | Established result | Remaining boundary |
| --- | --- | --- |
| Descriptor opening | The complete [`gzdopen` public contract](../../ZlibF/Proof/gzlib.c.dopen-public.lean) and its initialization witness are registered. Allocation failures, descriptor effects, cleanup and the returned heap are included. | Later gzip reads, writes and closing require their own proofs. |
| Default decoder histories | [Scoped sequence safety](../../ZlibF/Proof/inflate.c.default-scoped-sequence-safety.lean) composes actual initialization, permitted operations, recovery, copy and release. The [per-call result](../../ZlibF/Proof/inflate.c.default-history-public-goal.lean) retains the public output, accounting, return-code and memory-frame clauses. | The history domain is explicitly restricted; the unrestricted public decoder and independent sequence-format result remain open. |
| Fast decoding | The [semantic foundation](overview-changelog.md#fast-decoder-semantic-foundation-local) connects root-table decoding to independent length, distance and token meaning, including extra bits and end-of-block. | Complete-loop output composition and its connection to all public caller histories remain open. |
| Compressor initialization | [Fast and slow initialization](overview-changelog.md#memory-aware-fast-initialization) establish their actual initialized boundaries across memory levels 1–9: levels 1–3 for fast and 4–9 for slow. | Later strategy execution and completion across all these configurations remain open. |
| Preset dictionary acceptance | The [configured-window correction](overview-changelog.md#configured-dictionary-window-authorized-repair) matches the default decoder's retained dictionary window. Positive and negative format examples and the no-dictionary equivalence are checked. | This repairs a specification boundary; complete translated sequence correctness and completion remain open. |

Local build, kernel replay and audit evidence for these results is recorded
with its source in [the overview](../overview.md). Remote acceptance is shown by
the [main-branch checks](https://github.com/cla7aye15I4nd/zlib-f/actions?query=branch%3Amain).

### Integration

Review the focused function-manual scopes and regenerate the documentation source-policy lock in a
reviewed audit update. Independently review the new source and kernel-syntax locks and the first
verification baseline. Maintain repository protections for the four checks and protected-path
review. Register newly checked results only after their required checks.

### Public contracts

Independently approve the 103 target statements, caller domains and representation limits before
accepting a verification baseline. Extend the ordinary data-epoch refinement to advanced raw
dictionary replacement and all header/priming/recovery combinations; retain their exact per-entry
effects and unconditional sequence safety. No final correctness claim may silently drop those
obligations.

### CRC address model

The CRC translation now observes a stable origin residue for every represented static or
embedded byte array. Local proofs cover all residues, seeds and readable lengths for both
public CRC update entries, with the same immutable-heap result. The original 47-byte static
input is now a [positive regression](../../tests/verification/regressions/crc-static-address.lean).
The public contracts and caller domains are unchanged. Local evidence still needs final
acceptance checks on the integrated commit.

Extend the representation relation to general ABI layout, effective types, scalar-cell aliases
and byte views of other records. The current address abstraction represents only the low
three bits observed by the CRC alignment test; it is not a complete address-space model.

### Inflate causal model

Complete the universal output and unknown-dictionary refinement against the C. The earlier
whole-lookahead consistency is false; the supporting-bit-prefix correction is reviewed. The fixed
data-error detection lag of eight bytes also has a counterexample; derive a justified replacement
rather than raising the constant without proof. Register the checked `inflate_decodes` model proof,
then establish these conditions for actual decoder runs. Prove the general negative-value priming
bridge, beyond the checked model witnesses and finite execution matrix.

### Differential harness

Keep the new allocation-failure and negative-prime regressions in automated validation. The
test-owned gz handles, input line and deflate buffers are now released. Normal and unsuppressed
sanitizer runs compare all 47,890 inputs. A cleanup mutation confirms that the harness still reports
library state leaked by a missing end call.

### Proof mutants

Complete the remaining legacy lists. Every newly proved public entry must supply direct translation
mutants in the locked mapping and demonstrate failure in its function proof. Unproved entries
acquire their records with their proofs.

### Decode tables

Connect the proved canonical-code coverage and entry-shape lemmas to the heap written by
`inflate_table`; establish the table predicates used by the decoders.

### Inflate

The internal code-length root lookup has a bounded execution result for the actual
constructed table. It pulls at most one input byte, preserves the exact input
cursor and bit stream, and leaves on input exhaustion. This supporting result
does not complete CODELENS, the dispatch invariant or the public inflate goal.
See [the lookup proof](../../ZlibF/Proof/inflate.c.lookup-codes.lean) and
[the cursor proof](../../ZlibF/Proof/inflate.c.input-cursor.lean).

The actual window updater preserves the per-byte-object platform bound and
static storage for an existing window, fresh allocation and genuine allocation
failure. It uses the proved default allocator and ring copies. The platform
bound is an environment premise; this theorem proves preservation through the
operation. It does not complete the public inflate goal, ownership, accounting
or the full caller frame. See [the window proof](../../ZlibF/Proof/inflate.c.window-platform.lean).

The locally checked internal fast body now emits one independent literal/copy token, ends the
block, or rejects an invalid length code, invalid distance code or too-far match without output.
The actual distance result preserves exact remaining bits and equates copying with independent
bytewise history copying. The token relation has checked composition, decomposition and rejection
results against the original format grammar. Whole-fast-call bit origin also checks through the
loop, byte rollback and final writeback. All these results retain the original safety conclusions.

Establish table meaning, suffix stability, compatible leaf flags and saved-window history from
actual construction, installation and init. Complete whole-fast-call output composition and cover
all legal buffer views. Finish the other decode modes, across-call composition, copy and recovery.
These remain internal-domain results, not registered public proofs. The public inflate and sequence
goals remain open.

### Inflate back

Finish table construction, compressed blocks, callback composition and the complete function.

### Deflate

Finish general initialization (`deflateInit2_`), dictionary setting, priming, copying, `fill_window`,
strategy loops and the complete function. The recovered dictionary-query proof builds and rejects
three translation mutants in its own proof; registration remains.

The exact `Goal.deflateInit_` now has a locally checked proof in
`public-deflate-init`. It expands the actual fixed-parameter call at window
15, memory level 8 and strategy 0. Compression level remains arbitrary.
The proof covers version and parameter refusal, all five allocation
outcomes, failure cleanup, the old-object frame and the exact live-object
ledger. Successful execution establishes `DGood`; it is not a caller
premise. A concrete default caller successfully returns that invariant.
The universal `deflateInit2_` theorem remains open and is not a dependency.

The complete root build, full fresh kernel replay, allowed-axiom inspection
and zero-placeholder scan pass locally. Three direct wrapper mutants
reject the original exact public proof in a fresh kernel. Wrong-symbol-limit
and dropped-cleanup mutants retain the synchronized whole-source equality
but fail their execution proofs with type errors. Resource failures are
not counted. The strict entry mutation list also passes.

The exact default-entry proof and its concrete witness are registered.
Generated locks add 72 semantic records and two theorem-type records.
Existing semantic and theorem-type records are unchanged. Acceptance on
a named CI commit remains. These are local results, not CI approval.

### Trees

Actual `gen_codes`, leaf preparation, heap ordering, and the complete merge/root-storage
prefix have checked internal execution proofs. Node bounds and queue facts derive from the
actual descriptor/reset/scan/repair/order execution. Old heap contents, lengths and depths
remain unrestricted. Each merge executes child selection, tail stores, frequency/depth
updates, parent stores and sift-down in source order. The loop terminates and the final root
store has its exact state effect. Actual callee execution theorems are used.

The actual forest and final root store now establish the bit-length representation premises.
The complete actual `build_tree` executes both code-generation calls under explicit storage
and static-table conditions. The installed literal, distance and bit-length descriptors
discharge the table conditions. Every originally nonzero-frequency symbol receives a positive
limited length and its exact reversed canonical word, which fits that length. No callee
contract is assumed. The actual lengths and stored words now agree with the independent
format's canonical codes and complete-code rule. Its decoder returns each originally used
symbol and preserves every trailing bit suffix.

The constructor's exact frame preserves the caller's output invariant and existing bits.
Actual construction followed by sending one used symbol composes on the same heap, with
independently decodable output. Its fifteen-bit room condition is an explicit internal
obligation; derive it from the block/overlay bound. Initialization and arbitrary legal call
histories remain open. These are internal-state results, not a public deflate theorem.

Actual `scan_tree` terminates, writes its sentinel and records exact wrapping frequency
increments for every run. Actual `build_bl_tree` composes both scans, bit-length-tree
construction, the descending search and the unsigned cost update. Source-code words and
descriptors are preserved. Generic search returns 2..18. Actual block initialization and
source-tree construction establish the stronger 3..18 range, literal/distance count ranges
257..286 and 1..30, and all nineteen bit-length values at most seven. A new call-composition
proof retains the END_BLOCK frequency and unchanged bit-length tree through any list of valid
actual tallies that fits the current block. Actual `init_block`, those tallies and all three
constructors then establish the same header-field ranges on one returned heap. This proves
neither the strategy's input-to-tally history nor preservation across block flushes.

The complete actual `send_tree` now terminates and emits exactly the shared run-length
model. The direct-repeat loop includes its final signed decrement. All repetition branches,
the early continue, next-length reads and the final for-loop iteration execute in source
order. The exact heap frame retains both tree arrays and the existing output prefix.
Actual bit-length construction now supplies the two senders' source capacities, length
bounds and fitted words for every positively scanned symbol. Each such word also has its
independent symbol-decoding result on every suffix. These data follow on one returned heap
from actual `init_block`, any legal within-block tally list and all three constructors.
Exact total bit room remains an internal obligation. Finish `send_all_trees`, independent
run-length/header decoding and the output/symbol overlay bound; individual word decoding
does not establish decoding of the complete run-length sequence.

Three code-assignment, eleven scan/reset/repair, five heapify/descriptor, and seventeen
merge/guard/root-store mutants fail their execution proofs. Complete source equality still
checks independently for the synchronized variants. The three code-assignment mutants also
reject with the complete constructor in the build target. Three direct `send_code` mutations
of its length entry, code entry and emitted length fail its emission proof with the complete
build/send composition as the build target. Five scan and eight bit-length-construction
mutants fail their execution proofs while synchronized whole-function equalities still check.
Three tally mutations of the literal index, match index and full-buffer flag fail their
execution proofs while the complete source equality still checks. Eight `send_tree`
mutations of the repeat decrement, first-code decrement, zero-run threshold, extra-bit
width/base, continue guard, next read and final iteration fail their execution proofs.
Their complete synchronized source equalities still check. These results are not registered
or CI-approved. Finish tree-description emission, full bit-cost refinement, block compression
and the overlay bound, including the small memory levels.

### Other APIs

Finish the compression utilities and the gz read/write/open paths.

### End-to-end claims

Instantiate the heap API, connect the history invariant to the format model, and prove sequence
safety, ownership, termination and functional correctness on the supported configurations.

## Inflate completion dictionary handshake

See the [canonical completion finding](overview-changelog.md#inflate-completion-dictionary-handshake)
for the counterexample, evidence boundary and required contract correction.

### Descriptor-open integration checkpoint

The `4927bb0` source freeze on the current main baseline passes the complete
local build, fresh kernel replay and declaration audit: 452 registered
theorems and 90 of the 181 fixed targets. Independent source, registration
and generated-lock reviews pass. All earlier registered statements and
semantic records are preserved. The complete public `gzdopen` proof and
its joint initialization witness share the actual returned heap.

Eight other registrations concern existing abstract API and heap-free
format mathematics. They do not establish translated compression or
decompression. The ordinary compressor, decoder, whole-buffer wrappers
and subsequent gzip I/O still need their complete public proofs.
Named-commit remote CI remains separate from these local checks.
