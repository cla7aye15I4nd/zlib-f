# Stream compression: window, chains and lifecycle

Source: `zlib/deflate.c`; translation: `ZlibF/Zlib/deflate.c.lean`.
The [API guide](../api/README.md) gives public behavior. Internal contracts use
`I-fw-*`, `I-sh-*`, `I-hc-inv`, `I-lm-*` and `I-fp-*` in
[internal contracts](../design/internal-contracts.md). Tree construction and the
shared-buffer bound F9 are explained in [trees](trees.md).

This page gives the proof structure and its internal premises. Conditional
results over `DGood` or a search invariant need an initialization and
preservation bridge before they imply public correctness. Current accepted
scope and remaining work are recorded only in [the overview](../overview.md).

## Storage and size equations

```mermaid
flowchart LR
    Stream["Caller z_stream"] --> State["Owned deflate_state"]
    State --> Window["window: 2W bytes"]
    State --> Prev["prev: W positions"]
    State --> Head["head: hash_size positions"]
    State --> Pending["pending_buf: 4B bytes"]
    Pending --> Symbols["sym_buf starts at offset B"]
    State --> Header["Caller gzip header"]
    State --> Tables["Read-only code tables"]
```

The stream owns five blocks: state, window, `prev`, `head` and pending storage.
The caller owns the stream, its input/output views and any gzip header buffers.
Embedded trees, heap and depth arrays belong to the state block.

Validated default-build parameters give these equations:

| Field | Value |
| --- | --- |
| `w_bits` | Normalized window parameter, with 8 changed to 9 |
| `W = w_size` | `1 << w_bits`, so `512 ≤ W ≤ 32768` |
| `window_size` | `2W` |
| `hash_bits`, `hash_size` | `memLevel + 7`, `1 << hash_bits` |
| `B = lit_bufsize` | `1 << (memLevel + 6)`, from 128 to 32768 |
| `pending_buf_size` | `4B` |
| `sym_buf`, `sym_end` | `pending_buf + B`, `3(B - 1)` |

These equations describe the default shared-symbol branch; configurations such
as a different symbol layout need their own refinement. Allocation products
must fit the allocator's 32-bit unsigned multiplication. The largest buffer
products here are 131072 bytes. State-size and ABI assumptions are separate.

The normalization to `W ≥ 512` is load-bearing:
`MIN_LOOKAHEAD = 262`, `MAX_MATCH = 258`, `MAX_DIST = W - 262 ≥ 250`.
Without it, a 256-byte window would make the distance subtraction wrap.

## Symbols and signed block positions

The symbol ledger ties each stored three-byte symbol to the leaf
frequencies in the same state. Distance zero means a literal; a positive
distance stores a length offset from three. A symbol represents at most
258 input bytes. With at most `B - 1` symbols, the represented byte count
is at most `258 * (B - 1)`. Each literal/length leaf frequency is at most
the symbol count plus one; each distance leaf is at most the symbol count.
The extra one is the end marker established by the actual initializer.
These bounds justify UInt16 increments without assuming no wrapping.
Summing the actual literal/length leaf frequencies gives exactly the
symbol count plus one. Summing the distance leaves gives at most the
symbol count. The proof counts each symbol once in its selected leaf;
it does not multiply a per-leaf upper bound by the alphabet size.
Thus the initial tree weight budget is at most B, with a strict bound
for the distance tree, before any source-prescribed dummy leaves.

The block balance is

```text
strstart - block_start = represented_bytes(symbols) + credit
```

At a regular slow-strategy boundary, credit is zero or one for a deferred
byte. At intermediate cutpoints it can be negative: tallying a match
subtracts its whole length before the source advances through that match.
Literal tally subtracts one, and one-byte traversal adds one.
Sliding subtracts the window size from both positions and preserves the
balance. The capacity bound controls a negative block_start and justifies
its checked signed subtraction. For default memory level 8, B is 16384;
the general shared-buffer bound permits B up to 32768.

The initialization bridge must retain actual leaf values, not just the
array extents in DGood. The tally bridge must retain both actual packed
bytes and the corresponding natural-number histogram on its returned
heap. Extent-only contracts cannot supply either fact.

## D: window bounds and `fill_window`

The shape invariant **D** is

```
strstart + lookahead ≤ window_size = 2W
```

Initialization starts both counters at zero. Reading input increases lookahead
by no more than the available window room. Consuming bytes advances `strstart`
and decreases lookahead by the same count. The proof must establish D at every
entry and strategy-loop point that uses it.

`I-fw-pre` additionally provides `lookahead < MIN_LOOKAHEAD`, valid sizes/masks,
`insert ≤ strstart`, a bounded high-water mark, search settings and the
hash-chain invariant. With the current D, the default branch computes
`more = window_size - lookahead - strstart` without loss from the relevant
unsigned subtractions and casts.

If `strstart ≥ W + MAX_DIST = 2W - 262`, then `more ≤ 262 - lookahead < W`.
The slide copies `W - more` bytes from `[W, 2W-more)` to `[0, W-more)`.
Both ranges are in the window and disjoint. The code adjusts `match_start`,
`strstart`, signed `block_start`, `insert`, hash positions and free room.

Each adjustment needs its own type argument. `strstart ≥ W` justifies its
subtraction. It does not show that `match_start ≥ W`: an unsigned stale match
position may wrap, and the proof must show when that value can subsequently be
used. Signed `block_start -= (long)W` must remain in range under its actual
invariant. Model the source expression and conversions exactly.

The sliding proof keeps a source-equal contiguous prefix: window copy,
match and current positions, signed block position, insertion clamp,
then both hash-rescaling loops. The new machine strstart is the old
position minus W. The logical input origin increases by W, so retained
match witnesses can continue to use modular distances even when an old
match_start wraps. Private pending bytes and their frequency ledger stay
unchanged.

After this prefix, the real outer-loop body agrees with a non-sliding
body on that returned heap. Equality of first body evaluations gives
equality of the remaining do-while computation, with the same condition
and remaining fuel. The non-sliding execution supplies the actual read,
checksum, re-priming and padding result. With no input the body still
slides before it exits; the generic high-water proof then supplies any
required padding without assuming the new window is already padded.

After the slide, `more += W` again measures room beyond data. If input remains,
`read_buf` copies at most that room into
`window + strstart + lookahead`. The insertion loop hashes only available
three-byte strings, masks `ins_h` to `hash_size` and writes the corresponding
`prev`/`head` cells. Establish how pending `insert` positions relate to the
current window contents.

The high-water initialization writes no farther than `window_size`: either it
extends after the new data by `min(window_size-curr, WIN_INIT)`, or it extends
from the old high-water mark by the smaller of the desired extension and the
remaining capacity. Bound both branch-specific subtractions before using them.
These writes also support the initialization history of later reads.

`I-fw-post-room` gives `strstart ≤ window_size - MIN_LOOKAHEAD`. The slide test
runs before the no-input exit, so the room argument must cover end-of-input
calls too. **to confirm**: every search caller obtains this bound from either
sufficient lookahead under D or a call to `fill_window`, including strategy
changes and resumed calls. A source reading of one loop does not prove it for
all strategies.

A non-sliding refill has real free room whenever the source lookahead
test requests it. Read at the old valid endpoint. Re-prime the rolling
hash at the current strstart, rather than at allocation offset zero.
After the source condition stops the outer loop, extend high-water
padding beyond the new valid endpoint. Retain the caller-input prefix
in the logical history and append the newly accepted bytes there.

```mermaid
flowchart LR
    R[Read at the old endpoint] --> L[Update lookahead]
    L --> H[Prime at strstart]
    H --> C[Check outer condition]
    C --> P[Extend high-water padding]
    P --> J[Return the engine boundary]
```

## H1/H2: meaningful hash-chain reads

The source leaves `prev` uninitialized and fills it on demand. Safety must hold
for arbitrary contents of the other slots. Let a position be **inserted** when
an insertion operation records its three-byte hash, with its identity adjusted
by window slides and invalidated by hash clearing. Position zero is `NIL`.
With `T = strstart - W` interpreted in the mathematical position domain, use:

- **H1:** Every head is zero or a meaningful inserted position within the current
  represented data range.
- **H2:** For each retained inserted `q > T`, `prev[q & wmask]` contains its recorded
  predecessor after slide adjustment, either zero or a smaller inserted position
  with the relevant hash.

These clauses express `I-hc-inv`. Their exact temporal/range formulation must
cover insertion in `fill_window` and dictionaries as well as the strategy
macros. Membership in an allocated `prev` array alone proves no such fact.

`CLEAR_HASH` writes the last head and zeroes the preceding heads. The head map
is then empty; there is no need to initialize every `prev` slot. An insertion
writes its predecessor slot before publishing its position in the head. A
proof must track insertion order and show that overwriting the slot for a
position one window behind cannot destroy a retained link.

`slide_hash` visits every head and `prev` slot. It transforms every 16-bit value
m by `m ≥ W ? m-W : 0`. This is safe even for garbage. For meaningful links,
prove that the transformation agrees with new window positions and preserves
the mask slot, since subtracting W preserves the residue modulo W. Discarded
positions become `NIL`; arbitrary unused slots remain outside H2's domain.
The `do … while (--n)` loops start with positive sizes and have fixed bounds.

Dictionary insertion and copying must preserve these relationships. Copying
all of `prev` also copies garbage; that is permitted by the runtime rules.
No argument may infer that every copied slot was initialized.

## `longest_match`: F5 and F6

`I-lm-pre` supplies a nonzero matching head below `strstart`, distance at most
`MAX_DIST`, H1/H2, a room bound, a valid previous length and a positive effective
search budget. The first head is therefore in the retained H2 range.

Set `limit = max(strstart-MAX_DIST, 0)`. The first body may have
`cur_match = limit` when the distance is exactly `MAX_DIST`: the body is a
`do` loop. A continuing body requires the next predecessor to be strictly
above limit. Do not use that continuation test as an extra premise for the
first body.

At each reached predecessor read, H2 shows that the slot was initialized for
that position and contains zero or a smaller meaningful position. The loop test
rejects zero and out-of-range predecessors. This is **F5**: garbage may be
rescaled, but it is not used as a chain address.

The bounded-window argument is **F6**. `scan` starts at `window + strstart` and
`match` at an earlier valid position. Previous-match sentinels use a length at
most 258. The default comparison loop advances from offset 2 in groups of eight
up to offset 258, since `258 - 2 = 8 × 32`. The room premise gives
`strstart + 258 < window_size`, so every such comparison is in bounds. Alternate
unaligned comparison branches require their actual width/alignment proof.

These comparisons may inspect arbitrary bytes beyond real lookahead. Such a
read is allowed for the modeled integer bytes, but the returned match is
clamped to lookahead. Functional correctness must show that the selected match
agrees on the real data; no-fault reasoning alone does not prove independence
of garbage.

For termination, meaningful predecessor positions strictly decrease. The
configured chain budget also bounds the walk. **to confirm**: the budget stays
positive after its `>>= 2` reduction whenever that branch applies, including
values permitted through `deflateTune`. If a zero budget wraps on decrement,
unsigned wrapping is defined; it still invalidates a proof that assumes that
budget strictly decreases to zero. Use only bounds justified by the exact
contract.

The actual insertion result supplies two different facts at different times.
Before insertion, a nonzero returned head is below the old insertion frontier,
which is no later than `strstart`. After insertion, the head names `strstart`
and its predecessor cell names that returned head. Use the first fact for
candidate order and the latter facts for chain provenance. A post-insertion
NIL head at position zero does not constrain arbitrary old prev contents.
The heap bridge derives matcher storage from DGood and comparison room from
D plus sufficient lookahead. It does not assume the matcher's contract.

The slow strategy decreases lookahead before inserting the consumed match
positions. Its insertion loop therefore needs three valid bytes, not the
262-byte matcher entry condition. For a previous length from 3 through 258,
that source update leaves at least five lookahead bytes. The positive
prev_length counter after subtracting two is at most 256. Use that actual
heap counter as the do-while rank. Keep strstart plus the counter constant
while each insertion advances the primed rolling hash. The final source
increment restores the original strstart-plus-lookahead endpoint.

A pending literal also needs strstart to be positive when match_length is
below three. Keep this fact separately from the conditional match witness.
Initialization has no pending literal, and every source decision preserves
the implication from a pending literal to a consumed previous byte.

The result returns `min(best_len, lookahead)` and updates `match_start` on an
improvement. Prove its byte-equality and distance facts for callers, including
the case in which stale match state is retained.

## Strategy loops and symbol production

SlowBoundary ties the actual owned arrays to the logical input, current
hash-chain frontier and lazy match history. It also carries the symbol
ledger and block balance. Deferred-byte credit is defined by the actual
match_available flag. Initialization supplies this boundary with no
symbols and an empty input view.

```mermaid
flowchart LR
    Init[Default initialization] --> Boundary[SlowBoundary]
    Boundary --> Search[Actual insertion and search]
    Search --> Match[Match tally and consumption]
    Search --> Literal[Literal tally and advance]
    Search --> Defer[Defer one byte]
    Match --> Boundary
    Literal --> Boundary
    Defer --> Boundary
```

The non-flushing body appends at most one real symbol. A selected match
starts with one deferred byte, tallies the full previous match length,
then advances through the remaining length minus one. Its credit returns
to zero. A literal spends one credit and restores it by advancing one
byte. Deferring emits no symbol and changes credit from zero to one.
The exact record frame retains all fields outside the source writes.
In particular the buffer geometry, block_start, high_water and wrapper
configuration are available to the next proof step.

| Function | Required invariant and functional step |
| --- | --- |
| `deflate_stored` | Bound direct input/output copies, pending header rewrites and window retention; track `block_start`, signed/unsigned conversions, and hash-slide bookkeeping for later strategy changes. |
| `deflate_fast` | Insert meaningful positions, prove a selected match, tally valid symbols and preserve D/H1/H2 across flush/return. |
| `deflate_slow` | Also relate deferred literals, `prev_length` and lazy-match decisions to the consumed input. |
| `deflate_rle` | Establish the prior-byte read at `strstart-1` and comparison room through offset 258; emit only valid distance-one matches. |
| `deflate_huff` | Emit the consumed bytes as literals and preserve the same block/flush invariant. |

A symbol consumes three bytes and increases `sym_next` by three. Flushing at
`sym_end = 3(B-1)` bounds every tally write within the symbol region.
For a match, the stored length offset is at most 255 and distance minus one is
at most 32767, so `_length_code` and the 512-entry `_dist_code` lookup are in
range. The branch `256 + (dist >> 7)` is at most 511 under that premise.

These bounds must hold again when `compress_block` reads the symbol. If pending
output overwrote it, the reconstructed distance could be any 16-bit value and
the table index could reach 767. F9 therefore protects later reads as well as
output writes. A total compressed-size bound does not establish F9's prefix
condition. See [trees](trees.md#the-overlay-lemma-f9), including the small
`memLevel` cases.

`block_start` can become negative after a slide. The block-flush macro then
passes a null raw-buffer pointer, so an invariant requiring
`0 ≤ block_start` everywhere is wrong. **to confirm**: the signed interval and
per-branch nonnegative conditions establish each actual window copy and the
stored-length subtraction without hiding that case.

## `deflate`: headers, data and trailers

```mermaid
stateDiagram-v2
    [*] --> Init
    Init --> Busy: zlib header
    Init --> Gzip: gzip wrapper
    Gzip --> Extra: supplied header
    Extra --> Name
    Name --> Comment
    Comment --> Hcrc
    Hcrc --> Busy
    Gzip --> Busy: default header
    Busy --> Busy: strategy steps and partial flushes
    Busy --> Finish: finish complete
    Finish --> [*]
```

The actual source has conditional skips and partial returns inside these
groups. The invariant D7 ties `EXTRA`, `NAME`, `COMMENT` and `HCRC` to valid
`gzhead` storage. An earlier invariant admitted `EXTRA` with a null header;
that counterexample showed a missing reachability condition, not a legal
sequence theorem.

Each header `put_byte` needs pending room. Extra/name/comment loops flush at
capacity and preserve their exact progress counters across output exhaustion.
The subtraction `(extra_len & 0xffff) - gzindex` requires the corresponding
progress bound. Trailer writes require the same room proof. `flush_pending`
uses `pending_out + pending ≤ pending_buf + pending_buf_size` and copies at
most `avail_out`, then updates exact cursors and counts.

Public correctness additionally relates emitted wrapper fields, block bits,
checksums and trailer lengths to the consumed input and selected flush schedule.
A monotone history of whether compression has started matters across refusals:
a failed call must not make a later call look like a fresh stream.

## API lifecycle and error cases

| Functions | Proof boundary |
| --- | --- |
| `deflateInit_`, `deflateInit2_` | Validate parameters and version/size; allocate state and four buffers; establish every field/ownership clause on success and free every successful allocation on failure. The default allocator does not zero storage. |
| `deflateReset`, `deflateResetKeep`, `lm_init` | Distinguish full history/hash reset from retained-state behavior and establish the appropriate phase invariant. |
| `deflateEnd` | Free all owned buffers and state exactly once under every admitted status; return the documented status and clear the state pointer. |
| `deflateSetDictionary`, `deflateGetDictionary` | Read/copy the permitted dictionary views, update wrapper checksum/history and meaningful insertions, and return the exact dictionary suffix. |
| `deflatePrime` | Preserve nonnegative/negative-count behavior and pending/bit-buffer capacity conditions with the source's exact shifts. |
| `deflateParams` | Compose any `deflate(Z_BLOCK)` call and its partial/failure effects before changing strategy, level and hash state. |
| `deflateCopy` | Allocate independent blocks, clean up each failure prefix, copy only the source-prescribed ranges and rebase pending/symbol/descriptor pointers. |
| `deflateBound`, `deflateBound_z` | Prove machine arithmetic and separately prove output adequacy under the contract's configuration/header conditions. A numeric formula theorem is not adequacy. |
| `deflateTune`, `deflatePending`, `deflateSetHeader`, `deflateUsed` | Exact parameter/query/refusal effects, permitted output-cell writes and preservation needed by later data calls. |

Copy's window content range is `high_water`; its `prev` copy includes unwritten
integer cells. Allocation failure may occur after earlier allocations succeeded.
The proof must retain the source's cleanup behavior and destination/source
frames for each case. Callee contracts are proved execution results, never
hypotheses bundled into the top theorem.

The lifecycle theorem composes initialization, calls, reset/dictionary/header/
priming/copy operations and End. The round-trip theorem then connects the actual
emitted stream to independent DEFLATE semantics for every permitted split,
strategy, level and configuration in its domain. Historical restrictions such
as `memLevel ≥ 4` must remain explicit where a theorem has them; they cannot
stand for the full `zlib.h` domain.
