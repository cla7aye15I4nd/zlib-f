The [allocation trace](/sample/allocation.html) gave the compressor a state, window, predecessor array, hash heads and pending buffer. It also followed a failure that occurred before all five were available. The [state operations](/sample/state-operations.html) then reused, branched or released those objects. The proof must follow those same objects through actual translated calls, rather than starting by assuming that every useful fact already holds.

## Initial objects {#establishment}

The public initialization statements distinguish caller storage from the state they establish. [`InitDomain`](/reference/source/ZlibF/Spec/Public/Domains.html) describes fresh identities, unique object representation, library globals, readable version information and a writable non-live stream with compatible allocator fields. It supplies no post-initialization library invariant and assumes no callee contract.

[`InflateInitial` and `DeflateInitial`](/reference/source/ZlibF/Spec/Public/Initialisation.html) describe successful results on the returned heap. They include concrete field settings, the stream representation and an exact allocation ledger. The deflate result identifies five new owned identities; the inflate result starts with one state and a NULL window. The initialization proof must derive these facts from the actual writes and allocation outcomes.

This is also a non-vacuity obligation. A preservation statement with an impossible premise proves nothing useful about an application. The initialization-domain targets quantify over accepted parameter combinations and permitted non-failing allocations, then require successful actual execution. A fixed `witnessHeap` additionally demonstrates that the caller domain can hold. That one witness supplements universal coverage; it does not replace the other window sizes or compression settings.

## Representation and reachable history {#representation}

[`Zlib.Inflate.Spec.Good`](/reference/source/ZlibF/Proof/inflate.c.base.html) bundles a live stream, `StInv`, `Uniq` and `Fresh`. Its window clauses describe the actual allocation, capacity, valid byte count and ring indices. Its table-pointer clauses distinguish the embedded codes from static fixed tables. Its fixed array extents matter: a Lean array value alone does not enforce the corresponding C declaration's length.

[`Zlib.Deflate.Spec.DGood`](/reference/source/ZlibF/Proof/deflate.c.base.html) similarly includes a live compressor, storage/size constraints, uniqueness, freshness and a tree invariant. Non-NULL allocator fields in a live-state check are not the separate `DefAlloc` assertion that the represented allocator/free callbacks are the supported default functions.

These are concrete representation predicates, not a complete account of algorithmic history. Shape facts do not alone identify a window's logical bytes or establish that a table entry implements the canonical code. The relations used for refinement must connect those meanings to the same returned heap.

[`StreamReachable`](/reference/source/ZlibF/Spec/Public/History.html) records actual successful initialization, actual returning operations, permitted caller rebuffering and successful copies. A recorded execution equation is evidence that the call happened; it does not grant its specification for free. `StreamSequenceSafety` requires the invariant as a conclusion about every admitted history, and requires the next admitted call to return. It must do more than preserve an invariant conditionally when a caller assumes one.

## Fresh identities {#identity}

The heap stores different object kinds in typed tables. A byte block and a state record cannot silently share one allocation identity. `Uniq` states that at most one of those tables contains an object at each block number.

[`C.Fresh`](/reference/source/ZlibF/Runtime/Schema.html) states that every identity from `nextBlk` onward is unused. An allocating proof must preserve that condition as the counter advances. `Fresh` and `Uniq` have different jobs: the first protects future allocation, the second protects the interpretation of existing identities. Neither alone says that two specific stream-owned buffers are suitably separated; the corresponding representation clauses must establish that too.

Arbitrary fresh integer contents also remain in scope. Allocated capacity is not evidence that a predecessor or pointer field was written. The [safety reference](/reference/docs/spec/safety.html) explains the model's fixed integer garbage and fresh-NULL pointer convention. Establishment needs write-before-read evidence where the runtime cannot detect an omitted pointer write.

## Frame and live-block accounting {#ledger}

[`Frame`](/reference/source/ZlibF/Spec/Public/Initialisation.html) protects existing allocations outside an explicit changed set. It also preserves statics, allocation-oracle and garbage functions, while allowing the fresh-identity and allocation-attempt counters to advance. It is not whole-heap equality.

The separate `LiveChange` definition supplies the exact ledger:

```text
after.live b ↔ (before.live b ∧ ¬ removed b) ∨ created b
```

For successful init, `created` names the new owned blocks. For failed init, no new live block remains and no old live block is removed. For End, the removed set is precisely the old stream-owned set. The failed five-request trace must account for later successful allocations even after an earlier buffer request failed.

Caller output needs finer boundaries than an object-wide frame. [`BufferFrame`](/reference/source/ZlibF/Spec/Public/History.html) preserves byte-array sizes and bytes outside the union of authorized regions. It allows the delivered prefix or registered header destinations to change without granting arbitrary modification of the rest of their allocations.

## Reset and copy obligations {#operations}

For Reset, unchanged allocation identities and changed logical history must coexist. [`inflateResetPre` and `DeflateResetContract`](/reference/source/ZlibF/Spec/Public/Lifecycle.html) state which counters, pointers and history fields change. An incompatible decoder window can disappear from the owned set; ordinary compressor reset retains its allocations and clears the dictionary hash. A conditional reset theorem requiring `DGood` cannot establish `DGood` for a new allocation: initialization must first construct the required state and tree facts.

[`relocateCode`, `copiedDeflate` and the copy targets](/reference/source/ZlibF/Spec/Public/Copy.html) describe equal progress with independent storage. Static code pointers can remain shared; references into copied embedded arrays move to the new identity. Pending cursors and tree descriptors require corresponding relocation. The source stream/state is preserved, and failure leaves no newly owned destination blocks. A correct byte copy alone would miss these pointer and ownership obligations.

## Counterexamples and scope {#scope}

The [method record](/reference/docs/proof/method.html#one-representation-invariant) describes an earlier invariant admitting a gzip EXTRA phase with a NULL header. That conditional execution exposed a missing state relationship. It did not establish that permitted public histories could reach it, and did not justify excluding a legal caller input.

The [contract review](/reference/docs/checking/contract-review.html#counterexamples-to-the-old-statements) also records an old table query admitting `2^63` slots instead of the actual embedded extent. A counterexample to that representation question required a reviewed statement correction, not a disguised proof shortcut. Distinguish a proof-technique failure, wrong specification, translation mismatch and actual C defect before changing any premise.

The broader composition of history, pointer initialization and functional meaning remains **to confirm** through the corresponding execution proofs. Advanced operations retain their per-entry effects and sequence-safety obligations; ordinary format epochs do not automatically refine every combination of dictionary replacement, priming and recovery. Definitions and local results named here locate evidence, not full acceptance. The [complete method](/reference/docs/proof/method.html), [stream composition](/reference/docs/proof/stream-composition.html) and [current progress](/reference/docs/progress.html) retain the exact obligations, scopes and named-commit acceptance evidence.
