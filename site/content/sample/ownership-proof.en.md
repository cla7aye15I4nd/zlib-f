The application wants a simple lifetime guarantee: after it initializes a stream, every allowed next call uses valid storage; when an attempt fails or the stream ends, no private object is lost. The difficult cases are concrete. A late buffer allocation can succeed after an earlier one failed. A copied pointer can still refer into the original state. Reset can keep old bytes physically present while making them unusable as history.

Use the [allocation example](/sample/allocation.html): state, window, hash heads and pending storage were allocated, but the predecessor allocation failed. Cleanup must release all four successful objects, including those allocated after the failure. Use the [copy example](/sample/state-operations.html#copy): decoder A has delivered `ABAB`, and the new decoder must continue A without depending on A's private lifetime.

| Error to exclude | Required conclusion on the returned state |
| --- | --- |
| Failed initialization strands the later head/pending allocations | No newly owned live block remains; pre-existing live objects remain |
| Ending A invalidates the copied decoder's private table/window | New owned identities and correctly relocated internal pointers |
| Reset lets a new message use A's discarded `ABAB` | Storage reuse and logical-history reset hold together |
| A permitted next call sees malformed state or writes outside its destination | Init establishes the invariant; actual histories preserve it and the permitted memory frame |

The following predicates and targets state these obligations. Naming one is not a claim that its complete target has been proved. The [progress record](/reference/docs/progress.html) owns current acceptance evidence. The proof must follow these same objects through actual translated calls, deriving the useful facts from initialization rather than assuming them.

## Establish a usable stream through Init {#establishment}

Start before the first allocation. The application supplies a writable stream that does not already own a live zlib state, readable version information and appropriate allocator fields. It need not know the future private window, tables or pointers. If those were already required as premises, Init would not explain how an application obtains a usable stream.

The public initialization statements distinguish caller storage from the state they establish. [`InitDomain`](/reference/source/ZlibF/Spec/Public/Domains.html) describes fresh identities, unique object representation, library globals, readable version information and a writable non-live stream with compatible allocator fields. It supplies no post-initialization library invariant and assumes no callee contract.

[`InflateInitial` and `DeflateInitial`](/reference/source/ZlibF/Spec/Public/Initialisation.html) describe successful results on the returned heap. They include concrete field settings, the stream representation and an exact allocation ledger. The deflate result identifies five new owned identities; the inflate result starts with one state and a NULL window. The initialization proof must derive these facts from the actual writes and allocation outcomes.

For the successful default compressor, “five new identities” means state, window, predecessor, head and pending, with distinct owned storage and fields that point to it. For the failure example, that success postcondition is inapplicable: the failure branch has its own status and cleanup conclusions. A proof must classify the actual allocation outcomes rather than quietly assuming the successful branch.

This is also a non-vacuity obligation. A preservation statement with an impossible premise proves nothing useful about an application. The initialization-domain targets quantify over accepted parameter combinations and permitted non-failing allocations, then require successful actual execution. A fixed `witnessHeap` additionally demonstrates that the caller domain can hold. That one witness supplements universal coverage; it does not replace the other window sizes or compression settings.

## Keep the next call safe through actual histories {#representation}

At A's `ABAB` checkpoint, the next match needs more than “a pointer exists.” It needs a live window of the right capacity, a count of valid history bytes and indices that locate those bytes. A dynamic decoding-table pointer must select an entry inside the state that actually owns it. These persistent facts are bundled into a representation invariant so every function uses the same account of the state.

[`Zlib.Inflate.Spec.Good`](/reference/source/ZlibF/Proof/inflate.c.base.html) bundles a live stream with three kinds of facts. `StInv` describes valid private-state fields, array extents and pointer layout. `Uniq` says an allocation identity has only one object representation. `Fresh` protects unused identities for future allocation; the next section separates those two identity rules in detail. Its window clauses describe the actual allocation, capacity, valid byte count and ring indices. Its table-pointer clauses distinguish the embedded codes from static fixed tables. Its fixed array extents matter: a Lean array value alone does not enforce the corresponding C declaration's length.

[`Zlib.Deflate.Spec.DGood`](/reference/source/ZlibF/Proof/deflate.c.base.html) similarly includes a live compressor, storage/size constraints, uniqueness, freshness and a tree invariant. Non-NULL allocator fields in a live-state check are not the separate `DefAlloc` assertion that the represented allocator/free callbacks are the supported default functions.

These are concrete representation predicates, not a complete account of algorithmic history. Shape facts do not alone identify a window's logical bytes or establish that a table entry implements the canonical code. The relations used for refinement must connect those meanings to the same returned heap.

Now ask how A reached the checkpoint: successful Init, calls that accepted input and delivered `ABAB`, then perhaps a legal caller buffer replacement. A proof that starts only with a hand-built “good checkpoint” does not show that this application's history establishes it. Induction must start with actual initialization and cover each allowed transition, including failure returns that leave the stream live.

[`StreamReachable`](/reference/source/ZlibF/Spec/Public/History.html) records actual successful initialization, actual returning operations, permitted caller rebuffering and successful copies. A recorded execution equation is evidence that the call happened; it does not grant its specification for free. `StreamSequenceSafety` requires the invariant as a conclusion about every admitted history, and requires the next admitted call to return. It must do more than preserve an invariant conditionally when a caller assumes one.

## Distinguish new objects from existing ones {#identity}

When Copy succeeds, ending A must leave the copied decoder's new state/window alive. To express this, the proof model gives each allocation an identity. The identity is what distinguishes two equally sized windows and lets a free remove one without removing the other.

The heap stores different object kinds in typed tables. A byte block and a state record cannot silently share one allocation identity. `Uniq` states that at most one of those tables contains an object at each block number.

[`C.Fresh`](/reference/source/ZlibF/Runtime/Schema.html) uses `nextBlk` as the first not-yet-issued allocation identity and states that every identity from there onward is unused. This is an object counter, not a memory address or a byte count. An allocating proof must preserve that condition as the counter advances. `Fresh` and `Uniq` have different jobs: the first protects future allocation, the second protects the interpretation of existing identities. Neither alone says that two specific stream-owned buffers are suitably separated; the corresponding representation clauses must establish that too.

Freshness does not initialize an object. In the failed compressor attempt, cleanup reads buffer-pointer fields, so it must be justified that every such field was written before cleanup reads it. In successful compression, a bounded predecessor index still needs evidence that the chain position is meaningful.

Arbitrary fresh integer contents also remain in scope. Allocated capacity is not evidence that a predecessor or pointer field was written. The [safety reference](/reference/docs/spec/safety.html) explains the model's fixed integer garbage and fresh-NULL pointer convention. Establishment needs write-before-read evidence where the runtime cannot detect an omitted pointer write.

## Account for every live block and permitted write {#ledger}

Return to the failed third allocation. Before Init, the caller may already own other live objects unrelated to this stream. After cleanup those old objects must remain, while state, window, head and pending from this attempt must be gone. Meanwhile, the stream's error message or default allocator fields may have changed, and the allocator has observed the attempts. Thus “nothing remains allocated by this attempt” is useful; “the whole heap is unchanged” is too strong.

[`Frame`](/reference/source/ZlibF/Spec/Public/Initialisation.html) protects existing allocations outside an explicit changed set. It also preserves statics, allocation-oracle and garbage functions, while allowing the fresh-identity and allocation-attempt counters to advance. It is not whole-heap equality.

To write the exact ledger, fix an allocation identity `b`. `before` and `after` are heaps before and after the call; `live` records whether that identity is allocated. `removed` and `created` are sets, written as predicates on identities. The symbols `∧`, `∨`, `¬` and `↔` mean “and,” “or,” “not” and “if and only if.” The separate `LiveChange` definition states:

```text
after.live b ↔ (before.live b ∧ ¬ removed b) ∨ created b
```

Read this for one allocation identity `b`: it is live afterward exactly when it was live and not removed, or belongs to the operation's newly live set. For the failed attempt, the newly live set is empty on return and no pre-existing live block is removed. The temporary successes are accounted for by actual frees before returning. For a successful Copy, the new destination blocks are added while A's blocks remain.

For successful init, `created` names the new owned blocks. For failed init, no new live block remains and no old live block is removed. For End, the removed set is precisely the old stream-owned set. The failed five-request trace must account for later successful allocations even after an earlier buffer request failed.

For comparison, `inflate` may write `ABAB` into four permitted output bytes before history-window allocation fails. Its object stays live, but those four bytes have changed. An ownership ledger alone cannot say whether a fifth byte was overwritten.

Caller output needs finer boundaries than an object-wide frame. [`BufferFrame`](/reference/source/ZlibF/Spec/Public/History.html) preserves byte-array sizes and bytes outside the union of authorized regions. It allows the delivered prefix or registered header destinations to change without granting arbitrary modification of the rest of their allocations.

## Prove reuse, independent copies and release {#operations}

A useful Reset theorem must permit the reused memory while ruling out a stale-history match. In the `ABAB` example, unchanged physical bytes do not contradict an empty logical history: the valid-history count becomes zero. Conversely, simply retaining a live window says nothing about which history is authorized.

For Reset, unchanged allocation identities and changed logical history must coexist. [`inflateResetPre` and `DeflateResetContract`](/reference/source/ZlibF/Spec/Public/Lifecycle.html) state which counters, pointers and history fields change. An incompatible decoder window can disappear from the owned set; ordinary compressor reset retains its allocations and clears the dictionary hash. A conditional reset theorem requiring `DGood` cannot establish `DGood` for a new allocation: initialization must first construct the required state and tree facts.

For Copy, compare two possible mistakes. Copying bytes without fixing internal table pointers breaks private ownership. Allocating independent buffers but forgetting the held bits or unfinished match breaks continuation. The postcondition needs both independence and equal saved progress on the same returned heap.

[`relocateCode`, `copiedDeflate` and the copy targets](/reference/source/ZlibF/Spec/Public/Copy.html) describe equal progress with independent storage. Static code pointers can remain shared; references into copied embedded arrays move to the new identity. Pending cursors and tree descriptors require corresponding relocation. The source stream/state is preserved, and failure leaves no newly owned destination blocks. A correct byte copy alone would miss these pointer and ownership obligations.

The End excerpt uses `TRY_FREE(stream, pointer)` to free a non-NULL private buffer and skip a NULL one. `ZFREE` releases the state record itself. `status` remembers the compressor stage before release; `BUSY_STATE` identifies ordinary compression still in progress, which explains the final error-code choice without keeping the released state alive.

End closes the same ledger. The [actual compressor End tail](https://github.com/madler/zlib/blob/757f0527154291bcf6bfbd6396ecde6bedd2db95/deflate.c#L1320-L1328) is useful evidence of the order:

```c
TRY_FREE(strm, strm->state->pending_buf);
TRY_FREE(strm, strm->state->head);
TRY_FREE(strm, strm->state->prev);
TRY_FREE(strm, strm->state->window);

ZFREE(strm, strm->state);
strm->state = Z_NULL;

return status == BUSY_STATE ? Z_DATA_ERROR : Z_OK;
```

These are selected verbatim lines, not a teaching implementation. In the allocation-failure example, `TRY_FREE` skips the NULL predecessor and frees the later successes too. For a valid busy compressor, release still occurs before `Z_DATA_ERROR`. Proving End means deriving the exact removed set and preserved caller objects from this execution, including the result code. It must not equate a non-`Z_OK` result with unchanged ownership.

The [fixed-snapshot ledger definitions](https://github.com/cla7aye15I4nd/zlib-f/blob/e8232b1bfb90938be902ef226c7dc7436a2f07c0/ZlibF/Spec/Public/Initialisation.lean#L9-L21) separate the `Frame` and `LiveChange` obligations explicitly. They are specification definitions; their presence does not discharge any execution theorem.

## Diagnose a failed argument without changing the domain {#scope}

If one of these arguments gets stuck, first identify the failing claim. Did a proof technique fail to show a true bound, did the representation admit an impossible state, did the translation differ from C, or does a permitted real C execution have a defect? Those diagnoses demand different changes. An unsafe state manufactured from an overly broad invariant is not by itself a reachable application failure.

The [method record](/reference/docs/proof/method.html#one-representation-invariant) describes an earlier invariant admitting a gzip EXTRA phase with a NULL header. That conditional execution exposed a missing state relationship. It did not establish that permitted public histories could reach it, and did not justify excluding a legal caller input.

The [contract review](/reference/docs/checking/contract-review.html#counterexamples-to-the-old-statements) also records an old table query admitting `2^63` slots instead of the actual embedded extent. A counterexample to that representation question required a reviewed statement correction, not a disguised proof shortcut. Distinguish a proof-technique failure, wrong specification, translation mismatch and actual C defect before changing any premise.

The broader composition of history, pointer initialization and functional meaning remains **to confirm** through the corresponding execution proofs. Advanced operations retain their per-entry effects and sequence-safety obligations; ordinary format epochs do not automatically refine every combination of dictionary replacement, priming and recovery. Definitions and local results named here locate evidence, not full acceptance. The [complete method](/reference/docs/proof/method.html), [stream composition](/reference/docs/proof/stream-composition.html) and [current progress](/reference/docs/progress.html) retain the exact obligations, scopes and named-commit acceptance evidence.
