A decoder has delivered four bytes, but the application still needs the rest of the message. To continue safely, it must preserve more than the text already received: it must know which instruction is unfinished and which storage that instruction can still read. To start a different message or save two possible continuations, it must deliberately change that relationship.

Zlib separates the application's **task record** from the codec's **private working storage**. The task record, `z_stream`, records which readable input and writable output regions the codec may use now; these associations are its buffer bindings. Behind it, a private state object keeps decoding progress and may own a history window, a bounded buffer of already-produced bytes available to later copy instructions. The input, output and optional header objects belong to the application; the codec borrows their usable ranges. This distinction determines what can be replaced, copied or freed.

There are three difficulties. Delivered bytes and unfinished work advance at different times. Copying a private state does not automatically give the application two output buffers. An allocation error can occur after bytes have already been written. A useful protocol must describe the actual state after each operation, including these partial effects.

Use one checkpoint to make those requirements concrete. The selected raw stream `73 74 82 40 00` represents `ABABABAB`. With four output positions, a decoding call delivers `ABAB` and leaves a match that can produce the remaining `ABAB`. Continuing completes the same task; Reset starts from a new complete encoding; Copy saves the same position for two independent continuations. In the diagram, application-owned bytes stay separate from codec-owned state and window objects.

<div class="zl-demo-mount"><zlib-demo kind="checkpoint"><p>At the checkpoint the application has ABAB, and the decoder has four match bytes left. Continue by binding a new output region. Reset discards the unfinished instruction and needs a fresh complete stream. Copy duplicates private state and history, but caller output pointers still alias until separate destinations are bound. Ending one copy must leave the other able to continue.</p></zlib-demo></div>

## Establish the task and its configuration {#init}

Before any bytes can be processed, the codec needs a place to save progress and, where required, space for its window, indexes or pending output. Initialization obtains that private storage and attaches it to the application's task record. It consumes no message input and produces no encoded or decoded bytes. The [initialization result in Lean](/reference/source/ZlibF/Spec/Public/Initialisation.html) records the resulting state fields and exact new allocation set: five private objects for the selected compressor layout, one initial state object for the ordinary decoder. This is the starting state from which later calls are justified.

Storage is obtained and released through allocator callbacks: functions chosen by the library or application. A zero-initialized task record selects the ordinary build's default pair. A custom pair must remain compatible, and its associated application context, called `opaque`, must remain valid while the stream can use it. These functions govern storage lifetime; changing an input slice does not replace the allocator.

The application also chooses a format, a history capacity and a compression policy. `method` selects DEFLATE here. `windowBits` encodes the wrapper request and window scale. `memLevel` selects search-index and symbol-storage capacities; level and strategy choose the work performed with those objects. These choices are made at initialization or through their specific later controls, rather than passed anew with every data chunk.

These controls act at different moments:

| Moment | Controls | What changes |
| --- | --- | --- |
| Initialize a compressor | `method`, `windowBits`, `memLevel`, level, strategy, allocator | Accepted format, window/index/symbol capacities, search policy and resource behavior. |
| Initialize a decoder | `windowBits`, allocator | Admitted wrappers, requested history-window limit and resource behavior. The decoder does not receive the encoder's compression level. |
| Continue an existing task | Input/output slices and a boundary request | Which bytes are available now and which completion or stopping boundary is requested. |
| Deliberately change a live task | Search-policy changes, dictionaries, primed bits, header registration, Reset or Copy | A particular policy, context or continuation; each operation has its own timing and storage requirements. |

For the ordinary build, compressor level `Z_DEFAULT_COMPRESSION` becomes 6. `memLevel` determines hash/symbol capacities; level and strategy select search policy and budgets. Capacity can still change candidate distributions and block boundaries. A zlib compressor request of eight window bits becomes nine; raw and gzip reject that eight-bit case. Decoder admission is different: it has its own accepted signed requests and header-derived settings. A compressor configuration and a decoder admission request should therefore be compared by format and effective window, not by integer equality.

These are runtime controls within a selected build. Compile-time choices also matter. `FASTEST` changes nonzero compression levels to 1; `Z_SOLO` does not supply the ordinary default allocator; `MAXSEG_64K` makes compressor Copy return `Z_STREAM_ERROR`. The examples here use the ordinary default layout and allocator. The matching and decoding chapters explain how the corresponding normalized settings enter their loops.

A useful initialization invariant says exactly which objects were obtained, which fields were written, and which bytes are meaningful. Allocating a window creates capacity. It does not turn every byte of that allocation into valid match history. Similarly, non-NULL allocator pointers alone do not establish that they are the modeled default functions.

## Separate input acceptance from output delivery {#buffers}

Each call borrows two regions from the application: readable input and writable output. Each region needs a current address and an available byte count. The task record names the input pair `next_in` and `avail_in`, and the output pair `next_out` and `avail_out`. Save the two availability counts before processing. After a normal returning call, their differences locate the actual consumed and written prefixes:

```text
input_taken    = old_avail_in  - new_avail_in
output_written = old_avail_out - new_avail_out
```

For compression, input taken into the window can still be uncommitted lookahead. Committed literals and matches can still await a block decision. Encoded bits can still be held in the bit register, and complete bytes can still wait in pending storage. Only bytes copied into the caller's destination contribute to this call's delivered output. Thus an empty input slice does not mean its compressed result has already reached the application.

The compressor's completed bytes wait in an internal delivery queue. Its cursor `pending_out` names the next undelivered byte, and `pending` counts those still waiting. The caller's `total_out` counts bytes already delivered over the task. Here `strm` points to the application’s stream record and `s` to its private compressor state. In the actual [pending-output copy](https://github.com/madler/zlib/blob/757f0527154291bcf6bfbd6396ecde6bedd2db95/deflate.c#L969-L986), `len` is bounded by both waiting data and this call's output room:

```c
zmemcpy(strm->next_out, s->pending_out, len);
strm->next_out  += len;
s->pending_out  += len;
strm->total_out += len;
strm->avail_out -= len;
s->pending      -= len;
```

The caller cursor and pending cursor advance together. Replacing the output buffer must preserve the private compressor and its remaining pending suffix. The application processes the written prefix before reusing that storage. It also retains the unread input suffix until the codec has taken it.

For decompression, a byte taken from the compressed input may still have unused bits in the accumulator. At this checkpoint four of the five compressed bytes have been taken, with one of their bits still held in state and one compressed byte still unread. The output prefix is already uncompressed data. At the `ABAB` checkpoint, replacing the four-byte destination continues the saved match; resetting would discard it. The application can bind another destination without changing the task.

Error returns retain effects in source order. In particular, `inflate` first publishes its updated buffer pointers and can then fail to allocate a history window. New output can be present even though its normal final total-counter updates were skipped. The returned slice and the counters therefore need separate relations. The caller's output buffers remain caller objects throughout.

## Request a boundary with flush {#flush}

While handling one message, an application can want several different boundaries: accumulate more input, make the current prefix available to a receiver, stop at a block, or finish the message. The current call carries that request in its `flush` argument. It does not free private storage. Compression chooses boundaries to write; decoding observes boundaries in the supplied encoding.

For the compressor, `Z_NO_FLUSH` permits accumulation for better block decisions. `Z_BLOCK` completes a block without requiring byte alignment; up to seven bits can remain held. `Z_PARTIAL_FLUSH` appends an empty fixed-code block without the byte-alignment promise of a sync flush. `Z_SYNC_FLUSH` emits an aligned marker so a receiver can obtain all input supplied so far. `Z_FULL_FLUSH` adds the same kind of boundary and discards the compressor's preceding match history. Neither sync nor full flush declares the message finished.

`Z_FINISH` declares that no more source bytes will be added. Keep the unread part of the already supplied slice and continue with `Z_FINISH` and more output room until `Z_STREAM_END`. The returned end code means the final block and wrapper trailer have been delivered. End then releases resources. If a nonfinal flush fills the destination, continue that same flush request with more room until it is complete; repeatedly requesting another marker is a different operation.

The decoder reads boundaries chosen by the encoded stream. Its `Z_SYNC_FLUSH` does not insert a marker or discard history. `Z_BLOCK` can stop at a wrapper-header or block boundary. `Z_TREES` additionally stops after a block description, before its payload. For applications recording such boundaries, the returned `data_type` field reports unused input bits and flags for the final block, an end/header boundary or a completed block description. This locates a stopping point in bits; it does not declare the message complete. With `Z_FINISH`, failure to finish in this call turns an otherwise ordinary `Z_OK` result into `Z_BUF_ERROR`. The saved task can still be continued with additional input or output space.

```mermaid
flowchart TD
    A["Live task and current slices"] --> B["Process with the selected request"]
    B -->|"room or input needed"| C["Return written prefix and saved work"]
    C -->|"replace slices, preserve state"| A
    B -->|"requested intermediate boundary"| D["Return at that boundary"]
    D -->|"more of the same message"| A
    B -->|"complete encoded stream"| E["Z_STREAM_END"]
    E --> F["Reset for another task or End"]
```

Changing compression policy can itself cross a boundary. `deflateParams` checks the new level and strategy and, when necessary, calls `deflate` with `Z_BLOCK` under the old settings. If the old block cannot be completed, it returns `Z_BUF_ERROR` with the old policy still selected. Input consumption and output already produced remain observable. More output room and a retry are needed; the failed policy change is not a rollback of compression work.

`deflateTune` is a lower-level control. It stores its four integer arguments, converting three to unsigned fields; it does not validate a sensible search budget. If a later search argument uses positive budget bounds, those bounds must be stated and established. A changed level through Params, or ordinary compressor Reset, restores that level's standard tuning.

## Supply a dictionary, bits or header context {#dictionary}

A dictionary makes agreed bytes available as match sources before those bytes would otherwise have appeared in this task. It is not output to be delivered again. Suppose messages share the vocabulary `AB`. The compressor can reference it only when the receiver will provide corresponding history.

For zlib compression, install the dictionary before compression starts. The dictionary identifier records the checksum of the supplied dictionary, while the usable window retains an appropriate suffix. Gzip compression has no preset-dictionary path. Raw compression admits dictionary installation at suitable block boundaries, with no pending lookahead. To test that timing, the source uses `wrap` for the wrapper (0 raw, 1 zlib, 2 gzip), `status` for the compression phase and `lookahead` for accepted bytes not yet assigned a representation. `strstart` is the current input position; `block_start` marks the current block’s original-byte start. With no lookahead, equal positions mean there are no original bytes accumulated in that block. The [installation guard](https://github.com/madler/zlib/blob/757f0527154291bcf6bfbd6396ecde6bedd2db95/deflate.c#L558-L573) rejects the other timings:

```c
if (wrap == 2 || (wrap == 1 && s->status != INIT_STATE) || s->lookahead ||
    (wrap == 0 && (long)s->strstart != s->block_start))
    return Z_STREAM_ERROR;
```

Dictionary loading temporarily binds the dictionary as compressor input, populates the window and hash, then restores the caller's input binding. It can increase `total_in` without sending the dictionary as message output. In a history containing dictionary installation, `total_in` therefore cannot simply be read as message-payload length. Pointer movement, accepted dictionary context and message-byte meaning need separate accounts.

A zlib decoder requests the dictionary with `Z_NEED_DICT`. Installation checks the supplied identifier; a wrong dictionary gives `Z_DATA_ERROR` and permits another attempt. Raw decoding can install dictionary history at call boundaries without an identifier check. Installation copies the bytes into private history, leaves the caller's input/output pointers and totals unchanged, and can fail while allocating the window. A non-NULL zero-length raw dictionary is a distinct case from a NULL dictionary pointer, which the source rejects.

Priming supplies bits already handled by an enclosing format. `inflatePrime` appends 1–16 low bits above held input bits when the combined count fits 32; zero is a no-op, and a negative count clears the held bits. `deflatePrime` appends 0–16 low bits to pending output. It can compact existing pending bytes before discovering insufficient space. Invalid count requests return different codes in the two APIs: decoder priming uses `Z_STREAM_ERROR`, compressor priming uses `Z_BUF_ERROR`. In ordinary raw-stream use, supply the prefix at the documented start point; inserting arbitrary bits does not by itself establish a valid DEFLATE message.

Gzip metadata is borrowed storage. `deflateSetHeader` retains a header and its optional extra/name/comment inputs for emission and queries that inspect it. Finishing the header does not unregister those pointers. `inflateGetHeader` registers a writable header record and bounded capture destinations before parsing. Short destinations capture only what fits; a string terminator appears only when it fits. Reset clears registration without freeing these caller objects. Copies can retain the same borrowed pointers, so ending one private codec does not end the caller's metadata lifetime.

## Reuse capacity with Reset {#reset}

Return to decoder A after `ABAB`. To decode independent message B, ordinary `inflateReset` discards A's bit progress and valid history, then the caller binds B's slices. It does not erase the `ABAB` already delivered to the application, or reposition an external file.

Reset must invalidate old match sources without unnecessarily releasing their capacity. Three private fields make that distinction explicit. `wsize` is the active ring size, `whave` is the number of valid history bytes and `wnext` is the next write position. The requested wrapper is saved as `reqwrap`, while `wrap` describes the current one; recovery can change the current setting. In this excerpt, `state` points to the private decoder object. The [reset tail](https://github.com/madler/zlib/blob/757f0527154291bcf6bfbd6396ecde6bedd2db95/inflate.c#L125-L141) restores the request and invalidates history:

```c
state->wrap = state->reqwrap;
state->wsize = 0;
state->whave = 0;
state->wnext = 0;
return inflateResetKeep(strm);
```

The old allocation may remain, but zero valid bytes means B cannot use its old contents as match sources. The called ResetKeep clears held bits and restarts parsing. Neither reset replaces the input/output bindings for the caller. In particular, the old input pointer may be in the middle of a block. After discarding held bits and the unfinished instruction, a new task needs a complete new encoding; rebinding the old compressed suffix is not continuation. ResetKeep also restarts parsing and clears bit progress: retaining window bytes does not retain the middle of the old instruction. The [reset postconditions](/reference/source/ZlibF/Spec/Public/Lifecycle.html) express this by resetting the mode and held bits separately from window contents and caller bindings.

| Operation | Logical contents | Capacity and configuration |
| --- | --- | --- |
| `inflateResetKeep` | Restarts progress while retaining usable window history. | Keeps current wrapper/window state and allocated storage. |
| `inflateReset` | Discards logical history and saved bit progress. | Restores requested wrapper/window, frees an incompatible window, preserves the validation choice. |
| `inflateReset2` | Discards progress and selects another accepted request. | Replaces wrapper/window request and validation setting; frees incompatible storage. |
| `deflateResetKeep` | Discards pending output and undecided lookahead, while retaining window/hash history and tuning. | Keeps compressor allocations and selected configuration. |
| `deflateReset` | Starts with empty match history and default tuning for the current level. | Keeps allocations, wrapper, window, memory level, level and strategy. |

The Keep entries are undocumented public symbols and need deliberate protocol design. Retained compressor history can produce a new reference to bytes from before the reset. A receiver starting with empty history would not have those bytes. Physical storage reuse and independent-message semantics must therefore be distinguished explicitly.

Decoder Reset restores the validation choice last selected by `inflateValidate`, since that operation updates the requested as well as current setting. Reset2 establishes the validation setting of its new request. ResetKeep retains the current wrapper, including wrapper changes made by synchronization recovery. These differences affect later validation and accepted input, not just memory consumption.

## Resume at a synchronization marker {#recovery}

Reset starts another task. Recovery instead tries to keep a later decodable part of the current input after damage. `inflateSync` searches for the four bytes `00 00 ff ff`, the marker ending an empty stored block. It first searches whole bytes retained in the bit accumulator, then consumes the current input slice. A partial marker match remains in the state so another call can continue the search. No complete marker gives `Z_DATA_ERROR`; no searchable bytes gives `Z_BUF_ERROR`.

Finding the marker restarts parsing at a block boundary, clears decoding history and held progress, and preserves the accumulated input/output totals. If no wrapper header was read, recovery selects raw decoding; otherwise it disables checksum validation for the remainder. It does not reconstruct the lost bytes. The full-flush protocol is useful here because the compressor discards preceding match history at that boundary. A sync-flush marker alone does not stop later matches from referring to earlier data; an incidental marker pattern is not enough to establish a correct recovered suffix.

## Copy a checkpoint with independent private storage {#copy}

At A's four-byte checkpoint, successful Copy lets A and its copy each continue with the remaining `ABAB`. The prefix already delivered remains the application's responsibility. Before running both continuations, the application supplies appropriate output destinations; copied caller pointers do not create two separate caller buffers.

A bytewise state-record copy is insufficient. The dynamic literal/length table begins at the source's embedded `codes` array; its distance table follows within that array. A copied pointer would still name A's storage, so ending A would invalidate it. The literal/length pointer is named `lencode`, the distance pointer `distcode`, and the construction cursor `next`. The selected source’s [registered equality patch](https://github.com/cla7aye15I4nd/zlib-f/blob/main/patches/0001-inflate-copy-pointer-equality.patch) recognizes the embedded-array base without comparing the order of pointers into different objects. Here `state` names the source private object and `copy` the new destination object. The code keeps the distance-table offset while changing its owner:

```c
if (state->lencode == state->codes) {
    copy->lencode = copy->codes;
    copy->distcode = copy->codes + (state->distcode - state->codes);
}
copy->next = copy->codes + (state->next - state->codes);
```

The equality also covers the canonical table pointers installed by reset. When decoding uses shared static fixed tables, those pointers keep their shared lifetime. The construction cursor `next` is always relocated. Decoder Copy obtains a new state and, if the source has a window, a separate window. Compressor Copy obtains its own state/window/predecessor/head/pending allocations and repairs pending cursors and embedded tree descriptors. It copies initialized content, including the saved input/encoding progress.

Use a distinct writable destination that owns no live codec. A failed copy releases newly obtained destination objects and clears destination state, while retaining the source checkpoint. Successful copies require separate End calls. Caller I/O and borrowed metadata remain caller responsibilities. These conditions explain both independence and continuation: correct private pointers without the saved match would lose the task; identical saved fields with pointers into A would lose independence.

The proof tracks where these fields came from as well as whether they lie within bounds. The [table-origin relation](/reference/source/ZlibF/Proof/inflate.c.default-origin-state.html), named `DefaultOriginState`, records that the literal pointer is at `codes` or that both decoding pointers name the paired fixed tables, together with the default header-state alternatives. Initialization establishes these facts. Actual decoding, reset, dictionary and control operations preserve them. For a successful Copy, the [successful-copy argument](/reference/source/ZlibF/Proof/inflate.c.copy-both-origin.html), `inflateCopy_actual_success_both_origin`, derives the required allocation successes from the returned `Z_OK`, then establishes the state relation for both source and destination. The caller does not have to assume an internal table-origin contract.

## Account for allocation and release in source order {#allocation}

Successful compressor initialization obtains five allocations: state, window, predecessors, hash heads and pending/symbol storage. The tree arrays are embedded in the state; symbols share pending storage in the selected packed layout. An ordinary decoder initially obtains only its state. Its private window can be allocated later when history must survive a return or a dictionary is installed.

Failure handling follows the actual request schedule. After compressor state succeeds, the source attempts all four buffers before the combined NULL test. If the predecessor request fails, later head and pending requests can still succeed. Cleanup must release all four successful objects, including the successes after that failure.

```mermaid
flowchart LR
    A["State succeeds"] --> B["Window succeeds"]
    B --> C["Predecessors fail"]
    C --> D["Heads succeed"]
    D --> E["Pending succeeds"]
    E --> F["Combined test"]
    F --> G["Release four successful objects"]
```

The failure branch sets a cleanup-compatible state and invokes End. If the first state allocation fails, buffer requests do not occur. The allocation model records a separate outcome for each attempt, so one failed request cannot justify assuming that all later requests fail. Cleanup removes live objects but does not rewind allocation-attempt or fresh-identity counters. The decoder has another ordering: it allocates state before validating the window request. A request with invalid window bits can therefore encounter allocation failure first; a successful state allocation followed by parameter rejection releases that state.

The delayed decoder window is an optimization with a visible error path. A call can first write `ABAB`, publish its buffer pointers, then fail to obtain the window needed for the next call. The written prefix remains. A one-call finish that does not need retained history can avoid that window allocation and copying work entirely.

End closes the private allocation lifetime. The [compressor End tail](https://github.com/madler/zlib/blob/757f0527154291bcf6bfbd6396ecde6bedd2db95/deflate.c#L1312-L1328) first releases buffers and state, then chooses its result:

```c
TRY_FREE(strm, strm->state->pending_buf);
TRY_FREE(strm, strm->state->head);
TRY_FREE(strm, strm->state->prev);
TRY_FREE(strm, strm->state->window);

ZFREE(strm, strm->state);
strm->state = Z_NULL;

return status == BUSY_STATE ? Z_DATA_ERROR : Z_OK;
```

`TRY_FREE` skips NULL buffers. `status` was saved before release. A busy abandoned compressor can thus return `Z_DATA_ERROR` after releasing its private storage. `inflateEnd` releases its optional private window and state and returns `Z_OK` for a valid live decoder even when the message was abandoned. Neither operation completes pending message output. The original input/output objects and borrowed header objects stay with the application.

## Let an interface own the driving loop {#callbacks}

Whole-buffer utilities are suitable when the original input and destination capacity are already known. They create a temporary stream, run it and end it before returning. Their wide lengths can exceed the width of `avail_in` and `avail_out`, so the internal loop supplies representable chunks and separately tracks the wider remainder. The returned output length describes the written prefix; the input-counting decompressor can also report where trailing data begins. There is no live temporary codec left for the caller to resume.

An application can also let the library own the decoding loop, supplying functions for the library to call when it needs input or has output to deliver. Such application functions are callbacks. The raw decoder `inflateBack` uses this arrangement with an input callback, an output callback and a caller-provided window serving as history and output-delivery storage. `inflateBackInit` accepts window-bit arguments 8 through 15; the caller supplies the corresponding `2^windowBits` writable bytes. Its decoder loop lives in `infback.c`; it does not repeatedly call ordinary `inflate`. An input callback supplies the next readable chunk when requested. An output callback receives a full window or final prefix and reports whether it accepted that event. Already accepted output events are not rolled back by a later callback failure.

The input chunk must remain readable until consumed. An output callback cannot modify that active input or the decoder's window. Callback-owned state can change only within the stated preservation rules. Initialization allocates the callback decoder's state but borrows its window; `inflateBackEnd` frees that state and leaves the window for its caller.

Termination also needs a finite input supply or another explicit progress condition. Let `mu` count bytes the input callback can still provide. Supplying `n` bytes reduces that reserve by at least `n`. The [finite-input relation and bit budget](/reference/source/ZlibF/Proof/infback.c.macros.html), `InFinite` and `phi`, make the supply condition explicit:

```text
held bits + 8 × current-chunk bytes + 8 × future-input bytes
```

The future-input reserve depends only on the input callback's own byte blocks. The output callback preserves those blocks, so it cannot replenish spent input budget. Loading a byte merely moves budget into the bit accumulator. Consuming a field spends bits. Mode transitions also need a decreasing rank, bounded by the loop execution allowance in the model. Every callback returning promptly is not enough if it can keep supplying nonfinal blocks forever. The [callback preservation relation](/reference/source/ZlibF/Proof/infback.c.callbacks.html), `CbContract`, additionally gives callbacks selected writable byte blocks and excludes callback allocation/free; those are its precise premises. The broader public callback protocol needs its own permitted effects stated explicitly.

## Keep file position and decoded position distinct {#gzip}

File access needs one more persistent object: a handle that retains file position, buffers and an internal codec across operations. The gzip file interface calls this handle `gzFile`. `gzread` can read compressed bytes ahead of the uncompressed prefix requested by the application. Consequently, descriptor position, buffered compressed input and delivered uncompressed position are different quantities.

For example, after delivering `ABC`, a request to seek forward from logical position 3 to 5 can consume buffered `DE`; if those bytes are not buffered, the handle records work to skip by reading and decoding. Seeking backward can require rewinding and decoding again. A compressed byte offset alone does not identify a resumable decompressor state.

Gzip reading also handles member concatenation and the transparent-input case. An ordinary `inflate` call finishes one encoded stream; a file reader can arrange another member afterward. `gzclose` releases the handle's buffers, codec state and file resource under its contract. The application still owns the destination passed to `gzread`.

The proof's external world matters here. The [implemented file world](/reference/source/ZlibF/Zlib/gzfs.html), named `Fs`, represents regular files and descriptor positions beside the heap, the model’s inventory of memory objects and their contents. Reads reach represented EOF/errors, and writes include a file-size-limit path. Pipes, concurrent descriptor changes and arbitrary short-read/error schedules need additional external assumptions or models. Formatted gzip writing also translates a variable C argument list into bytes; its represented argument list has separate premises from the machine ABI that passes those arguments. Therefore a file proof states both its heap preservation and its file-world premises. This is a concrete model boundary, independent of the code's input/output accounting.

## Derive state validity and the resource ledger {#correctness}

The checkpoint now supplies a precise proof problem. Continuing A preserves the remaining `ABAB`; Reset makes old bytes unavailable to a new message; Copy preserves the saved task in newly owned private objects; End removes precisely those private objects. The proof uses the same heap returned by each actual operation.

The initialization domain supplies a writable stream record with no live codec attached, valid argument storage, represented library globals, fresh allocation identities and compatible allocator fields. Successful initialization establishes the live codec invariant and allocation set. Failure gives the cleanup relation for objects acquired by that attempt. It must not require the post-initialization invariant as an unexplained premise of Init.

The example requires two separate promises. Other caller objects must retain their contents, and each private allocation must either remain live or be accounted for when created or released. The [frame and allocation-ledger definitions](/reference/source/ZlibF/Spec/Public/Initialisation.html) name these promises `Frame` and `LiveChange`. The latter states:

```lean
def LiveChange (before after : Heap) (created removed : Nat → Prop) : Prop :=
  ∀ b, after.live b ↔ (before.live b ∧ ¬ removed b) ∨ created b
```

Here `b` identifies an allocation, not a byte offset. For successful compressor Init, the created set contains its five distinct objects and the removed set is empty. For failed Init, no newly acquired object remains live. For End, the created set is empty and the removed set is exactly the stream's owned objects. For Copy, new destination objects appear while source objects retain their contents and lifetime.

Borrowed buffers and headers are not promoted to codec-owned objects. Their readable/writable ranges and separation conditions are supplied at the calls that use them. A legal buffer replacement preserves private state; the next call's argument relation supplies valid new slices and any active metadata destinations. The `ActiveHeader` relation keeps the registered header record and its ranges valid while those pointers remain registered.

To compose calls, first derive the private-state relation from the operations the application actually performed. The [decoder sequence construction](/reference/source/ZlibF/Proof/inflate.c.origin-history.html), `DefaultOriginHistory`, starts with successful default initialization. Each later step records its actual arguments, buffer replacement and returning execution. Induction then derives live storage, table origins and the default allocator for the returned state. The construction does not ask the application to assert the internal invariant after each call. A dictionary query can write its requested caller destination even though it does not change private decoding progress.

That construction has a concrete platform and configuration domain: default zlib initialization with a fifteen-bit window, stream-size argument 112 (the selected model’s stream-record size in bytes) and the modeled default allocator. Every represented byte object has fewer than `2^63` bytes, and rebuffering preserves that property; this is a bound on individual memory objects. The selected controls include dictionaries and queries; a later Reset2 again chooses fifteen bits. Successful Copy requires a distinct destination record. Sync steps supply an actual fault-free returning execution, so this induction preserves state across such recovery steps without asserting termination of an arbitrary marker search.

Next apply the [decoder's next-call theorem](/reference/source/ZlibF/Proof/inflate.c.origin-history-memory-contract.html), `DefaultOriginHistory.next_memory_contract`, to that derived state and the next valid borrowed slices. Its conclusion gives the actual returning execution, input consumed, output written, mode, preserved caller objects and new private allocations. For `Z_OK`, `Z_STREAM_END`, `Z_DATA_ERROR` and `Z_BUF_ERROR`, the theorem advances the totals by those slice lengths. On `Z_MEM_ERROR`, the totals keep their entry values even though the output slice can contain new bytes. On `Z_OK`, some input was consumed or some output was written, and the request was not `Z_FINISH`. These are different conclusions needed by a driving loop: memory safety permits the call, slice accounting locates its effects, and the progress clause prevents an unchanged successful iteration. Connecting the written bytes to the decoded message uses the bit, table and match relations from the preceding chapters.

The [default compressor sequence theorem](/reference/source/ZlibF/Proof/deflate.c.engine.compression-protocol-history.html), `default_init_compression_histories`, uses the same principle: start at actual initialization and preserve the execution boundary through an explicit call sequence. Its initialization premises are five successful allocations, fresh and unique heap objects, represented library globals, default-or-NULL allocator fields, the stated version-byte check and stream-size argument 112. Its sequence admits legal rebuffering, positive-output-room FINISH steps, and new-nonempty-input NO_FLUSH steps before finishing. These premises explain which driving loop the result justifies. The byte-to-record and record-to-bit relations supply the separate format argument at that boundary.

Finally, [the public End goals](/reference/source/ZlibF/Spec/Public/Lifecycle.html) require the corresponding live-state invariant, `Good` for decoding or `DGood` for compression, and specifically the default release function `zfree = zcfree`. Freshness belongs to those invariants. End then clears the state link, preserves caller objects and removes precisely the owned private set. This closes the allocation ledger for that allocator domain; it does not assume an arbitrary custom release callback has the same effects.

## Compose local relations into a complete call {#composition}

The preceding chapters provide different facts about the same execution. Matching identifies which original bytes a record represents. Encoding relates those records to emitted bits. Decode-table construction and lookup connect bits to instructions. Copying connects instructions to output bytes. State validity supplies the live storage and ranges that let each step run.

At a return boundary, those facts meet the actual consumed and written slices. Saved fields describe the work left for the next call. Header and trailer checks connect the chosen wrapper to that data. The resource ledger explains which private objects remain and what End removes.

```mermaid
flowchart TD
    Init["Execute initialization"] -->|"Success"| State["Valid state, configuration, owned storage and call arguments"]
    Init -->|"Failure"| NoState["Clean up this attempt's new private objects"]
    subgraph Compression["Compression"]
      Match["Input bytes agree with committed records"] --> Encode["Records agree with emitted bits"]
      Encode --> Packed["Pending and delivered bytes preserve those bits"]
    end
    subgraph Decoding["Decoding"]
      Read["Input bits agree with table instructions"] --> Copy["Instructions agree with recovered bytes"]
    end
    State --> Match
    State --> Read
    State --> Copy
    Packed --> Boundary["Returned slices, saved work and wrapper conditions"]
    Copy --> Boundary
    Boundary -->|"next legal call"| State
    Boundary --> End["End closes the exact resource ledger"]
```

The nodes name relations to connect; arrows pass a conclusion into the premises of the next argument. At each handoff, the heap, configuration, byte order and ownership refer to the same returned state. A successful completion branch yields its format and output conclusion. A pause retains the remaining-work relation; refusals and allocation failures retain their actual byte effects and resource ledger. The complete-call argument follows those actual control branches.
