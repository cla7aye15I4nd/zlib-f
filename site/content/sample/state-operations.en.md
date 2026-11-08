[Streaming calls](/sample/stream-state.html) continue the same task by replacing buffers. The application may next make a different decision: abandon this message for another, save a checkpoint for two continuations, or install an agreed dictionary for a task. These decisions can all retain memory without retaining the same logical progress.

Use raw stream `73 74 82 40 00` again, but change output capacity from five bytes to four. At the first return, decoder A has delivered `ABAB` from `ABABABAB`, with four match bytes still to produce. This four-byte checkpoint is used throughout the chapter. The application owns the delivered prefix; its next intention determines the API:

| Application request | Input to the operation | Result the application can use |
| --- | --- | --- |
| Decode independent message B | A live decoder and Reset | Fresh logical progress in reusable storage; then bind B's buffers |
| Save A's current position | A live decoder and a distinct empty destination for Copy | Two independently owned checkpoints, each able to continue A |
| Begin matching from agreed bytes `AB` | A dictionary and a permitted installation point | Available match sources; the dictionary is not delivered output |
| Handle an enclosing bit/header format | Supplied bits or caller-owned metadata storage | Exact bit insertion or metadata access, with additional borrowing requirements |

Rebuffering continues A, Reset abandons A, and Copy preserves A. None replays output already delivered. The examples develop ordinary call sequences before connecting them to C fields and full contracts. Valid storage, readable/writable ranges and sequential use remain required; a C pointer type does not establish lifetime.

## Reset progress for another message {#reset}

Suppose decoder A has delivered `ABAB`. The application keeps those bytes. To decode independent message B, it calls [inflateReset](/reference/functions/inflateReset.html), then supplies B's buffers. Reset forgets A's progress and makes its old history unavailable to matches. It does not erase delivered application bytes or move an external file position. Existing I/O pointers and available counts remain unchanged, so changing their bindings is still the caller's job.

The saved history has three numeric fields: `wsize` is the active ring size in bytes, `whave` is its valid byte count, and `wnext` is the next write index. Zeroing them invalidates logical history without requiring every old byte to be erased. `reqwrap` remembers the requested wrapper configuration; `wrap` is the current one, which recovery may have changed.

Why can Reset forget `ABAB` without erasing every byte in memory? In the actual [reset tail](https://github.com/madler/zlib/blob/757f0527154291bcf6bfbd6396ecde6bedd2db95/inflate.c#L137-L141), logical history is described by counts and indices:

```c
state->wrap = state->reqwrap;
state->wsize = 0;
state->whave = 0;
state->wnext = 0;
return inflateResetKeep(strm);
```

`whave = 0` says there are no usable history bytes. An old physical window may still exist, but B cannot justify a backward match from its old contents. The called ResetKeep clears the held-bit accumulator and restarts the decode phase. There are no writes to `next_in`, `next_out` or their available counts in these reset functions; the caller must bind B's buffers. This is a selected source excerpt, not a replacement implementation.

The three decoder resets differ precisely:

| Entry | Progress and history | Configuration and allocation |
| --- | --- | --- |
| [inflateResetKeep](/reference/functions/inflateResetKeep.html) | Clears totals, held bits, dictionary-set status and header registration; retains window history. | Retains current wrapper/window settings and allocations. It does not restore wrapper changes made by recovery. |
| [inflateReset](/reference/functions/inflateReset.html) | Performs the progress reset and empties logical history. | Restores the requested wrapper/window, retaining a compatible window or freeing an obsolete one. Preserves the validation choice. |
| [inflateReset2](/reference/functions/inflateReset2.html) | Abandons progress, history and header registration. | Selects a new accepted wrapper/window request and enables its validation; frees incompatible window storage. Invalid values return `Z_STREAM_ERROR` unchanged. |

All three return `Z_OK` for the accepted live-stream reset. A failed stream check returns `Z_STREAM_ERROR` without changes; a dangling arbitrary pointer is not covered by that clean refusal.

`inflateReset2` includes every signed window argument in its focused parameter domain. The argument encodes both the wrapper and a base-two size exponent: exponent 15 means `2^15 = 32768` history bytes. Requests -15, 15, 31 and 47 all use that exponent while selecting raw, zlib, gzip and automatic detection respectively; the [inflateInit2_ contract](/reference/functions/inflateInit2_.html) lists all accepted values, including special zero-size requests. Reset never allocates a replacement window itself.

For the compressor, pending output means complete compressed bytes not yet delivered. Lookahead means accepted input bytes not yet committed to literals or matches. Reset has to decide what happens to both forms of unfinished work as well as to searchable history.

[deflateReset](/reference/functions/deflateReset.html) retains the compressor's five allocations and current level, strategy, wrapper and memory settings. It discards pending output, unfinished lookahead, bit progress and match history; default tuning for the current level is restored. [deflateResetKeep](/reference/functions/deflateResetKeep.html), an undocumented entry like its decoder counterpart, retains window/hash history and tuning. Both restart wrapper output and forget a custom gzip header. Neither certifies that abandoned work was delivered. A later match after ResetKeep can refer before the reset, so empty-history decoding is not promised.

## Copy a checkpoint for two continuations {#copy}

At A’s four-byte-output `ABAB` checkpoint, a successful copy lets both decoders continue with the remaining `ABAB`. The already delivered prefix is still the application’s responsibility; Copy does not deliver it again. A checkpoint must retain buffered bits, tables, history and unfinished operations, together with recoverable unread input. A byte offset alone is insufficient. [inflateCopy](/reference/functions/inflateCopy.html) and [deflateCopy](/reference/functions/deflateCopy.html) require a distinct writable destination with no live owned state in the focused workflow; self-copy and overwriting a live destination do not receive that leak-free contract.

Why isn't copying the state record enough? Suppose A's dynamic literal table starts ten entries into its embedded table storage. A record copy initially leaves the new pointer aimed at A's entries. If A ends, that pointer would dangle; if either table changes, the supposedly independent checkpoint would change too.

Successful decoder copy owns a new state and, if present, its own window. Dynamic table pointers into the source's embedded `codes` must move to the copy at the same offsets; static fixed tables can remain shared. The construction cursor also needs relocation. Compressor copy duplicates its five allocations, preserves initialized window/hash/pending/symbol content, and retargets pending cursors and embedded tree descriptors. Distinguishing static from owned pointers requires a valid provenance argument, not just two readable pointer values.

The fields `lencode` and `distcode` point to the literal/length and distance decoding tables. Their containing array is `codes`. Pointer subtraction below counts table entries, not bytes. `state` names the source state and `copy` the newly allocated destination, so the expression preserves an entry offset while changing the owning array.

The [actual relocation code](https://github.com/madler/zlib/blob/757f0527154291bcf6bfbd6396ecde6bedd2db95/inflate.c#L1380-L1388) first copies the records, then repairs the table pointers. The following selected lines are verbatim; the surrounding range check is in the linked source:

```c
copy->lencode = copy->codes + (state->lencode - state->codes);
copy->distcode = copy->codes + (state->distcode - state->codes);
```

For the ten-entry example, subtracting the old array base gives ten, and adding that offset to the new base selects the corresponding new entry. `next`, the table-construction cursor, also moves. Static fixed tables can remain shared because they outlive both streams. The provenance/range argument is part of the proof obligation, including the C comparisons used to select this case.

Both copies preserve the source and require separate End calls. Caller input/output pointers and retained header pointers are copied too: arrange suitable output destinations before continuing both, and keep shared borrowed metadata alive. Allocation failure frees the attempt's new blocks and clears destination state without consuming the source checkpoint. The [allocation chapter](/sample/allocation.html) follows this ledger; the [ownership proof](/sample/ownership-proof.html) explains how exact preservation and reachable-history claims are connected.

## Start with an agreed dictionary {#dictionary}

Suppose many messages begin with the same protocol vocabulary. Sending that vocabulary inside every message wastes space. The two ends can instead agree on it before compression. With preset history `AB`, a body can begin with a length-6, distance-2 match and produce `ABABAB`: the first two output bytes come from the dictionary and later copies can use newly produced bytes. The dictionary is a source of history, not output. This is a possible format description, not a promised compressor choice.

Reset alone cannot create this context. For a new zlib task that requests the dictionary, the application must install the agreed bytes. If it presents the wrong identifier, decoding should remain at the request so it can retry; a failed check must not silently select the wrong history.

The ordinary zlib exchange is [deflateSetDictionary](/reference/functions/deflateSetDictionary.html), compressed bytes carrying the dictionary identifier, `Z_NEED_DICT`, then [inflateSetDictionary](/reference/functions/inflateSetDictionary.html). The identifier is Adler-32 of the entire supplied dictionary; retained history is bounded to a window-sized suffix. Equal identifiers do not establish equal bytes: correctness still needs the appropriate dictionary context.

The focused compressor workflow installs a non-NULL, readable dictionary immediately after initialization or ordinary reset, before compression. The public operation also includes repeated pre-start zlib calls, which accumulate Adler-32, and legal raw replacement. The C refuses gzip, nonzero lookahead, inappropriate zlib status, or a raw position that is not a completed block boundary with `Z_STREAM_ERROR`. It allocates nothing and restores the temporary input binding; dictionary loading can increase `total_in` without delivering dictionary bytes as message output.

On the decoder, zlib installation requires the waiting dictionary state. A wrong identifier returns `Z_DATA_ERROR` without changes, permitting another attempt. Raw mode allows installation at call boundaries without an identifier check; gzip has no preset-dictionary path. The decoder copies the bytes, advances no input/output pointers or totals, and may allocate its window. Failure returns `Z_MEM_ERROR` in an endable memory-error state. NULL dictionary is a refusal even for zero length; zero-length non-NULL raw dictionaries are accepted.

## Supply the bits already read by a container {#prime}

Some containers start a raw DEFLATE body partway through a byte. The surrounding parser may already have extracted those first bits, so feeding only the remaining whole bytes would lose them. Prime supplies such bits without pretending they arrived as another full input byte. For example, appending three bits from the value 5 contributes low bits `1, 0, 1`, in that order; their meaning still depends on the body being decoded.

[inflatePrime](/reference/functions/inflatePrime.html) places supplied bits before the next input byte. Zero bits changes nothing; a negative count clears held bits. Counts 1–16 append the low value bits above existing bits when the total fits 32 bits. Excess count or space returns `Z_STREAM_ERROR` unchanged.

[deflatePrime](/reference/functions/deflatePrime.html) appends 0–16 low value bits to pending output without delivering bytes to `next_out`. Insufficient space returns `Z_BUF_ERROR` without inserting bits, although existing pending bytes can first be compacted. Counts outside the range are refused before compaction. Its ordinary use prefixes raw output before the first compression call after init/reset.

A failed stream check gives `Z_STREAM_ERROR` for either entry without inserting bits. The C does not enforce every raw-mode or timing premise in these focused workflows. Outside those premises is not automatically UB or a documented clean refusal. Arbitrary inserted fragments need not produce an ordinary valid stream; the operation's exact bit effects and its format interpretation remain distinct obligations.

## Capture or emit caller-owned header metadata {#headers}

An application displaying a gzip member's original name needs storage for metadata separately from the decoded file bytes. It registers that storage before parsing reaches the header. A short destination may capture only a prefix: registration does not promise an unlimited string or transfer ownership of the destination.

[inflateGetHeader](/reference/functions/inflateGetHeader.html) registers caller-owned gzip metadata storage and sets `done` to zero. The record and optional extra/name/comment destinations remain alive and writable until parsing ends or registration is cleared. Their capacities limit writes; a name terminator appears only if it fits. `done` becomes 1 for completed gzip capture or -1 when automatic detection instead recognizes zlib.

No ownership transfers. Reset clears registration without freeing the record. A failed stream check or wrapper without gzip support returns `Z_STREAM_ERROR`; NULL header on an otherwise accepted request is dereferenced by C, not a clean-error case. [deflateSetHeader](/reference/functions/deflateSetHeader.html) borrows the corresponding emission metadata until header output finishes. Late registration cannot rewrite bytes already emitted. Exact storage-separation restrictions belong to the linked contracts.

## State-operation proof connections {#proof-obligations}

At this checkpoint, the useful promise is concrete: Reset cannot let B read A's discarded history; Copy cannot leave a private table pointer aimed into A; a failed allocation cannot destroy the source or strand destination blocks; borrowed headers must stay within the caller's valid destinations. Equal counters alone establish none of those promises. The proof must derive the state, pointer and ownership relationships from actual init and permitted histories, and relate both copied continuations to the same saved progress. Per-entry contracts specify these obligations; the [ownership chapter](/sample/ownership-proof.html) explains their composition. Current acceptance remains recorded in [progress](/reference/docs/progress.html).

At the four-byte checkpoint, continuing or copying must preserve valid sources for the remaining `ABAB`; ordinary Reset must prevent a new message from using those sources. Follow [actual allocation and cleanup](/sample/allocation.html) next to account for the objects supporting those choices, especially when Copy or delayed-window allocation fails midway.
