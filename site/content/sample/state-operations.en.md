The [streaming chapter](/sample/stream-state.html) continues one task with replacement buffers. A reset starts another task; a copy branches the current one. Dictionaries, supplied bits and borrowed headers change what those continuations mean. Follow the data each operation keeps before deciding whether its next output is an independent stream.

Keep the running example: decoder A has delivered `ABAB` from `ABABABAB`, with four match bytes still to produce. Reset abandons that work for message B. Copy preserves the checkpoint for two continuations. An agreed dictionary supplies history to a new task rather than recovering this one. These are different uses of retained bytes.

The mechanisms below follow the selected C and focused contracts, **to confirm** through the corresponding execution proofs. Those focused workflows do not narrow the broader public targets. Caller storage, readable/writable ranges and sequential use remain required; a pointer's C type does not establish its lifetime.

## Reset and retained history {#reset}

Suppose decoder A has delivered `ABAB`. The application keeps those bytes. To decode independent message B, it calls [inflateReset](/reference/functions/inflateReset.html), then supplies B's buffers. Reset forgets A's progress and makes its old history unavailable to matches. It does not erase delivered application bytes or move an external file position. Existing I/O pointers and available counts remain unchanged, so changing their bindings is still the caller's job.

The three decoder resets differ precisely:

| Entry | Progress and history | Configuration and allocation |
| --- | --- | --- |
| [inflateResetKeep](/reference/functions/inflateResetKeep.html) | Clears totals, held bits, dictionary-set status and header registration; retains window history. | Retains current wrapper/window settings and allocations. It does not restore wrapper changes made by recovery. |
| [inflateReset](/reference/functions/inflateReset.html) | Performs the progress reset and empties logical history. | Restores the requested wrapper/window, retaining a compatible window or freeing an obsolete one. Preserves the validation choice. |
| [inflateReset2](/reference/functions/inflateReset2.html) | Abandons progress, history and header registration. | Selects a new accepted wrapper/window request and enables its validation; frees incompatible window storage. Invalid values return `Z_STREAM_ERROR` unchanged. |

All three return `Z_OK` for the accepted live-stream reset. A failed stream check returns `Z_STREAM_ERROR` without changes; a dangling arbitrary pointer is not covered by that clean refusal.

`inflateReset2` includes every signed window argument in its focused parameter domain. Requests such as -15, 15, 31 and 47 select raw, zlib, gzip and automatic detection; the [inflateInit2_ contract](/reference/functions/inflateInit2_.html) lists all accepted values, including special zero-size requests. Reset never allocates a replacement window itself.

[deflateReset](/reference/functions/deflateReset.html) retains the compressor's five allocations and current level, strategy, wrapper and memory settings. It discards pending output, unfinished lookahead, bit progress and match history; default tuning for the current level is restored. [deflateResetKeep](/reference/functions/deflateResetKeep.html), an undocumented entry like its decoder counterpart, retains window/hash history and tuning. Both restart wrapper output and forget a custom gzip header. Neither certifies that abandoned work was delivered. A later match after ResetKeep can refer before the reset, so empty-history decoding is not promised.

## Dictionary context {#dictionary}

With preset history `AB`, a body can begin with a length-6, distance-2 match and produce `ABABAB`. The dictionary is a source of history, not output. This is a possible format description, not a promised compressor choice.

The ordinary zlib exchange is [deflateSetDictionary](/reference/functions/deflateSetDictionary.html), compressed bytes carrying the dictionary identifier, `Z_NEED_DICT`, then [inflateSetDictionary](/reference/functions/inflateSetDictionary.html). The identifier is Adler-32 of the entire supplied dictionary; retained history is bounded to a window-sized suffix. Equal identifiers do not establish equal bytes: correctness still needs the appropriate dictionary context.

The focused compressor workflow installs a non-NULL, readable dictionary immediately after initialization or ordinary reset, before compression. The public operation also includes repeated pre-start zlib calls, which accumulate Adler-32, and legal raw replacement. The C refuses gzip, nonzero lookahead, inappropriate zlib status, or a raw position that is not a completed block boundary with `Z_STREAM_ERROR`. It allocates nothing and restores the temporary input binding; dictionary loading can increase `total_in` without delivering dictionary bytes as message output.

On the decoder, zlib installation requires the waiting dictionary state. A wrong identifier returns `Z_DATA_ERROR` without changes, permitting another attempt. Raw mode allows installation at call boundaries without an identifier check; gzip has no preset-dictionary path. The decoder copies the bytes, advances no input/output pointers or totals, and may allocate its window. Failure returns `Z_MEM_ERROR` in an endable memory-error state. NULL dictionary is a refusal even for zero length; zero-length non-NULL raw dictionaries are accepted.

## Supplied bits {#prime}

[inflatePrime](/reference/functions/inflatePrime.html) places supplied bits before the next input byte. Zero bits changes nothing; a negative count clears held bits. Counts 1–16 append the low value bits above existing bits when the total fits 32 bits. Excess count or space returns `Z_STREAM_ERROR` unchanged.

[deflatePrime](/reference/functions/deflatePrime.html) appends 0–16 low value bits to pending output without delivering bytes to `next_out`. Insufficient space returns `Z_BUF_ERROR` without inserting bits, although existing pending bytes can first be compacted. Counts outside the range are refused before compaction. Its ordinary use prefixes raw output before the first compression call after init/reset.

A failed stream check gives `Z_STREAM_ERROR` for either entry without inserting bits. The C does not enforce every raw-mode or timing premise in these focused workflows. Outside those premises is not automatically UB or a documented clean refusal. Arbitrary inserted fragments need not produce an ordinary valid stream; the operation's exact bit effects and its format interpretation remain distinct obligations.

## Borrowed headers {#headers}

[inflateGetHeader](/reference/functions/inflateGetHeader.html) registers caller-owned gzip metadata storage and sets `done` to zero. The record and optional extra/name/comment destinations remain alive and writable until parsing ends or registration is cleared. Their capacities limit writes; a name terminator appears only if it fits. `done` becomes 1 for completed gzip capture or -1 when automatic detection instead recognizes zlib.

No ownership transfers. Reset clears registration without freeing the record. A failed stream check or wrapper without gzip support returns `Z_STREAM_ERROR`; NULL header on an otherwise accepted request is dereferenced by C, not a clean-error case. [deflateSetHeader](/reference/functions/deflateSetHeader.html) borrows the corresponding emission metadata until header output finishes. Late registration cannot rewrite bytes already emitted. Exact storage-separation restrictions belong to the linked contracts.

## Copies and pointer relocation {#copy}

At A’s `ABAB` checkpoint, a successful copy lets both decoders continue with the remaining `ABAB`. The already delivered prefix is still the application’s responsibility; Copy does not deliver it again. A checkpoint must retain buffered bits, tables, history and unfinished operations, together with recoverable unread input. A byte offset alone is insufficient. [inflateCopy](/reference/functions/inflateCopy.html) and [deflateCopy](/reference/functions/deflateCopy.html) require a distinct writable destination with no live owned state in the focused workflow; self-copy and overwriting a live destination do not receive that leak-free contract.

Successful decoder copy owns a new state and, if present, its own window. Dynamic table pointers into the source's embedded `codes` must move to the copy at the same offsets; static fixed tables can remain shared. The construction cursor also needs relocation. Compressor copy duplicates its five allocations, preserves initialized window/hash/pending/symbol content, and retargets pending cursors and embedded tree descriptors. Distinguishing static from owned pointers requires a valid provenance argument, not just two readable pointer values.

Both copies preserve the source and require separate End calls. Caller input/output pointers and retained header pointers are copied too: arrange suitable output destinations before continuing both, and keep shared borrowed metadata alive. Allocation failure frees the attempt's new blocks and clears destination state without consuming the source checkpoint. The [allocation chapter](/sample/allocation.html) follows this ledger; the [ownership proof](/sample/ownership-proof.html) explains how exact preservation and reachable-history claims are connected.
