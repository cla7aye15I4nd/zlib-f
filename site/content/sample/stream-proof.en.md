An application wants `ABABABAB` but has only a five-byte output buffer. In the [running C example](/sample/stream-state.html#history), it supplies compressed bytes `73 74 82 40 00`, calls `inflate`, handles `ABABA`, then reuses the buffer and gets `BAB`. The first call returns `Z_OK`; the second returns `Z_STREAM_END`.

That run answers “what happened for these bytes?” A proof must also answer “why can this continue safely and recover the right bytes for every allowed call history?” It must connect the actual writes to the compressed input, preserve unfinished work across the buffer change, and account for failures and resource release. The observations `ABABA` and `BAB` are the starting evidence to explain, not an assumption that decoding is correct.

## What the two-call example asks us to prove {#example-obligations}

| Observation or action | Required argument |
| --- | --- |
| Call 1 consumes 4 compressed bytes and writes `ABABA`. | Actual input bits justify this output prefix; prefetched bits need not all have been interpreted. |
| Three match bytes remain at return. | Saved mode, remaining length and distance describe exactly the unfinished work. |
| The application reuses the five-byte output buffer. | Necessary old bytes survive in owned history, and future reads use valid storage. |
| Call 2 writes `BAB` and completes. | New output extends the same result; raw block completion justifies `Z_STREAM_END`. |
| An allowed call fails or the application ends the task. | Its actual writes, counters, allocations and cleanup still satisfy the relevant safety contract. |

The subject is the statement-by-statement C translation: its heap, saved fields and returned pointers. An independent format relation describes which original bytes a compressed stream means. The rest of the chapter explains how the argument must connect them. Named local lemmas below are components with explicit premises, not a claim that the complete decoder has already been proved. [Progress](/reference/docs/progress.html) records accepted evidence.

## The continuation relation {#continuation}

To resume the example, the next call needs more than the fact that the previous output spelled `ABABA`. Keep four connected records at the call boundary:

| Record | What it describes in the example |
| --- | --- |
| Caller storage | The remaining compressed input and the new writable output range. |
| Private decoder state | Its live allocation, `MATCH` mode, remaining 3 bytes, distance 2, tables and owned history. |
| Data history | The consumed compressed prefix and the recovered prefix `ABABA`. |
| Format progress | Raw mode here; for a wrapper, its dictionary, checksum and completion phase as well. |

A **representation invariant** states that the saved fields, allocations and byte contents agree. The proof model uses `Good` for a shared state condition. A proof must establish such a condition at initialization and preserve it through actual calls; it cannot simply assume the desired callee contract.

For the running match, let `H` be chronological history before the next byte and `d = 2`. One expansion step appends `H[|H|-d]`. Appending that byte also changes the history used by the following step. The invariant must therefore connect the saved remaining length to the already expanded prefix, not simply say that `length ≤ 258` and the distance is in range.

Across the first return, the logical prefix is `ABABA`. The example reuses the same output memory; a legal later call can instead replace the allocation. The old output allocation then need not remain available. What must remain is a valid representation of the required suffix. A useful content equation is:

```text
new_history = suffix_window(old_history ++ newly_produced)
```

The physical ring need not have that order in increasing array indices. Its `wnext` and `whave` fields determine the chronological list. After rebuffering, the first resumed `B` is justified by that list; after enough new output, the source can move into the current caller buffer. The proof of a source read must explain which of these cases applies.

The actual [`updatewindow_ring_public`](/reference/source/ZlibF/Proof/inflate.c.window-public-ring.html#L82) relates the returned ring contents to the old chronological ring followed by the new source bytes, with the excess prefix dropped. Its scope includes an existing writable window, `Good`, the exact allocated size, readable source bounds and explicit range separation. It is a concrete content-preservation component. Establishing that its old ring already represents the decoder's logical history, and calling it from every required return path, are additional composition obligations.

## Which input bits justify the output? {#prefix}

Input accounting needs the same care as output history. A table lookup can inspect more bits than the selected symbol consumes. In [the decode-table example](/sample/decode-tables.html), A uses one bit even though the root index examines two. The second bit can already belong to D. Requiring the A result to be justified by a complete interpretation of every prefetched bit would attach the wrong amount of evidence to that result.

Instead, associate each output prefix with a **supporting bit prefix**: enough source bits to determine those bytes under the independent format relation. Bits beyond that prefix remain lookahead. A later malformed symbol or trailer must not invalidate the fact that an earlier supported prefix was correctly produced. The fast path can also return whole lookahead bytes to caller input; transport the same source position through that adjustment.

The model's [`output_evidence_determined`](/reference/source/ZlibF/Proof/Api/InflateCausality.html#L19) derives byte-prefix determinacy from causal bit-prefix evidence. Its subject is the heap-free API relation, not the C translation. That distinction identifies a real task: prove that the actual table, extra-bit and copy executions establish the evidence required by the model. A model theorem becomes applicable only after this bridge exists.

The source includes a concrete guard against an overly permissive relation: [`inflate_no_input_mem_cannot_guess`](/reference/source/ZlibF/Proof/Api/Inflate.html#L41) rules out inventing byte `a` from a fresh raw stream with no consumed input, even on a memory-error result. Allowing an error does not license arbitrary output. The same principle applies to ordinary successful prefixes and to dictionary-dependent output.

## Why the next call starts in a valid state {#calls}

A single-call preservation statement is conditional on its input state. To obtain a lifetime claim, that condition must come from actual initialization and earlier legal calls. [`StreamReachable`](/reference/source/ZlibF/Spec/Public/History.html#L89) is built from actual successful init, legal caller rebinding, actual operations and successful copies. It does not insert a callee's desired contract as an assumption about a previous call.

The caller step uses [`Rebuffer`](/reference/source/ZlibF/Spec/Public/History.html#L50). It allows the application to replace input/output bindings and unowned storage while preserving private stream storage and the other control fields. The next operation separately needs readable/writable ranges, separation, live borrowed headers and the accepted platform premises. In the selected LP64 scope, the byte-object size bound is an explicit environment condition, not a limit on the total number of bytes a long stream may process.

For data meaning, [`DataStep`](/reference/source/ZlibF/Spec/Public/Sequences.html#L66) records the actual execution and the bytes observed in its returned output slice. The trace appends `input.take used` and the newly written output. This is an observation, not a premise that the output is correct. The sequence target must establish that the accumulated observations satisfy the independent decoding relation.

A dictionary is a separate history contribution. Before the zlib handshake is resolved, the required bytes may be unknown even when their checksum identifier is known. Once the actual `inflateSetDictionary` accepts a dictionary, the argument connects its copied suffix to the dictionary used by the format relation. Raw dictionary replacement after decoding has started can introduce several history contexts; `DataLog.singleDictionary` explicitly records when the ordinary single-dictionary statement no longer describes that epoch. Dropping that distinction would claim a stronger theorem than the target states.

## What a return has already changed {#returns}

Follow one actual run through all of its exits. A mode's local `break` returns to dispatch. `Ex.leave` reaches the common return path with the local registers as they stand. A direct `Ex.ret` has different accounting. The dictionary request, malformed-data mode and window-allocation failure therefore cannot all be treated as one abstract “stop.”

[`StreamAccounting`](/reference/source/ZlibF/Spec/Public/Streams.html#L12) connects `used` and produced length to the new pointers and available counts, while preserving the stream identity and fixed allocator/control fields. The [public inflate target](/reference/functions/inflate.html#formal-target) also distinguishes normal total updates from a late `Z_MEM_ERROR`: the call can have written output and published advanced cursors before `updatewindow` fails, while the later total/checksum account has not run. For that exit, an unchanged-total conclusion is compatible with nonempty actual output. An unchanged-output conclusion is not.

The pinned [common return path](https://github.com/madler/zlib/blob/757f0527154291bcf6bfbd6396ecde6bedd2db95/inflate.c#L1140-L1155) shows the order that the proof must preserve:

```c
    RESTORE();
    if (state->wsize || (out != strm->avail_out && state->mode < BAD &&
            (state->mode < CHECK || flush != Z_FINISH)))
        if (updatewindow(strm, strm->next_out, out - strm->avail_out)) {
            state->mode = MEM;
            return Z_MEM_ERROR;
        }
```

`RESTORE` publishes the new pointers before the allocation can fail. The additions to `total_in`, `total_out` and `state->total` occur after this excerpt. In our successful two-call run they are reached; on this late memory-error exit they are skipped. That statement order is why a proof must track the returned output slice separately from total counters. The universal execution argument for this C reading is **to confirm**.

## Why every individual call returns {#termination}

Termination requires a bound on mode transitions as well as byte loops. Installing a table or changing from a decoded length to its distance can move the state without consuming a new byte or producing output. “Input decreases on every iteration” is therefore not the right invariant. One route combines finite input, output and remaining-copy measures with a bounded ordering of internal mode transitions.

The existing [`xwhileBrk_rank`](/reference/source/ZlibF/Proof/inflate.c.xloop-rank.html#L10) makes the local-to-loop step precise: a continuing iteration preserves its predicate and strictly decreases a rank read from registers and heap; exits establish the postcondition; the initial rank plus two must fit the loop fuel. The theorem supplies the induction principle. A complete decoder application must still give that predicate, prove each actual mode case and establish the initial fuel bound. Naming the rank lemma alone does not establish those facts.

## Wrapper and completion relations {#wrappers}

The [wrapper chapter](/sample/wrappers.html) supplied the last piece of the same task. Headers must establish the selected format and window conditions; dictionary bytes must become history rather than output; payload updates must use exactly the produced bytes; trailers must be read in their specified byte order. Registered gzip metadata adds separate caller-owned write regions with their own lifetimes.

The actual [`inflate_CHECK_run`](/reference/source/ZlibF/Proof/inflate.c.main.check.html#L157) separates insufficient trailer input, a mismatching enabled check, and the continuation into `LENGTH`. Its premises include `BitInv`, correct CRC statics and a `PutAt` relation identifying the just-written output slice. Its Adler value clause explicitly retains the one-byte/noncanonical-seed condition rather than assuming every arbitrary accumulator is canonical. A full caller argument derives the required accumulator property from the history where applicable.

`CHECK` updates output accounting before changing the local output baseline. Later return accounting must use the changed baseline, so it does not count those bytes twice. Gzip length comparison uses the low 32 bits of produced size. Disabled validation follows its own accepted configuration; it cannot be proved equivalent to enabled validation by forgetting the setting.

## Which completion guarantee is being requested? {#completion-scope}

The two-call run used a full-size raw decoder. Other permitted configurations need separate conclusions. The [inflate sequence target](/reference/source/ZlibF/Spec/Public/Sequences.html#L158) distinguishes:

| Claim | Does it require `FullWindow`? |
| --- | --- |
| Safety and cleanup for allowed histories. | No. |
| An ordinary single-dictionary data epoch that actually returns `Z_STREAM_END` has accumulated input/output satisfying the independent decoding relation. | No. |
| A valid source yields its correct output prefix without `Z_DATA_ERROR`, under the stated valid-source, single-dictionary and consumed-prefix conditions. | Yes: [`Api.FullWindow`](/reference/source/ZlibF/Spec/Api/Basic.html#L130). |

“Single-dictionary” describes an epoch whose data meaning can use one dictionary; it does not say that every possible raw dictionary replacement fits this clause.

`FullWindow` selects a 32 KiB window, or the specified zero-bit requests whose header/default choice gives that full window. For zero effective window bits, zlib must announce 15 in its header, gzip uses the default 15, and automatic detection admits the corresponding zlib or gzip case. A smaller retained window can reject a format-valid stream depending on how the caller splits output: current-call output and retained history provide different amounts of accessible match history. Format validity alone therefore does not establish acceptance under every accepted window configuration.

The separate [`InflateCompletes`](/reference/source/ZlibF/Spec/Public/Sequences.html#L128) clause retains `FullWindow` and adds an unfinished single-dictionary trace, the actual `Good` state, valid caller buffers and active header storage, no allocation failure, and modes outside `BAD`, `MEM` and `SYNC`. A pending dictionary must already be resolved. The consumed input log must be a prefix of the valid source. The current input range must contain exactly its remaining bytes, the output range must have enough room, and flush must be `Z_NO_FLUSH`, `Z_SYNC_FLUSH` or `Z_FINISH`. Under those premises the next actual call must reach `Z_STREAM_END` and write the remaining decoded suffix. Supplying more room alone cannot replace the other premises. These targets are stronger than one mode lemma or the heap-free causal theorem: their components must be joined on the same returned heaps. The [component guide](/reference/docs/proof/inflate.html) gives the detailed obligations, and [progress](/reference/docs/progress.html) records accepted evidence and remaining work.
