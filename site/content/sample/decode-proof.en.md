The decoder route has followed the same information through three forms: [buffered source bits](/sample/input-bits.html), [installed decode tables](/sample/decode-tables.html), and [literal or match output](/sample/decode-copy.html). A proof has to connect those forms on the actual execution. An array bound alone cannot identify a symbol, and a correct abstract symbol cannot justify an invalid memory read.

Keep `AD` and the overlapping `ABABABAB` match in view. The examples explain individual connections. The target still quantifies over the whole stated domain, including fragmented input, small output buffers, malformed data and admitted failures. They are not restrictions added to make the argument easier.

## Unconsumed input {#bit-prefix}

The reservoir chapter distinguished pulling from consuming. The useful invariant describes one unconsumed sequence:

```text
remainingBits = low_bits(hold, bits) ++ bits(unread_input_bytes)
```

Pulling a byte changes where that sequence resides without changing its values or order. Dropping a decoded field removes exactly its prefix. The source [`BitInv` and `stream`](/reference/source/ZlibF/Proof/inflate.c.main.macros.html#L29) connect locals to an actual readable input range and the normalized hold value.

[`PULLBYTE_succ`](/reference/source/ZlibF/Proof/inflate.c.main.macros.html#L89) states a real translated pull under that invariant and an explicit shift bound. [`NEEDBITS_run`](/reference/source/ZlibF/Proof/inflate.c.main.macros.html#L150) includes both success and input-exhaustion exits, preserving the unconsumed sequence while accounting for pulled bytes. These local statements do not themselves establish every main-decoder entry condition.

A decoded symbol depends on its supporting prefix. It need not describe every speculative bit already buffered. For AD, A consumes only the first bit although the root lookup inspects two. The same distinction must survive fast-path byte backtracking and resumption with new input views.

## Actual table content {#table-content}

The constructor's output must be the very table the decoder later reads. First follow the actual `count`, `offs`, ordered `work`, reversed codes, repeated stores and subtable links. Then establish what those written cells mean for the supplied lengths.

The declaration [`inflate_table_content`](/reference/source/ZlibF/Proof/inftrees.c.content.html#L327) retains actual execution, return classification and table contents. Its [target definition](/reference/source/ZlibF/Spec/InflateTableContent.html#L32) makes the connection concrete: the returned heap contains the array, and the internal environment is an execution result tied to input lengths, kind, location and root width. Geometry is not a caller-supplied substitute for running the constructor.

This still differs from a complete decoder interface. [`inflate_table_complete_decoder_safe`](/reference/source/ZlibF/Proof/inftrees.c.content.data.html#L295) explicitly requires a complete alphabet. It does not cover empty or accepted incomplete single-symbol alphabets merely because the constructor can handle them. [`inflate_table_codes_decoder_safe`](/reference/source/ZlibF/Proof/inftrees.c.content.codes.html#L118) addresses the code-length-table interface under its constructor premises. Read each statement's domain separately.

## Lookup geometry and symbol meaning {#lookup}

[`LenTableSafe` and `DistTableSafe`](/reference/source/ZlibF/Proof/inffast.c.tableok.html#L63) describe bounded root regions, bounded one-level links and suitable leaves. Their length and extra-bit bounds justify the fast decoder's refills and shifts. The raw presence of 1444 allocated entries does not provide these facts.

Geometry is one requirement; agreement with the independent code is another. A mutation that swaps C and D can preserve every index bound while changing decoded output. The producer-to-consumer connection must retain exact `op`, `bits` and `val`, including invalid and end markers, at the same heap and returned width.

<div class="zl-demo-mount"><zlib-demo kind="table-proof"><p>A bounded table can still decode the wrong symbol. The teaching scene separates readable cells and bounded links from agreement with the intended canonical code.</p></zlib-demo></div>

A caller invokes the theorem about the translated constructor after establishing its premises. It cannot assume an unproved callee specification or silently exclude a valid input because a convenient intermediate theorem has a narrower domain.

## Output and logical history {#history}

For a literal, extend the output by that byte. For a match, the independent repetition rule copies from the dictionary-plus-output history one byte at a time. The physical source can switch from the ring's tail to its start, then to current output, as in the six-byte worked match.

The proof therefore carries both shape and content. Window indices, live storage and initialized ranges justify access; a suffix relation identifies which logical historical byte each cell contains. A dictionary supplies history without being counted as new output. Replacing output buffers must preserve logical values without pretending old borrowed memory remains available forever.

[`copyMatch_run`](/reference/source/ZlibF/Proof/inffast.c.match.html#L100) records the actual fast copy's successful or too-far-distance behavior under explicit context, distance, length and room premises. It is an internal execution result, not the entire public decoder or a proof that initialization and every history establish those premises.

## Fast and slow composition {#composition}

The source [`inflate_fast_safe`](/reference/source/ZlibF/Proof/inffast.c.final.html#L257) states the helper's safety, termination, frame, normalization and writeback goal. [`actual_body_refines_token`](/reference/source/ZlibF/Proof/inffast.c.body-token.html#L685) relates one actual fast body to an independent token, block end or rejected token. A one-body refinement and a complete helper safety statement supply different conclusions.

The main decoder must derive the helper's margins, table properties and history at its real fast guard. Slow dispatch must preserve a compatible relation for smaller buffers, unfinished fields and returned matches. `LOAD` and `RESTORE` connect local registers with boundary state; they do not hold those representations equal throughout the body. Silent mode transitions also need a rank, since not every dispatch consumes input or writes output.

## Memory, termination and public scope {#scope}

Every access additionally needs liveness, writable or readable permission, bounds and the correct object. Writes must preserve unrelated memory. Cleanup accounts for allocations on success, failure and End. The C/runtime correspondence still includes pointer, alignment and uninitialized-memory limitations recorded in [safety](/reference/docs/spec/safety.html) and the [trusted base](/reference/docs/trusted-base.html).

Termination must exclude the actual model's fuel exhaustion. Finite copy counts, bounded table links, progress measures and silent-transition ranks need composition into that concrete budget. The theorem's internal premises must come from actual initialization and allowed history operations, including refused calls.

These are explanations of declarations and obligations, not new acceptance claims. [Progress](/reference/docs/progress.html) records accepted scope and remaining work; [`inflate`](/reference/functions/inflate.html) states the public behavior to establish. Continue to [stream state](/sample/stream-state.html) to follow this argument across call boundaries. As a separate comparison, [compression block output](/sample/blocks.html) follows the reverse direction: symbols becoming bits, pending bytes and delivered output.
