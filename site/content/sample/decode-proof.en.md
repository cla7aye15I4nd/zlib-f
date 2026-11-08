The decoder's promise is to recover the bytes described by the compressed input, in order. Reading ahead, using a lookup table, copying several bytes in one loop, or pausing for another buffer must preserve that promise. It must also stay within valid memory and handle detected bad data through defined error returns.

The starting information is the unconsumed compressed input, the decoder's saved work and historical bytes, and the caller's offered buffers. The result is a justified output prefix and an exact continuation state, or the specified completion/error result. “Justified” means the independent format rules explain those output bytes. It does not mean that any buffered prefix is already a complete valid stream. Fragmented input, small output buffers, malformed data and admitted failures remain in the stated domain.

## Check the promise on the examples {#example}

The previous chapters followed [source bits](/sample/input-bits.html), [installed tables](/sample/decode-tables.html) and [output copies](/sample/decode-copy.html). Keep these small calculations in view:

| Stage | Concrete step | What must remain true |
| --- | --- | --- |
| Pull a byte | Three saved bits plus `0xA5` become eleven held bits | No input bit changes or disappears merely because it moved into the reservoir |
| Decode A from `AD` | Inspect root `10`, return A, remove only one bit | Remaining input is `111`, the complete code for D |
| Follow a subtable | Root `11`, then subtable `1`, returns D | The actual installed cells agree with D's code |
| Copy after `AB` | Length six, distance two appends `ABABAB` | Each new byte equals the historical byte two positions behind it |
| Pause after two copies | Output is `ABAB`; four match bytes remain | Resuming must finish the same match without rereading its instruction |

These examples locate the obligations; they do not prove all inputs. The formal argument needs relations that continue to express these facts after *every* admitted step. Such a preserved relation is an **invariant**. To prove it about the C translation, first establish it from actual initialization, then show how each actual branch preserves it. An array bound alone cannot identify a symbol, and an abstractly correct symbol cannot justify an invalid read.

## Unconsumed input {#bit-prefix}

For the first two rows, compare all unread bits before and after the step. In the following teaching equation, `low_bits` lists the valid reservoir positions in reading order, `bits(unread_input_bytes)` expands the remaining bytes in that same order, and `++` joins lists. It is explanatory notation, not a copied Lean definition:

```text
remainingBits = low_bits(hold, bits) ++ bits(unread_input_bytes)
```

Pulling a byte changes where that sequence resides without changing its values or order. Dropping a decoded field removes exactly its prefix. Here is the actual consuming operation used by `inflate`, from [pinned `inflate.c`, lines 387–391](https://github.com/madler/zlib/blob/757f0527154291bcf6bfbd6396ecde6bedd2db95/inflate.c#L387-L391):

```c
#define DROPBITS(n) \
    do { \
        hold >>= (n); \
        bits -= (unsigned)(n); \
    } while (0)
```

For A, the caller must supply `n=1`: shifting `1110` gives `111` and the count falls from four to three. Supplying two would still leave an in-bounds integer operation, but it would delete D's first bit. The proof must establish both defined shifts and the correct removal amount. The source [`BitInv` and `stream`](/reference/source/ZlibF/Proof/inflate.c.main.macros.html#L29) connect locals to an actual readable input range and the normalized hold value.

[`PULLBYTE_succ`](/reference/source/ZlibF/Proof/inflate.c.main.macros.html#L89) states a real translated pull under that invariant and an explicit shift bound. [`NEEDBITS_run`](/reference/source/ZlibF/Proof/inflate.c.main.macros.html#L150) includes both success and input-exhaustion exits, preserving the unconsumed sequence while accounting for pulled bytes. These local statements do not themselves establish every main-decoder entry condition.

A decoded symbol depends on its supporting prefix. It need not describe every speculative bit already buffered. For AD, A consumes only the first bit although the root lookup inspects two. The same distinction must survive fast-path byte backtracking and resumption with new input views.

## Actual table content {#table-content}

For the subtable row, having a table with enough cells is insufficient: its cells must return D. The constructor's output must be the very table the decoder later reads. The [construction chapter](/sample/decode-tables.html#example) explains the producer's stages: `count` tallies each code length, `offs` locates its scratch positions, and `work` lists symbols in code order. Follow those actual updates, reversed codes, repeated stores and subtable links, then establish what the written cells mean for the supplied lengths.

The declaration [`inflate_table_content`](/reference/source/ZlibF/Proof/inftrees.c.content.html#L327) retains actual execution, return classification and table contents. Its [target definition](/reference/source/ZlibF/Spec/InflateTableContent.html#L32) makes the connection concrete: the returned heap contains the array, and the internal environment is an execution result tied to input lengths, kind, location and root width. Here “geometry” means the table regions, index bounds and links. These cannot be caller-supplied substitutes for running the constructor.

This still differs from a complete decoder interface. [`inflate_table_complete_decoder_safe`](/reference/source/ZlibF/Proof/inftrees.c.content.data.html#L295) explicitly requires a complete alphabet: the assigned codes leave no unused branches in the binary code tree. It does not cover empty or accepted incomplete single-symbol alphabets merely because the constructor can handle them. [`inflate_table_codes_decoder_safe`](/reference/source/ZlibF/Proof/inftrees.c.content.codes.html#L118) addresses the code-length-table interface under its constructor premises. Read each statement's domain separately.

## Lookup geometry and symbol meaning {#lookup}

[`LenTableSafe` and `DistTableSafe`](/reference/source/ZlibF/Proof/inffast.c.tableok.html#L63) describe bounded root regions, bounded one-level links and suitable leaves. Their length and extra-bit bounds justify the fast decoder's refills and shifts. The raw presence of 1444 allocated entries does not provide these facts.

In our teaching table, root `11` must lead to two readable cells; this is geometry. Subtable `1` must contain D with one-bit consumption; this is agreement with the independent code. Both are required. A mutation that swaps C and D can preserve every index bound while changing decoded output. The producer-to-consumer connection must retain exact `op`, `bits` and `val`, including invalid and end markers, at the same heap and returned width.

<div class="zl-demo-mount"><zlib-demo kind="table-proof"><p>A bounded table can still decode the wrong symbol. The teaching scene separates readable cells and bounded links from agreement with the intended canonical code.</p></zlib-demo></div>

A caller invokes the theorem about the translated constructor after establishing its premises. It cannot assume an unproved callee specification or silently exclude a valid input because a convenient intermediate theorem has a narrower domain.

## Output and logical history {#history}

For the copy and pause rows, compare bytes rather than just pointer positions. A literal extends output by that byte. A match follows the independent repetition rule: take the byte at the stated distance behind the current end, append it, and repeat. The available past consists of any preset dictionary followed by output so far, called the **logical history**. This definition includes newly written match bytes, as the `AB` example requires. The physical source can switch from the ring's tail to its start, then to current output, as in the six-byte worked match.

The proof therefore carries both shape and content. Window indices, live storage and initialized ranges justify access; a suffix relation says the retained window contains the most recent part of logical history, in its exact order. It identifies which historical byte each physical cell contains. A dictionary supplies history without being counted as new output. Replacing output buffers must preserve logical values without pretending old borrowed memory remains available forever.

[`copyMatch_run`](/reference/source/ZlibF/Proof/inffast.c.match.html#L100) records the actual fast copy's successful or too-far-distance behavior under explicit context, distance, length and room premises. It is an internal execution result, not the entire public decoder or a proof that initialization and every history establish those premises.

## Fast and slow composition {#composition}

Safety also includes preserving unrelated memory, called the **frame** requirement. The source [`inflate_fast_safe`](/reference/source/ZlibF/Proof/inffast.c.final.html#L257) states the helper's safety, termination, frame, normalization and writeback goal. [`actual_body_refines_token`](/reference/source/ZlibF/Proof/inffast.c.body-token.html#L685) relates one actual fast body to an independent token, block end or rejected token. A one-body refinement and a complete helper safety statement supply different conclusions.

The optimization can only be used after its premises are established. At the actual guard, the main decoder must derive the helper's six-byte input margin, 258-byte output margin, fewer-than-eight held bits, table properties and history. Slow dispatch must preserve a compatible relation for smaller buffers, unfinished fields and returned matches. `LOAD` and `RESTORE` connect local registers with boundary state; they do not hold those representations equal throughout the body. Some mode changes consume no input and write no output. Such a **silent transition** needs a decreasing rank: a measure showing that the decoder cannot keep changing modes forever without progressing or returning.

## Memory, termination and public scope {#scope}

Every access additionally needs liveness, writable or readable permission, bounds and the correct object. Writes must preserve unrelated memory, as required by the frame condition. Cleanup accounts for allocations on success, failure and End. The C/runtime correspondence still includes pointer, alignment and uninitialized-memory limitations recorded in [safety](/reference/docs/spec/safety.html) and the [trusted base](/reference/docs/trusted-base.html).

The executable model gives loops a finite iteration budget, called **fuel**. Termination must exclude exhaustion of that actual budget. Finite copy counts, bounded table links, progress measures and silent-transition ranks need composition into that concrete budget. The theorem's internal premises must come from actual initialization and allowed history operations, including refused calls.

These are explanations of declarations and obligations, not new acceptance claims. [Progress](/reference/docs/progress.html) records accepted scope and remaining work; [`inflate`](/reference/functions/inflate.html) states the public behavior to establish. Continue to [stream state](/sample/stream-state.html) to follow this argument across call boundaries. As a separate comparison, [compression block output](/sample/blocks.html) follows the reverse direction: symbols becoming bits, pending bytes and delivered output.
