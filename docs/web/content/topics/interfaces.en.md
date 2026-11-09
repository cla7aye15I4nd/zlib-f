## From byte processing to an application {#connection}

[Compression](/sample/blocks.html) turns original data into an encoding; [decoding](/sample/decode-copy.html) recovers the bytes. [Streaming](/sample/stream-state.html) lets processing pause: preserve state when output space runs out, supply another buffer, then continue. An application still has another choice to make: **who supplies those buffers, and who controls the next processing step?** That is where the interface families differ.

Keep the eight bytes `ABABABAB`. If the source and destination are already in memory, a utility can complete the task in one call. If encoded data comes from a custom container, callbacks can let the decoder request each piece. For a gzip file, `gzFile` can manage file reads, decoding and buffering together. These are choices for different tasks, not three stops in one execution.

## Choose by source and control {#choices}

| What the application has | Who controls processing | What is delivered | Route |
| --- | --- | --- | --- |
| Successive byte ranges; the application needs to replace input and output buffers itself | An application loop calls `deflate` or `inflate` | Consumed and written prefixes, plus state for continuation | [Use the stream API directly](/sample/interfaces.html) |
| A complete source or complete zlib encoding; a known destination capacity | A utility creates a temporary stream and runs its internal loop | Destination bytes and actual lengths; counted decoding also returns input consumption | [Complete buffers](/sample/buffers.html) |
| Raw DEFLATE pieces inside a custom container; callbacks and a decode window | One `inflateBack` call requests input and delivers output | Accepted output callback bytes and unread input from the last piece | [Callback decoding](/sample/callbacks.html) |
| A file path or descriptor; ordinary bytes should be read, or written as gzip | The application issues file requests; the handle manages buffering and its stream | File read/write results, logical position and error state | [Gzip files](/sample/gzip.html) |

Both format and control must fit. Buffer decoding utilities accept a zlib wrapper. `inflateBack` accepts only raw DEFLATE. Gzip file operations add member and file behavior. Direct streams select their wrapper through initialization parameters. Sharing the task of decompression does not make these inputs interchangeable. [Wrapper layout](/sample/wrappers.html#layout) explains how their encoded bytes differ.

## Format mechanisms and caller responsibilities {#engines}

Complete-buffer utilities enclose the ordinary stream protocol inside a function. To compress `ABABABAB`, the application supplies the source address and destination capacity once; the utility performs this sequence:

<ol class="bk-route-flow">
<li><strong>Create a temporary stream</strong><span>Initialize codec state and prepare input and output slices.</span></li>
<li><strong>Run to completion or error</strong><span>Call the stream engine, refill availability fields, and retain real consumption and production counts.</span></li>
<li><strong>End the temporary state</strong><span>Release internal resources and return lengths and the result.</span></li>
</ol>

No resumable stream remains after that utility returns. A gzip handle instead retains its internal stream between file operations. One `gzread` can fetch more encoded input while delivering only the requested original bytes. Descriptor position and delivered-data position therefore diverge.

`inflateBack` uses a separate callback decode loop in `infback.c`; it does not repeatedly call ordinary `inflate`. It still parses DEFLATE blocks, looks up symbols and copies bytes by distance. Its input comes from callbacks, and its decode window also supplies output callback slices. The byte meaning from [distance copying](/sample/decode-copy.html) remains the same; loop control and storage lifetimes change.

## Carry the result into its proof {#proofs}

Choosing an interface also chooses what the application can observe. Append `END` after the zlib encoding in the buffer task: success must recover eight bytes and stop input consumption before `END`. In the callback task, those eight bytes must appear in accepted output events; ordinary `next_out` accounting does not record their delivery. A file task adds descriptors, internal buffers and close obligations.

| Question left by the mechanism | Corresponding proof |
| --- | --- |
| Does the temporary stream report the right lengths and release allocated state on failure? | [Buffer composition](/sample/interfaces-proof.html#buffers) |
| Do active input and the window remain valid while callbacks change their own objects, and how does finite input support termination? | [Callback preservation and input budgets](/sample/interfaces-proof.html#callbacks) |
| Do returned bytes, logical position, descriptor position and resources after close agree? | [Heap and file world](/sample/interfaces-proof.html#files) |
| When the application continues a stream itself, how does one returned state become the next valid starting state? | [The cross-call argument](/sample/stream-proof.html) |

Follow one task through its mechanism and proof before choosing another. The [complete API index](/reference/api.html) retains precise arguments, refusal conditions, alias requirements and observations after errors. Those conditions determine which calls the examples generalize to.
