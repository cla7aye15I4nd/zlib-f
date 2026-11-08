## Recover the original bytes {#connection}

[Compression](/verification/output.html) turns repeated input into literals and matches, then encodes them as compressed bytes. Decoding runs in the opposite direction. It does not search for repetitions again: it reads the instructions already chosen by the sender and restores their bytes in order.

Take the complete raw DEFLATE stream `73 74 82 40 00`. These five hexadecimal bytes describe literals `A` and `B`, then “go back two bytes and copy six bytes,” followed by the final block's end. The result is the eight-byte text `ABABABAB`. The compressed bytes cannot be read directly as letters; the decoder must first locate the encoded fields within them.

<ol class="bk-route-flow" aria-label="Recover eight original bytes from compressed input">
<li><strong>Compressed input</strong><code>73 74 82 40 00</code><span>The application supplies whole bytes</span></li>
<li><strong>Interpret bits</strong><span>Read block type, codes and extra bits</span><span>Tables determine each symbol's bit consumption</span></li>
<li><strong>Recover instructions</strong><code>A · B · length 6 / distance 2</code><span>A block-end marker follows</span></li>
<li><strong>Produce output</strong><code>AB → ABABABAB</code><span>Expand the match one byte at a time</span></li>
</ol>

There are two distinct actions: **interpret compressed input to obtain an instruction, then execute that instruction to produce bytes.** A match is decoded once but can write many bytes. This distinction explains how a decoder can continue producing output without reading more input.

## Find the next bit, then the next symbol {#bits-and-tables}

The encoder packs fields of different lengths tightly into bytes. The decoder cannot discard an entire input byte whenever one field ends. [Input bits](/sample/input-bits.html) first joins a three-bit remainder to another byte, then decodes `AD` using the teaching code `A=0, B=10, C=110, D=111`. That small code isolates bit order and lookup; it is not another representation of the five-byte stream above.

Lookup tables avoid walking a tree one bit at a time for every symbol. They also introduce a distinction: inspecting two bits does not necessarily consume two bits. A's code has only one bit; the other inspected bit already belongs to D. [Decode tables](/sample/decode-tables.html) builds that very table, explaining repeated slots for short codes, subtables for long ones, and entries that describe both an action and its bit consumption.

A real DEFLATE stream selects fixed tables or describes code lengths in a dynamic block header. [Codes and length descriptions](/sample/huffman-lengths.html) follows the sender's description; the decoding-table chapter takes the parsed lengths and constructs arrays that can actually be queried. Both ends use the same canonical assignment rule.

## Turn symbols into bytes {#output}

A literal A writes one A. A length and distance invoke the repetition rule. [Match copying](/sample/decode-copy.html) expands a six-byte match after `AB`: the third copy already reads the A written by the first. That is why the original two bytes cannot be treated as an unchanging source interval.

The same chapter develops zlib's two execution routes. With little output room, the ordinary state machine preserves an unfinished match. With enough input and output, the fast path checks the margins for an entire instruction and removes repeated checks inside the loop. Both must produce the same bytes and leave the same unconsumed input.

## Preserve meaning through optimization {#guarantees}

The pipeline gives the proof concrete obligations: preserve input bits, construct tables that return the right symbol, copy the right bytes, and retain unfinished work across a pause. [Connecting decoder correctness](/sample/decode-proof.html) develops those relations along the same steps. Changing A's consumption from one bit to two can remain a safe integer operation while deleting D's first bit. Swapping two table entries can remain entirely in bounds while changing output. Memory bounds and byte meaning must be established together.

The complete decoder composition is unfinished. Bit preservation, table content, copying and actual return states still need to be connected along the same execution; [progress](/reference/docs/progress.html) records the remaining work. The [`inflate` contract](/reference/functions/inflate.html) gives the complete public parameters, return cases and storage requirements.

## Deliver the result to the application {#continuation}

Even for `ABABABAB`, the caller may not offer eight output slots at once. [Streaming and wrappers](/verification/streaming.html) continues with a five-byte buffer: deliver `ABABA`, preserve the remaining match, then deliver `BAB`. With zlib or gzip, decoding the body must also be followed by reading its trailer. That is where checksums join the same decoding task.
