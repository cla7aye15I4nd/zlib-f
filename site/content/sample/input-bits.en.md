The [algorithm overview](/algorithms/index.html) introduced bytes, symbols and blocks. The decoder now needs to bridge those representations. Two small fields explain its input side: `hold` contains buffered bits, and `bits` counts how many are valid. The input cursor points after the bytes already pulled into that reservoir, not necessarily after the last bit needed for a decoded symbol.

We will follow this distinction through an actual refill, then through the teaching message `AD`. Understanding it prepares the next chapter's [decode-table construction](/sample/decode-tables.html): the tables are arranged for the low bits that this reservoir exposes. Later, [stream state](/sample/stream-state.html) applies the same account when a call pauses and resumes.

## The bit reservoir {#reservoir}

The next available bit occupies bit 0 of `hold`. Later bits occupy successively higher positions. If `bits = 3`, only the lowest three positions are part of the buffered stream. A suitable normalized state has `hold < 2^bits`; the remaining input bytes follow those bits logically.

`LOAD` copies the stream's input/output cursors and the state's held bits into local registers. Parsing mostly uses those locals. `RESTORE` writes them back at the appropriate boundary. During the body, equating every heap field with its corresponding local would therefore describe the wrong execution point.

Consider `hold = 6`, written `110`, with three valid bits. The decoder will observe them in the order `0, 1, 1`. Reading an integer's usual left-to-right spelling would reverse that order. The number is storage; the low-to-high sequence is the input it represents.

## Byte refill and availability {#refill}

[`PULLBYTE`](/reference/source/ZlibF/Zlib/inflate.c.html#L446) first checks whether `have` is zero. With no byte available, it leaves for `inf_leave` before reading. Otherwise it decreases `have`, reads `*next`, advances `next`, appends the byte above the held bits, and increases `bits` by eight.

For the preceding state and next byte `0xA5 = 165`, the update is:

```text
old hold = 6, old bits = 3
new hold = 6 + (165 << 3) = 1326
new bits = 11
```

The low three bits remain unchanged. The next eight bits come from the new byte in its low-to-high order. A refill moves bits from unread memory into the reservoir; it does not consume a field or emit a symbol.

`NEEDBITS(n)` repeats this operation while fewer than `n` bits are buffered. It can stop after pulling some bytes but still fail to obtain enough because the offered input ends. Those pulled bits remain useful on the next call. Input exhaustion must not reset the reservoir or pretend the field was fully read.

## Inspection and consumption {#consumption}

`BITS(n)` masks the low `n` positions. It observes them without changing the reservoir. `DROPBITS(n)` then shifts `hold` right and decreases `bits`. The caller must first establish that enough bits exist; observation alone does not remove them.

These operations separate three accounts: bytes pulled from the caller, bits interpreted by the parser, and output bytes produced. A header field may consume bits without producing output. A match already decoded into state may produce many bytes without reading another input bit. One cursor cannot stand for all three quantities.

Ordinary numeric fields arrive least significant bit first. Huffman codewords arrive most significant code bit first, within byte positions that are still used low to high. Consequently, the codeword `110` occupies the reservoir's low positions as the integer `011`. The table builder anticipates this representation; the decoder need not reverse every input byte.

## A complete lookup trace {#trace}

Use the four-symbol teaching code `A=0`, `B=10`, `C=110`, `D=111`. Message `AD` arrives as `0 | 111`. Restricting the display to those four meaningful bits gives `hold = 1110`, `bits = 4`. This is an abstract code example, not a complete DEFLATE block or a claim that a byte refill reads only four bits.

<div class="zl-demo-mount"><zlib-demo kind="lookup"><p>AD arrives as 0,1,1,1. Root index 10 gives A but consumes only one bit. The remaining 111 follows root index 11, then subtable index 1, to D.</p></zlib-demo></div>

| Action | Reservoir, high bit shown first | Valid bits | Output |
| --- | --- | --- | --- |
| Before lookup | `1110` | 4 | empty |
| Inspect low two bits: `10` | `1110` | 4 | empty |
| Consume A's one bit | `111` | 3 | `A` |
| Follow root `11`, consume two bits | `1` | 1 | `A` |
| Subtable `1`, consume its one bit | empty | 0 | `AD` |

The first lookup inspects D's first bit as well as A's code. Dropping both would corrupt the next symbol. A short code therefore appears in multiple root slots, and each entry records its actual consumption width.

## Supporting bits and speculative input {#lookahead}

The extra bit seen while decoding A is a small example of lookahead. A faster path can read whole bytes ahead. The symbol's meaning must depend on the prefix that supports that symbol, while the remaining input stays available for later work. Reading a byte is not permission to attribute every bit in it to the output already produced.

On fast-path exit, unused whole bytes are returned to the input cursor; fewer than eight buffered bits remain. If 19 bits are buffered, two whole bytes are returned and three bits retained. Their values and order must still describe the same unconsumed stream. [Slow and fast copies](/sample/decode-copy.html#writeback) follows that accounting in context.

## Execution boundaries {#boundaries}

This walkthrough is a C reading **to confirm** through execution proofs. Each shift needs the selected width's bound; each pull needs a live readable byte and valid pointer advancement. The default LP64 translation uses a 64-bit hold word, but a proof cannot replace source-specific request bounds with that width alone.

The existing [`BitInv` and `stream`](/reference/source/ZlibF/Proof/inflate.c.main.macros.html#L29) make the reservoir-plus-unread-bytes relation explicit. Their role in the broader argument belongs to [the decoder proof chapter](/sample/decode-proof.html). For exact caller behavior on input exhaustion, malformed data, or incomplete work, consult [`inflate`](/reference/functions/inflate.html) and the [stream-decoding reference](/reference/docs/proof/inflate.html). None of those cases is excluded by choosing this small successful trace.
