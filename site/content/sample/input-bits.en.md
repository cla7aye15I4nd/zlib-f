A decoder must read a stream of bits even though the application supplies whole bytes. A field can end halfway through a byte; the next field starts at the very next bit. The job of the input machinery is to keep those leftover bits and join them to later input without losing, repeating or reversing any of them.

Its input is the previously saved bits plus the caller's unread bytes. Its output is a requested field value and the exact bits still unconsumed. It does not itself produce decompressed bytes. The [algorithm overview](/algorithms/index.html) explains the larger byte → symbol → output route; here we follow its first step.

## Keep the next bits in order {#reservoir}

Suppose the next three bits to read are `0, 1, 1`. A small integer can store them with the next bit in its lowest position: its usual binary spelling is then `110`, or decimal 6. Read this spelling from right to left to recover the stream order. Only these three positions are valid.

Now suppose the next field needs five bits. Three are already available, so the decoder must fetch a byte before reading that field. The new byte belongs *after* the three saved bits, not in their place. This temporary integer is called the **bit reservoir**. In the C implementation, `hold` is its value and `bits` is its valid-bit count. Our starting state is therefore `hold = 6`, `bits = 3`. A normalized reservoir satisfies `hold < 2^bits`; unread bytes logically follow it.

## Refill, with a concrete byte {#refill}

Let the next byte be `0xA5 = 165`. It contributes eight bits, low position first. Appending it above the saved three bits gives:

```text
saved bits in reading order: 0, 1, 1
new byte in reading order:  1, 0, 1, 0, 0, 1, 0, 1
new hold = 6 + (165 << 3) = 1326
new bits = 3 + 8 = 11
```

Nothing has been parsed yet: the same eleven bits have merely moved into one integer. The input cursor advances by one byte, while the next unconsumed bit remains the original `0`.

Here is the actual `PULLBYTE` macro used by `inflate`, from [pinned `inflate.c`, lines 366–372](https://github.com/madler/zlib/blob/757f0527154291bcf6bfbd6396ecde6bedd2db95/inflate.c#L366-L372):

```c
#define PULLBYTE() \
    do { \
        if (have == 0) goto inf_leave; \
        have--; \
        hold += (unsigned long)(*next++) << bits; \
        bits += 8; \
    } while (0)
```

`have` counts readable bytes still offered by the caller; `next` points to the next one. With our byte available, `have--` accounts for its removal, `*next++` reads 165 and advances the cursor, and the shift places it above the three saved bits. With no byte available, the first check leaves before reading. The [translated `PULLBYTE`](/reference/source/ZlibF/Zlib/inflate.c.html#L446) keeps this source order.

`NEEDBITS(n)` repeats the pull until at least `n` bits are buffered. It can pull some bytes and still run out of offered input before reaching `n`. Those bits must survive for the next call; input exhaustion cannot pretend that the field was read or clear the reservoir.

## Read a field, then consume it {#consumption}

Return to the five-bit field. The low five bits of 1326 form decimal 14. Reading this value leaves the reservoir unchanged. Once the parser accepts the field, it removes exactly five bits: `hold` becomes `1326 >> 5 = 41`, and `bits` becomes six. The next field starts with those six saved bits.

In C, `BITS(n)` masks the low `n` positions and `DROPBITS(n)` shifts right and subtracts `n` from the valid count; see [the actual macros, lines 383–391](https://github.com/madler/zlib/blob/757f0527154291bcf6bfbd6396ecde6bedd2db95/inflate.c#L383-L391). The caller must first establish sufficient bits and valid shift widths. Looking at bits is different from consuming them.

This example separates three accounts: bytes pulled from the caller, bits interpreted by the parser, and decompressed bytes produced. Header fields can consume bits without output; an already decoded match can produce output without further input. One cursor cannot represent all three.

## Decode two symbols {#trace}

A **Huffman code** assigns a variable-length bit sequence to each symbol. Use the teaching code `A=0`, `B=10`, `C=110`, `D=111`. Message `AD` arrives as `0 | 111`. Displaying just those four meaningful bits gives `hold = 1110`, `bits = 4`. This is an abstract code example, not a complete DEFLATE block or a four-bit byte refill.

A table can inspect two bits at once. Its **root table** is the first table consulted. Longer codes can lead to a smaller **subtable** for the remaining bits. The [next chapter](/sample/decode-tables.html) constructs these tables; first follow what their consumer needs:

<div class="zl-demo-mount"><zlib-demo kind="lookup"><p>AD arrives as 0,1,1,1. Root index 10 gives A but consumes only one bit. The remaining 111 follows root index 11, then subtable index 1, to D.</p></zlib-demo></div>

| Action | Reservoir, high bit shown first | Valid bits | Output |
| --- | --- | --- | --- |
| Before lookup | `1110` | 4 | empty |
| Inspect low two bits: `10` | `1110` | 4 | empty |
| Consume A's one bit | `111` | 3 | `A` |
| Follow root `11`, consume two bits | `1` | 1 | `A` |
| Subtable `1`, consume its one bit | empty | 0 | `AD` |

The first lookup sees D's first bit as well as A's entire code. Removing both would lose the start of D. Thus a table entry must record actual consumption, which can be shorter than the lookup width.

Ordinary numeric fields arrive least significant bit first. Huffman codewords instead arrive most significant *code* bit first, while byte positions are still read low to high. Codeword `110` therefore occupies the reservoir as integer `011`. The builder arranges its entries for this order; the decoder need not reverse every input byte.

## Read ahead without losing input {#lookahead}

The extra bit inspected for A is **lookahead**: input seen before it is needed. The fast decoder also fetches whole bytes ahead. A symbol depends on the prefix supporting that symbol; fetching a byte does not make every bit in it part of the output already produced.

On fast-path exit, unused whole bytes are returned to the input cursor and fewer than eight buffered bits remain. With 19 buffered bits, two bytes return and three bits remain. Their order must still describe the same unconsumed stream. [Slow and fast copies](/sample/decode-copy.html#writeback) follows this accounting.

The parser also works on local copies of its state. `LOAD` obtains the input/output cursors and saved bits from the stream, and `RESTORE` writes them back at a boundary. Heap fields and locals need not be equal while the body is running. [Stream state](/sample/stream-state.html) follows these boundaries across calls.

## What the proof must preserve {#boundaries}

The invariant to justify is simple to state: the reservoir followed by the unread bytes is exactly the unconsumed input. The existing [`BitInv` and `stream`](/reference/source/ZlibF/Proof/inflate.c.main.macros.html#L29) formalize that relation, along with readable storage and normalization. The [decoder proof chapter](/sample/decode-proof.html) explains how it connects to tables and output.

This walkthrough is a C reading **to confirm** through execution proofs. Each pull needs a live readable byte and valid pointer advancement; each shift needs the selected width's bound. The default LP64 translation uses a 64-bit hold word, which does not replace source-specific request bounds.

For exact caller behavior on input exhaustion, malformed data and incomplete work, consult [`inflate`](/reference/functions/inflate.html) and the [stream-decoding reference](/reference/docs/proof/inflate.html). These cases remain in scope beyond our small successful trace.
