A compressed file is useful only if someone who did not see the original can recover it. That requirement determines the whole design: how we describe repetition, how descriptions become bits, how the receiver learns their meanings, and how it knows when to stop. We will build a complete small codec before examining the corresponding choices in zlib.

## Make a smaller description that can be undone {#purpose}

Imagine sending `ABABABAB` to another computer. In the byte convention used here, A is 65, or hexadecimal `41`; B is 66, or `42`. The message is eight bytes:

```text
41 42 41 42 41 42 41 42
```

A **byte** has eight binary digits, or bits. It can represent any integer from 0 through 255. Hexadecimal writes a byte with two digits; each digit stands for four bits. Thus `41` means the bits `01000001`, not the two text characters “4” and “1”. A file is a sequence of these byte values. Text, pictures and executable programs all become byte sequences before the compressor handles them. Text also needs a character encoding: UTF-8 may use several bytes for one character. Nothing in our compression method depends on those bytes being printable letters.

Our task is to produce another byte sequence, then recover the original sequence **exactly**, including its length and every zero byte. This is lossless compression. A reader must obtain eight bytes here, not merely something that looks like the same text. Denote the original by `input`, the compressed packet by `packet`, and the reconstructed bytes by `output`. The desired round trip is `decode(encode(input)) = input`.

Copying the input to the packet satisfies recovery, but saves no space. Replacing it with “A and B alternate eight times” saves an explanation to a human, but leaves a computer with new questions. How are A and B represented? Is eight a byte count or a repetition count? Where does the instruction end? What if the original contains the punctuation used by the instruction? A compression format must answer those questions with exact rules, rather than relying on the receiver guessing the writer's intention.

There are two different opportunities. Repeated strings can be replaced with references to earlier strings. Unequally frequent symbols can be assigned unequally long bit codes. We will use both. They solve different problems, so it matters which representation the second one receives.

Nor can any lossless method make every input shorter. There are 256 possible one-byte inputs but only one byte sequence of length zero. Distinct inputs need distinct decodable descriptions. The same counting difficulty persists at larger lengths. A useful compressor exploits patterns in some inputs, accepts overhead in others, and measures the entire transmitted representation.

## Replace repeated bytes with instructions {#lz77}

Start with an easy repetition whose source already exists in full. For `ABCABC`, write the first three bytes directly. At that point the receiver has `ABC`. Instead of sending another `ABC`, send “look back three bytes and copy three bytes”. A byte written directly is called a **literal**. The copy instruction is a **backward reference**, or match. Its **distance** says how far behind the next output position the source begins; its **length** says how many bytes to produce.

```text
Original:      A B C A B C
Instructions:  literal A, literal B, literal C, match(distance 3, length 3)
Reconstructed: A B C → A B C A B C
```

Both numbers are necessary. Distance 3 with length 2 produces `AB`, whereas length 3 with distance 2 produces `BCA`. The distance is relative to the output position when the match begins. It is not an absolute file address and does not point into the compressed packet. Encoder and decoder can place their storage anywhere and still agree on the same sequence of bytes.

This family of techniques is called **LZ77**. The compressor searches earlier original bytes for a useful occurrence and chooses literals or matches. The decoder does not repeat that search. It follows the particular instructions in the packet. Multiple instruction sequences can reconstruct one input. For example, `ABCABC` could also be six literals. This freedom will later allow an encoder to trade search time against compression ratio without changing the decoding rules.

### A copy may create its own later source {#overlap}

Return to `ABABABAB`. After two literals the output is `AB`. Can a match already describe the remaining six bytes? Yes: distance 2, length 6. At first only two source bytes exist, so this requires a precise copying rule. Read one byte at the given distance behind the **current** end of the output, append it, then repeat. The end moves after every append.

| Byte being appended, zero-based | Source position | Byte read | Output after append |
| --- | --- | --- | --- |
| 2 | 0 | A | `ABA` |
| 3 | 1 | B | `ABAB` |
| 4 | 2 | A | `ABABA` |
| 5 | 3 | B | `ABABAB` |
| 6 | 4 | A | `ABABABA` |
| 7 | 5 | B | `ABABABAB` |

The read at position 4 uses a byte produced at position 2 by the same match. This is an **overlapping match**. The instruction means a sequence of dependent byte copies, rather than a snapshot of six pre-existing source bytes. A bulk copy routine with a different overlap rule is not a substitute. Even a snapshot-style temporary buffer would have no six-byte original source to read at the start.

In the following small JavaScript fragment, `output` is a growable array of byte values; `distance` and `length` are the match's two integers. The index is recomputed after every append:

```js
if (distance < 1 || distance > output.length || length < 3)
  throw new Error("invalid match");
for (let i = 0; i < length; i++)
  output.push(output[output.length - distance]);
```

The lower length bound of three is our teaching encoder's rule and also the smallest DEFLATE match. The distance check ensures the first read refers to an existing byte. Subsequent reads remain behind the growing end, including when length exceeds distance. A distance of zero cannot mean “repeat the last byte”: it points at the position that has not been written. Repeating the last byte uses distance 1.

We have therefore replaced eight bytes with three instructions:

```text
literal A, literal B, match(distance 2, length 6)
```

This is a useful intermediate description, but it is not yet a compressed byte sequence. The words “literal” and “match”, the two integers, and the end of the message still need a representation. If each instruction were stored as a large programming-language object, its memory footprint could exceed the original. Saving space requires designing the wire representation too.

### Make a simple encoder choose the instructions {#naive-search}

Use the most direct search first. At the next uncoded input position, try every distance from 1 through that position. For each distance, compare the original bytes from here with bytes that distance earlier, until they differ or the input ends. The comparison may extend past the current starting position: this is precisely the sequential-copy meaning established above. Keep the longest match, choosing the nearest distance on a tie. If its length is at least three, emit the match and advance by its whole length. Otherwise emit one literal and advance one byte. Append END when the input is exhausted.

At position 2 in `ABABABAB`, distance 1 fails immediately because A differs from the preceding B. Distance 2 matches six bytes through the end, so the encoder chooses length 6, distance 2. The encoder has the whole original and can compare these bytes directly; the decoder must generate them in order, as in the earlier table. The teaching scene uses exactly this search and nearest-distance tie rule. It is easy to understand but repeatedly examines many candidates, giving the next article a concrete expensive operation to optimize.

## Give common instructions shorter spellings {#huffman}

Suppose an instruction alphabet contains four symbols that occur with counts 8, 4, 2 and 2. An **alphabet** here means the set of possible symbols, not the English alphabet. For the moment label its members P, Q, R and S. A fixed two-bit code can distinguish them: `00`, `01`, `10`, `11`. Sixteen occurrences then cost 32 bits.

The counts suggest a better allocation. Give P code `0`, Q code `10`, R code `110` and S code `111`. The payload costs

```text
8 × 1 + 4 × 2 + 2 × 3 + 2 × 3 = 28 bits
```

The saving comes from using the shortest word eight times. P and Q are abstract symbols in this calculation; they do not replace the A and B bytes in our running example.

Variable-length words introduce a boundary problem. If one symbol had code `0` and another had code `01`, seeing the first zero would not tell the receiver whether a symbol had ended. Our chosen words avoid this: none is the beginning, or **prefix**, of another. The codes can be drawn as a binary tree: its root is the starting point before any bit is read, zero and one select branches, and leaves name complete symbols. A prefix code can be read from left to right. Stop at a leaf, emit that symbol, and restart at the root. For example, `010110111` splits uniquely into `0 | 10 | 110 | 111`, hence P, Q, R, S. Spaces are for the explanation; the packet needs none.

**Huffman coding** builds such a tree from frequencies. Start with one leaf per used symbol, weighted by its count. Repeatedly join the two lightest trees. To make the teaching encoder deterministic on ties, prefer the tree whose smallest leaf symbol number is smaller. Joining R:2 and S:2 creates a weight-4 subtree. Join that subtree with Q:4 to make weight 8. Join it with P:8 to make the root of weight 16. The resulting depths are 1, 2, 3 and 3. Marking branches with zero and one gives a prefix code of those lengths.

The weighted path length explains the construction's objective. Every time two subtrees are joined, each occurrence below them acquires one more code bit. Choosing light subtrees for that extra cost keeps frequently used leaves nearer the root. For an unconstrained binary prefix code with these frequencies, Huffman's method minimizes the payload's weighted length. It does not minimize the size of every possible complete file: headers, codebook descriptions, match choices and format length limits also cost something.

### The frequencies belong to the representation being encoded {#symbol-frequencies}

LZ77 and Huffman coding exploit different regularities. LZ77 uses order: `ABABABAB` contains a recurring string. Huffman uses unequal symbol counts. Rearranging a sequence without changing its counts leaves its Huffman payload cost unchanged for a given codebook, while it can destroy long matches. Conversely, an input with skewed frequencies can benefit from Huffman coding even when useful long repeats are scarce.

After LZ77, Huffman must describe the instructions we chose, not count the eight original bytes again. Our small format uses literal symbols 0 through 255, one match marker numbered 256, and one end marker numbered 257. **These two marker numbers belong to the teaching format. DEFLATE uses different assignments.** A match marker is followed by its numbers, which our simple format will store directly. The end marker tells the reader to stop decoding instructions.

For the chosen `ABABABAB` instruction sequence, Huffman sees A once, B once, MATCH once and END once. It does not see four A occurrences and four B occurrences. Four equally weighted leaves can all have length two, so the Huffman part gains no frequency advantage here. LZ77 nevertheless reduced the repeated byte sequence to one copy instruction. Longer inputs with many selected matches can make MATCH frequent and give it a shorter code.

This distinction also prevents misleading size comparisons. The three LZ instructions, four Huffman symbols including END, eight reconstructed bytes, and final packet bytes are four different counts. A match's distance and length add payload bits too. We will include all of them in the next calculation.

## Send enough information to reconstruct the codebook {#codebook}

The receiver has never seen the original, its frequencies, or the encoder's tree. “Use Huffman coding” does not tell it which symbol `0` represents. Building a tree privately and then sending only its payload leaves the compression method incomplete.

There are two straightforward solutions. Both ends can agree on a fixed book in advance. Or the packet can carry a description of the book selected for that packet. Our teaching codec takes the second route. It transmits each used symbol's code length, then assigns words by an agreed deterministic rule. The receiver does not need the original frequency counts or the history of tree merges.

The rule is called **canonical assignment**. Sort used symbols first by increasing code length, then by increasing symbol number within a length. Give the first symbol the all-zero word of its length. For each subsequent symbol, increment the previous word as a binary integer. If the new length is longer, append enough zeros to reach it. The bit width remains part of the word; `0` and `00` are not interchangeable spellings.

For lengths P:1, Q:2, R:3, S:3 and that symbol order, the calculation is `0`; increment to 1 and append zero, giving `10`; increment to 3 and append zero, giving `110`; increment once more, giving `111`. Different left/right choices in a tree drawing are irrelevant once both ends use this rule.

For our actual packet, A has symbol number 65, B has 66, MATCH has 256 and END has 257. Each length is two. Sorting gives:

| Symbol meaning | Symbol number | Transmitted length | Reconstructed code |
| --- | --- | --- | --- |
| Literal A | 65 | 2 | `00` |
| Literal B | 66 | 2 | `01` |
| Match follows | 256 | 2 | `10` |
| End of message | 257 | 2 | `11` |

The table in the packet will contain only the numbers and lengths. The final column is reconstructed independently. If a different input uses a literal zero byte, its symbol number is zero and it receives its own entry. No escape character is confused with an original byte: marker numbers lie outside 0 through 255.

Not every list of lengths describes a valid prefix code. Three length-one words cannot fit, since there are only two possible one-bit words. Our decoder checks that lengths are in range and do not overfill the binary tree; this teaching format also requires a complete tree when more than one symbol is present. Equivalently, summing `2^(-length)` gives exactly one. With lengths 2,2,2,2 it gives `4/4 = 1`. A singleton is handled explicitly: an empty input has only END, assigned length one and code `0`. That sole-symbol exception does not require an empty, zero-bit code that would be impossible to locate in the input.

The book is part of the cost. In this intentionally simple representation, each used symbol takes three header bytes. A small custom book may cost more than all its payload savings. Real formats therefore pay considerable attention to how books are described and when a fixed book is preferable.

## Specify the complete packet, not just its payload {#packet}

We can now state a byte-level format that another implementation can decode on its own. It is a **teaching format**, agreed between its encoder and decoder. Its packets are not DEFLATE, zlib or gzip streams, and cannot be passed to zlib's decoder. The scene accepts at most 512 original bytes and rejects a declared output count above 512, so its search and complete trace stay readable.

The packet begins on a byte boundary. It contains the original byte count, the codebook entry count, the entries, and the encoded instructions. Counts and symbol numbers use two-byte unsigned integers in **big-endian** order: first the high byte, then the low byte. Thus eight is `00 08`, 256 is `01 00`, and 257 is `01 01`.

Each book entry contains a two-byte symbol number followed by a one-byte code length. Entries appear in increasing symbol-number order, with each used symbol present once. Lengths range from 1 to 32; END must be present. Reconstructing canonical codes may require sorting the entries by length before symbol number, even though the transmitted entries themselves are sorted only by symbol number.

After the final entry, payload bits begin at the high bit of the next byte. Each next bit fills the next lower position. On crossing a byte boundary, continue at the high bit of a new byte. This **most-significant-bit-first** convention applies to both Huffman words and the match numbers in our teaching format. There is no alignment inserted between instructions or before a match number.

When a decoded symbol is 0 through 255, append that literal byte and read the next Huffman symbol. When it is MATCH, read exactly 16 bits as the unsigned distance, then exactly 16 bits as the unsigned length; these numbers are not Huffman symbols. The next Huffman word begins immediately after those 32 bits. Require distance at least 1 and no greater than the output length already available, and length at least 3. Stop only on END. At that point the output length must equal the count in the header, and all remaining bits in the last byte must be zero padding. There must be fewer than eight padding bits and no extra bytes. A truncated code, truncated number, missing END, bad book, impossible distance or excessive output is an error.

The original byte count is an extra boundary check, not a substitute for END. Reaching eight output bytes and then silently ignoring more instructions would accept an invalid packet. END determines the end of the encoded instruction sequence; the count checks its expansion; padding converts the final bits into whole bytes. These are different jobs.

### Serialize the eight-byte example {#packet-example}

The four entries above take twelve bytes. Including the four-byte prefix, the header is:

```text
00 08 | 00 04 | 00 41 02 | 00 42 02 | 01 00 02 | 01 01 02
8 bytes 4 entries   A:2        B:2       MATCH:2      END:2
```

The payload's structure is now completely determined. Write A's `00`, B's `01`, MATCH's `10`, distance 2 in sixteen bits, length 6 in sixteen bits, then END's `11`:

```text
00 | 01 | 10 | 0000000000000010 | 0000000000000110 | 11
```

There are `2 + 2 + 2 + 16 + 16 + 2 = 40` bits, exactly five bytes. Grouping the same bits by eights, without adding separators or alignment, gives:

```text
00011000 00000000 00001000 00000000 00011011
   18       00       08       00       1b
```

The complete packet is therefore 21 bytes:

```text
00 08 00 04 00 41 02 00 42 02 01 00 02 01 01 02 18 00 08 00 1b
```

Eight input bytes became 21 packet bytes. That is an honest outcome. A compact instruction sequence alone did not repay this format's explicit book and wide numbers. The purpose of this first construction is to make every dependency visible. Decoding remains well-defined even when the representation is larger. Compression ratio will become a design question once we can account for the whole file.

## Decode using only the packet {#decode}

Put the original input, frequency counts and selected instructions aside. Give a fresh receiver only those 21 bytes and the rules above. It first obtains expected output length 8 and book count 4, then reads four entries. Their equal two-bit lengths and symbol order reconstruct `00→A`, `01→B`, `10→MATCH`, `11→END`.

Start the payload with an empty output and its bit cursor at zero. The cursor counts payload bits already consumed; it is not an output position. Huffman decoding consumes only the bits needed to reach a leaf. A match then switches temporarily to fixed-width integer reading before returning to the same Huffman root.

| Step | Bits consumed by this step | Payload cursor afterwards | Action | Output |
| --- | --- | --- | --- | --- |
| 1 | `00` | 2 | Append literal A | `A` |
| 2 | `01` | 4 | Append literal B | `AB` |
| 3 | `10`, then 16 distance bits and 16 length bits | 38 | Copy 6 bytes, distance 2 | `ABABABAB` |
| 4 | `11` | 40 | Read END, check count and padding | `ABABABAB` |

At step 3 the numeric reads cross byte boundaries. Reading “the next two bytes” would be wrong: the distance begins six bits into the payload, not at a byte boundary. The bit reader must preserve the cursor while collecting sixteen bits. The received number is still 2; its byte-aligned hexadecimal spelling `00 02` was a way to explain its value, not a license to skip to the next byte.

The match expands with exactly the six dependent copies from the earlier table. The count becomes eight, but the receiver still reads END. The cursor then equals 40; no padding bits or bytes remain. The receiver accepts and returns the reconstructed eight bytes. At no step did it ask the encoder for a tree or consult the original to choose a match.

One way to organize this decoder is the following pseudocode. `readSymbol` follows canonical-code branches from a fresh root using the current bit cursor. `readBits(16)` reads an unsigned integer in the stated bit order. Header parsing constructs the book before this loop; finishing checks END's position and the permitted zero padding after it.

```text
output = []
repeat:
    symbol = readSymbol(book)
    if symbol == END: break
    if symbol < 256: append symbol to output
    else:
        distance = readBits(16)
        length = readBits(16)
        check 1 <= distance <= output.length and length >= 3
        repeat length times: append output[output.length - distance]
    check output.length <= expectedLength
check output.length == expectedLength
check only zero padding to the next byte remains
```

Every read must also reject a missing bit, and the book has already excluded symbol values other than literals, MATCH and END. The code is short because the format has done the hard work of removing ambiguity: the decoded marker determines what to parse next, prefix codes determine symbol boundaries, fixed widths determine number boundaries, and END determines message completion.

### Change the input and inspect every representation {#codec-scene}

The following scene runs this independent teaching encoder and a separate decoder that receives only the serialized packet. An **instruction trace** lists literals and matches in their original order. A **codebook** shows the transmitted lengths and reconstructed words. A **packet view** shows the bytes actually handed to the decoder. A **decode trace** shows how its bit cursor and reconstructed output advance. “Encode and inspect from start” rebuilds these views from the editable input. “Next step” follows the instructions, book, packet and receiver writes in order; “Back” or the position slider revisits an earlier step of that completed run.

Start with `ABABABAB`, then try `ABCABC` to compare a non-overlapping match, or `AAAAAAAA` to see distance 1. Hexadecimal input allows any byte value; each pair of digits supplies one byte. Empty input still needs a book containing END and a payload containing its one-bit code. Try unrelated bytes too: the overhead remains even when no useful match exists.

<div class="zl-demo-mount"><zlib-demo kind="minimal-codec"><p>For input ABABABAB, the teaching encoder chooses literal A, literal B and match(distance 2, length 6). Its canonical book is A=00, B=01, MATCH=10, END=11. The 21 packet bytes are 00 08 00 04 00 41 02 00 42 02 01 00 02 01 01 02 18 00 08 00 1b. A receiver reconstructs the book from the four transmitted lengths, reads the two literals and the match's two 16-bit numbers, produces ABABABAB by sequential copying, then consumes END at payload bit 40. These bytes use the teaching format, not DEFLATE.</p></zlib-demo></div>

The scene closes the basic codec: original bytes become instructions, instructions become an independently decodable packet, and that packet becomes the original bytes again. It is not necessary to stream data, use a file API or add a checksum to understand this complete transformation. Those features solve additional practical problems; none supplies a missing codebook to the construction above.

## Map the construction to actual DEFLATE {#deflate}

zlib is a library that implements compression and decompression. Its central compressed-data format is **DEFLATE**. In zlib's naming, `deflate` is the compressor and `inflate` is the decoder. DEFLATE combines LZ77-style matches with Huffman coding, but uses a more compact and precisely standardized representation than our teaching packet. We can now explain the differences in terms of objects whose purposes are already clear.

### Two alphabets encode a match's numbers {#deflate-alphabets}

DEFLATE does not send a generic MATCH marker followed by two sixteen-bit numbers. Its main **literal/length alphabet** combines byte values, end-of-block and length groups. Symbols 0–255 are literals, 256 is end-of-block, and 257–285 describe lengths from 3 to 258. Thus our teaching symbol 256 means MATCH, whereas DEFLATE symbol 256 means end-of-block. Symbol numbers must always be read with their format's alphabet.

A length symbol selects a base length and the number of following raw **extra bits**. Add the extra-bit value to that base. Length 6 is exactly symbol 260 and needs no extra bits. Lengths 11–12 share symbol 265: base 11 plus one extra bit distinguishes 11 from 12. A length of 12 is therefore symbol 265 followed by extra-bit value 1.

Once a length has been decoded, the next Huffman symbol comes from a different **distance alphabet**. Valid distance symbols 0–29 describe distances 1–32768 through the same base-plus-extra-bits idea. Distance symbol 1 means exactly 2. Distance symbol 4 means base 5 plus one extra bit, hence distance 5 or 6. A match of length 12 and distance 6 becomes length symbol 265, length extra value 1, distance symbol 4, distance extra value 1. Then decoding returns to the literal/length alphabet.

Separate books let the encoder adapt to different distributions of length groups and distance groups. They also make the parse unambiguous: the literal/length symbol tells the reader whether to append a byte, end the block, or read the remainder of a match. The base and extra-bit tables are format rules, known in advance; they are not inferred from frequencies. The selected source's [length and distance tables in `inftrees.c`](https://github.com/madler/zlib/blob/757f0527154291bcf6bfbd6396ecde6bedd2db95/inftrees.c#L70-L86) make those groups concrete.

The encoder's [`compress_block`](https://github.com/madler/zlib/blob/757f0527154291bcf6bfbd6396ecde6bedd2db95/trees.c#L900-L949) emits that exact order: literal or length code, optional length extras, distance code, optional distance extras, and eventually end-of-block. The numbers in its temporary records have already been selected by the match search; they are not the wire encoding.

### The block says where its codebooks come from {#deflate-blocks}

DEFLATE divides its instruction stream into **blocks**. Each starts with one bit saying whether this is the final block, followed by two bits identifying its representation. A block boundary can change codebooks; it does not automatically erase the previously reconstructed bytes available to matches. The decoder finishes the stream only after the final block has ended.

A **fixed Huffman block** uses code lengths prescribed by the format. Literal/length symbols 0–143 have length 8; 144–255 have length 9; 256–279 have length 7; 280–287 have length 8. Canonical assignment over those numbered symbols gives both ends the same words without a book description. Symbols 286 and 287 have positions in that fixed book but cannot encode valid lengths. The fixed distance book gives all 32 positions five-bit words; distance symbols 30 and 31 are reserved and invalid as match distances.

A **dynamic Huffman block** describes its own literal/length and distance books before the payload. It still transmits lengths and reconstructs canonical words. To reduce description overhead, it also compresses the length sequence. This adds one more, small alphabet whose symbols describe lengths, rather than original bytes. The decoder obtains this description alphabet first, then uses it to recover the two data alphabets. There is no circular dependency.

Concretely, after the three-bit block header, dynamic coding reads five bits plus 257 for the literal/length count, five bits plus 1 for the distance count, and four bits plus 4 for the number of description-alphabet lengths that follow. The ordinary valid data alphabets need at most 286 literal/length positions and 30 distance positions. The description alphabet has 19 numbered symbols. Each supplied length occupies three raw bits, in this prescribed symbol order:

```text
16, 17, 18, 0, 8, 7, 9, 6, 10, 5, 11, 4, 12, 3, 13, 2, 14, 1, 15
```

Positions beyond the supplied count have length zero, meaning absent. Canonical assignment now constructs the description book. Using it, decode exactly the announced literal/length count plus distance count of lengths. Description symbols 0–15 state a length directly; 16 repeats the preceding length 3–6 times using two extra bits; 17 inserts 3–10 zeros using three extra bits; 18 inserts 11–138 zeros using seven extra bits. Symbol 16 requires an existing previous length. A run must not exceed the announced total. Split the resulting sequence at the literal/length count and reconstruct the two canonical data books. Data-code lengths are at most 15; end-of-block must have a code. Only then can payload decoding begin. The [`TABLE`, `LENLENS` and `CODELENS` paths in `inflate.c`](https://github.com/madler/zlib/blob/757f0527154291bcf6bfbd6396ecde6bedd2db95/inflate.c#L792-L926) perform these stages in that dependency order.

The third valid form is a **stored block**. It skips to the next byte boundary, reads a sixteen-bit length and its sixteen-bit one's complement: every length bit inverted, equivalently `65535 − length`. The receiver checks that the two fields agree before copying that many original bytes directly. This redundancy rejects inconsistent length fields; it does not validate the copied content. Those length fields use low byte first. This form carries no Huffman payload and needs no end-of-block symbol: its byte count locates the block's end. Block type 3 is reserved. These choices ensure that data which would gain little from Huffman coding can still have a straightforward representation.

### Decode the same eight bytes in a real fixed block {#fixed-example}

Use the same selected instructions: A, B, length 6/distance 2. A final fixed block has the following fields. The code words shown are read in their Huffman order, with the first character read first:

| Field | Meaning | Bit sequence in reading order |
| --- | --- | --- |
| Header | Final flag 1, fixed type 1 | `1`, then `1 0` |
| Literal/length word | Literal A, symbol 65 | `01110001` |
| Literal/length word | Literal B, symbol 66 | `01110010` |
| Literal/length word | Length 6, symbol 260 | `0000100` |
| Distance word | Distance 2, symbol 1 | `00001` |
| Literal/length word | End-of-block, symbol 256 | `0000000` |

The total is `3 + 8 + 8 + 7 + 5 + 7 = 38` meaningful bits. DEFLATE fills each byte from its **low** bit upward, unlike our teaching packet. Multi-bit numeric fields place their low bit first, whereas Huffman code words are encountered in the codeword order shown above. This distinction is why reversing every printed binary field indiscriminately gives the wrong bytes. Place the listed bits successively into low-to-high byte positions, then add two zero alignment bits at the end. The resulting raw DEFLATE bytes are:

```text
73 74 82 40 00
```

A decoder reads the header and chooses the prescribed fixed books. It reads A and B, obtains length 6 from symbol 260, obtains distance 2 from the distance book, performs the six dependent copies, then reads end-of-block. The final flag says there is no next block. The same reconstruction now comes from a real five-byte DEFLATE stream, with no transmitted custom book. This is one legal selected encoding; it is not a prediction that zlib's ordinary compressor will choose precisely these matches and bytes.

The actual decoder represents copying with moving pointers. In the direct-output case, `put` points at the next output byte, `state->offset` holds the decoded distance, the source begins that distance before `put`, `from` names the current source, and `copy` counts how many bytes this part will append. The core [`inflate.c` copy loop](https://github.com/madler/zlib/blob/757f0527154291bcf6bfbd6396ecde6bedd2db95/inflate.c#L1063-L1075) retains the sequential meaning we derived:

```c
            do {
                *put++ = *from++;
            } while (--copy);
```

Each assignment reads a source byte and then advances both pointers. Source bytes written earlier by that same loop become readable later, just as in the distance-2 table. Efficient decoding must preserve that meaning even when it processes several bytes per iteration.

## Improve the codec, then extend its job {#roadmap}

We now have the complete basic picture. The encoder chooses literals and matches, codes the resulting symbols, supplies or identifies its books, and delimits the encoded message. The decoder reconstructs those books, parses the actual bits, expands matches from its own output, and recognizes completion. Every item is needed before the receiver can work independently.

The next question is efficiency. Searching every earlier position is expensive. Trying more matches can improve the compression ratio while taking more time. A custom book can shorten the payload while making a small block larger overall. A decoder that follows one tree edge per bit is easy to understand but spends work that a lookup table can avoid. The [next article on time, memory and compression ratio](/read/optimizations.html) develops those tradeoffs for both `deflate` and `inflate` from this complete codec.

After those optimizations, [the third article on practical features](/read/features.html) extends the task: accept data in batches, pause and continue with limited output storage, request flush boundaries, reuse a dictionary, and place DEFLATE inside zlib or gzip framing with Adler-32 or CRC-32 checks. Those additions depend on the byte transformation already established here. They let the same compression mechanism serve real applications with different delivery, reuse and integrity requirements.
