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

zlib is a library that implements compression and decompression. Its central compressed-data format is **DEFLATE**. In zlib's naming, `deflate` is the compressor and `inflate` is the decoder. The original is still a byte sequence. Match search still turns it into an ordered sequence of literals and backward references. The next change concerns how that sequence is represented on the wire.

DEFLATE divides a stream into **blocks**, each of which selects the representation rules for its data. Start with one Huffman-coded block: its pair of books stays unchanged while we read that block. We will later examine its header and the other block forms.

Keep our example in view:

```text
Original:      A B A B A B A B
Instructions:  literal A, literal B, match(length 6, distance 2)
```

Our teaching packet gives the match a generic MATCH word, followed by two wide integers. DEFLATE makes that representation more compact. It gives lengths and distances their own grouped representations, and uses Huffman coding for both groups. We will first follow that change with the books already drawn, then explain how the receiver obtains those books from a block.

### Two alphabets encode a match's numbers {#deflate-alphabets}

Start with the objects being encoded. Each literal contributes a byte value. Each match contributes **two numbers with different jobs**: how many bytes to produce, and how far back to find their source. An end marker finishes the block. The order of these objects is already fixed by the instruction sequence; Huffman coding only gives them shorter bit spellings.

DEFLATE organizes their symbols into two alphabets. The **literal/length alphabet** contains literal bytes, end-of-block and length groups. The **distance alphabet** contains distance groups. Each alphabet has its own independent Huffman tree. Listing each leaf's symbol and its root-to-leaf bit path gives that tree's codebook. The tables here list symbols and code words; the fast decoder lookup tables in the next article use arrays to accelerate walking such a tree.

Why put literals and lengths together? At each instruction boundary, the receiver must choose between appending one byte and executing a match. A length symbol simultaneously announces a match and supplies its length group, taking over the teaching format's generic MATCH marker. A distance is needed only after a length, so it can use a separate tree. Huffman coding permits many alphabet designs; this pair is DEFLATE's chosen parsing organization.

When constructing a dynamic block, the encoder counts occurrences in these two alphabets separately and constructs a book for each collection.

In the eight-byte example, the first alphabet sees four occurrences: literal A, literal B, length 6 and end-of-block. The second sees one occurrence: distance 2. Every match contributes one length symbol to the first collection and one distance symbol to the second. Literals and end-of-block contribute only to the first. For a longer input, repeated distance-1 matches may make one distance symbol very common while their lengths vary; the two collections then have different distributions.

<figure class="df-figure">
<div class="df-flow">
<div class="df-card"><strong>Chosen LZ77 records</strong><p>A · B · match(6, 2)</p><small>The records retain their order.</small></div>
<span class="df-arrow" aria-hidden="true">→</span>
<div class="df-card"><strong>Count symbols by role</strong><p>Literal/length: A, B, length 6, end</p><p>Distance: distance 2</p></div>
<span class="df-arrow" aria-hidden="true">→</span>
<div class="df-card"><strong>Write one payload</strong><p>A code · B code · length code · distance code · end code</p><small>Two books share one advancing bit cursor.</small></div>
</div>
<figcaption class="df-caption">The encoder adds one end-of-block marker. Separate symbol collections choose the code words. The original instruction order determines where those words appear in the single transmitted bit sequence.</figcaption>
</figure>

The symbol numbers make the roles concrete. In the literal/length alphabet, 0–255 mean literal bytes, 256 means end-of-block, and 257–285 select length groups covering lengths 3–258. In the distance alphabet, 0–29 select distance groups covering distances 1–32768. A number therefore needs its alphabet as well as its value. Literal/length symbol 65 means byte A; distance symbol 1 means distance 2. The latter does not append a byte with value 1.

| Instruction component | Alphabet used | Symbol in this example |
| --- | --- | --- |
| Append A | Literal/length | 65 |
| Append B | Literal/length | 66 |
| Produce 6 bytes by copying | Literal/length | 260 |
| Start the copy 2 bytes back | Distance | 1 |
| Finish the block | Literal/length | 256 |

For the moment, give both ends the following two valid books. The four used literal/length symbols have two-bit words in symbol order. The distance book has one used symbol, assigned the one-bit word `0`. A one-symbol distance book still consumes one bit; it does not turn into a zero-bit instruction. We choose these valid lengths to keep both trees small and the format visible; the next article examines zlib's constructor choices and their costs. We will construct exactly these books from a dynamic header below.

<figure class="df-figure">
<div class="df-two-col">
<div class="df-card"><strong>Literal/length tree</strong><div class="df-tree-scroll" tabindex="0"><svg class="df-tree" viewBox="0 0 320 205" width="320" height="205" role="img" aria-label="Independent literal/length tree: 00 reaches 65, 01 reaches 66, 10 reaches 256 and 11 reaches 260."><path d="M160,47 L80,76"/><text x="111" y="55">0</text><path d="M160,47 L240,76"/><text x="210" y="55">1</text><path d="M80,112 L36,146"/><text x="49" y="121">0</text><path d="M80,112 L124,146"/><text x="112" y="121">1</text><path d="M240,112 L196,146"/><text x="209" y="121">0</text><path d="M240,112 L284,146"/><text x="272" y="121">1</text><g><circle cx="160" cy="28" r="18"/><text x="160" y="32">root</text></g><g><circle cx="80" cy="94" r="18"/><text x="80" y="98">·</text></g><g><circle cx="240" cy="94" r="18"/><text x="240" y="98">·</text></g><g><circle cx="36" cy="164" r="18"/><text x="36" y="168">65</text></g><g><circle cx="124" cy="164" r="18"/><text x="124" y="168">66</text></g><g><circle cx="196" cy="164" r="18"/><text x="196" y="168">256</text></g><g><circle cx="284" cy="164" r="18"/><text x="284" y="168">260</text></g></svg></div><p>Leaf IDs mean A, B, end and length 6, as in the table above.</p></div>
<div class="df-card"><strong>Distance tree</strong><div class="df-tree-scroll" tabindex="0"><svg class="df-tree" viewBox="0 0 220 205" width="220" height="205" role="img" aria-label="Independent distance tree: 0 reaches symbol 1; the 1 branch is unused."><path d="M110,47 L60,146"/><text x="76" y="99">0</text><path d="M110,47 L160,146"/><text x="145" y="99">1</text><g><circle cx="110" cy="28" r="18"/><text x="110" y="32">root</text></g><g><circle cx="60" cy="164" r="18"/><text x="60" y="168">1</text></g><g class="df-tree-unused"><circle cx="160" cy="164" r="18"/><text x="160" y="168">×</text></g></svg></div><p>Leaf ID 1 means distance 2. × is unassigned. Enter this tree only after a length.</p></div>
</div>
<figcaption class="df-caption">Each tree has its own root. Follow edge bits from a root to a leaf to obtain that symbol’s code word. The literal/length tree chooses the next instruction; the distance tree completes a match that has already begun.</figcaption>
</figure>

With those books, the payload is only nine bits:

```text
00   | 01   | 11        | 0          | 10
A      B      length 6    distance 2   end
```

There is one physical payload and one cursor through it. Begin at the literal/length root and read `00`: append A. Restart at that same root and read `01`: append B. Read `11` there: this announces a length, so remember length 6 and enter the distance root. Read `0` there: remember distance 2. Now both numbers are available, so perform the six sequential copies. Return to the literal/length root and read `10`: finish the block.

The decoder knows the book **before** it reads a word. Its current task chooses the root. Decoding a length changes that task to “read a distance”; completing the match changes it back to “read the next literal, length or end”. No book identifier is inserted before each word. The grammar supplies that information. The distance word `0` can consequently coexist with literal/length words beginning in zero.

### Groups shorten the numbers; extra bits finish them {#deflate-extra-bits}

The example's length and distance each have a group of their own, so their Huffman symbols already determine the complete numbers. Larger values often share a group. That keeps the alphabets much smaller than one symbol per possible length or distance.

A group specifies two fixed facts: a **base value**, and a count of raw **extra bits**. The receiver decodes a Huffman symbol to choose the group, reads exactly that many following bits as an unsigned number, and adds it to the base. The grouping rules are fixed by DEFLATE. The Huffman words used to select the groups may change from block to block.

| Kind | Symbol | Base | Extra-bit count | Values represented |
| --- | --- | --- | --- | --- |
| Length | 260 | 6 | 0 | 6 |
| Length | 265 | 11 | 1 | 11–12 |
| Length | 266 | 13 | 1 | 13–14 |
| Distance | 1 | 2 | 0 | 2 |
| Distance | 4 | 5 | 1 | 5–6 |
| Distance | 5 | 7 | 1 | 7–8 |

Consider a receiver that has already emitted `ABCDEF`, and is now asked to copy length 12 at distance 6. The instruction produces `ABCDEFABCDEF`, leaving the full output `ABCDEFABCDEFABCDEF`. Representing that instruction proceeds in four stages:

1. Decode literal/length symbol 265. Its group starts at length 11 and requires one extra bit.
2. Read that raw bit as value 1. The length becomes `11 + 1 = 12`.
3. Decode distance symbol 4. Its group starts at distance 5 and requires one extra bit.
4. Read that raw bit as value 1. The distance becomes `5 + 1 = 6`.

The two extra bits go directly to the number reader. They do not traverse either Huffman tree. Once the four stages have supplied both numbers, the decoder copies twelve bytes and returns to the literal/length root. For a group requiring zero extra bits, the number reader consumes nothing and contributes zero.

Keep two kinds of “table” distinct here. A **Huffman book** maps a variable-length code word to a symbol. A **group lookup** maps that symbol to a base and an extra-bit count. First the book answers “which symbol?”, then the format's fixed group rules answer “which number?”. The selected source's [base and extra-bit arrays in `inftrees.c`](https://github.com/madler/zlib/blob/757f0527154291bcf6bfbd6396ecde6bedd2db95/inftrees.c#L70-L86) implement the second mapping; they do not describe the current Huffman tree.

The next scene keeps the two books visible alongside the one bit cursor. Start with the eight-byte example, then select the length-12/distance-6 match. Advance through a literal/length word, raw length extras, a distance word and raw distance extras. The active root and highlighted field show why each bit is interpreted that way. The second example begins with `ABCDEF` already available and supplies a different small pair of books: length symbol 265 replaces 260, and distance symbol 4 replaces 1. It isolates the match rather than transmitting that prefix again.

<div class="zl-demo-mount"><zlib-demo kind="deflate-alphabets"><p>DEFLATE has one payload cursor and two Huffman books. For A, B, length 6/distance 2 and end-of-block, the literal/length book supplies A, B, length 6 and end; the distance book supplies distance 2. After a length, decode its raw extra bits, then one distance symbol and its raw extra bits, copy the indicated bytes and return to the literal/length book. For length 12/distance 6, symbol 265 plus raw value 1 gives length 12; distance symbol 4 plus raw value 1 gives distance 6. The already available ABCDEF is extended by twelve bytes to ABCDEFABCDEFABCDEF.</p></zlib-demo></div>

This is also the encoder's order. Its selected match already contains a length and distance. [`compress_block`](https://github.com/madler/zlib/blob/757f0527154291bcf6bfbd6396ecde6bedd2db95/trees.c#L900-L949) converts them into the length symbol and extras, followed by the distance symbol and extras. A decoder reverses those representation steps and executes the match. It does not repeat the encoder's match search.

### The block says where its codebooks come from {#deflate-blocks}

We have used two books to read a payload. The receiver must also know which books to use. DEFLATE supplies that information at a **block** boundary. A stream is one or more consecutive blocks; each block announces how its following data is represented.

The first bit says whether this is the final block. The next two bits identify the block form. A fixed Huffman block selects two prescribed books. A dynamic Huffman block first transmits descriptions from which to reconstruct two books. A stored block supplies raw bytes instead. The numeric block-form values are 0 for stored, 1 for fixed, 2 for dynamic, and 3 for reserved. The reserved form causes a decoding error.

<figure class="df-figure">
<div class="df-flow">
<div class="df-card"><strong>Read three header bits</strong><p>Final flag + block form</p></div>
<span class="df-arrow" aria-hidden="true">→</span>
<div class="df-card"><strong>Obtain this block's representation</strong><p>Fixed: prescribed books</p><p>Dynamic: reconstruct books</p><p>Stored: counted raw bytes</p></div>
<span class="df-arrow" aria-hidden="true">→</span>
<div class="df-card"><strong>Finish this block</strong><p>Append reconstructed bytes to the same output.</p><small>Read another header unless the final flag was set.</small></div>
</div>
<figcaption class="df-caption">A block boundary changes how subsequent input bits are decoded. Previously reconstructed output remains available as the source of later matches.</figcaption>
</figure>

There are therefore two boundaries to recognize. End-of-block finishes the current Huffman instruction sequence. The final flag says whether to read another block after it. An earlier block can provide the bytes used by a later block's match, even if those blocks use different books. The books interpret compressed bits; the retained output supplies match bytes. Those two roles have different lifetimes.

### Fixed blocks obtain both books without a description {#deflate-fixed-books}

A fixed block uses code lengths built into the format. The literal/length tree is constructed from these four ranges:

| Symbol positions | Meaning of the positions | Code length |
| --- | --- | --- |
| 0–143 | First literal values | 8 |
| 144–255 | Remaining literal values | 9 |
| 256–279 | End-of-block and some length groups | 7 |
| 280–287 | Remaining length positions, including reserved 286–287 | 8 |

Apply the canonical assignment from the earlier section to all these positions. Both ends obtain the same tree. For example A, symbol 65, receives `01110001`; B receives `01110010`; end-of-block, symbol 256, receives `0000000`; length-6 symbol 260 receives `0000100`. Symbols 286 and 287 take up positions in the prescribed tree but are invalid as lengths.

The fixed distance tree has 32 positions, each with length 5. Its canonical words are the five-bit symbol numbers: distance symbol 1 has `00001`, and symbol 4 has `00100`. Positions 30 and 31 are reserved and cannot supply a match distance. A fixed block's three-bit header is enough to select both trees; it carries no code-length list.

Notice how these fixed words differ from the earlier four-leaf example. The **meaning** of literal/length symbol 260 is still length 6. Its **spelling** is now `0000100`, rather than `11`, because the block selected a different book. Symbol meanings and code words are separate layers.

### Dynamic blocks first reconstruct their two books {#deflate-dynamic-books}

A dynamic block can choose books suited to its data, so its receiver needs their descriptions. Choose the final flag 1 and dynamic block-form value 2. We will construct the exact pair used in the nine-bit example: A, B, end and length 6 each have code length 2; the only used distance symbol has code length 1.

The receiver needs to know which length belongs to which symbol. DEFLATE sends a **code-length array indexed by symbol number**. Every position through the declared last position appears, including unused symbols with length zero. Four used leaves therefore do not mean four array positions:

```text
Literal/length positions: 0 … 64 | 65 | 66 | 67 … 255 | 256 | 257 … 259 | 260
Code lengths:            0 …  0 |  2 |  2 |  0 …   0 |   2 |   0 …   0 |   2

Distance positions:      0 | 1
Code lengths:            0 | 1
```

The highest needed literal/length symbol is 260, so that array has 261 positions, numbered 0–260. The highest needed distance symbol is 1, so its array has two positions. After reconstructing the lengths, canonical assignment over each array separately gives A=`00`, B=`01`, end=`10`, length 6=`11`, and distance 2=`0`.

How should the block transmit 263 lengths without spending a whole byte on every zero? It joins the two arrays into one length sequence, then compresses that sequence. This introduces a small **description alphabet** whose values describe code lengths and repeated lengths. Its Huffman tree is a third tree, used only while reading the header. Its decoded numbers fill the two data arrays; they do not append original bytes.

The extra tree must itself have a description that can be read without already knowing that tree. DEFLATE does this by transmitting its small set of code lengths directly as three-bit integers. The dependency now has a starting point:

<figure class="df-figure">
<div class="df-flow">
<div class="df-card"><strong>Raw three-bit lengths</strong><p>Read without any Huffman tree.</p></div>
<span class="df-arrow" aria-hidden="true">→</span>
<div class="df-card"><strong>Description tree</strong><p>Decode and expand 263 data-code lengths.</p></div>
<span class="df-arrow" aria-hidden="true">→</span>
<div class="df-card"><strong>Two data trees</strong><p>Keep the first 261 lengths, then build both trees separately.</p></div>
<span class="df-arrow" aria-hidden="true">→</span>
<div class="df-card"><strong>Original instructions</strong><p>Use the literal/length and distance books to decode the payload.</p></div>
</div>
<figcaption class="df-caption">The header's temporary tree describes two later trees. Raw lengths establish it first, so no tree is required to describe itself.</figcaption>
</figure>

The description alphabet has 19 symbols. Symbols 0–15 mean “append this one code length”. Symbol 16 repeats the preceding length 3–6 times, with two raw extra bits selecting the count. Symbol 17 inserts 3–10 zeros, with three extra bits. Symbol 18 inserts 11–138 zeros, with seven extra bits. The receiver keeps appending until it has exactly the declared combined number of lengths. A repeat can cross the eventual split between the two arrays; that split is applied after expansion.

For our example, choose this valid description book:

| Description symbol | Its code word | What decoding it does |
| --- | --- | --- |
| 2 | `0` | Append one code length equal to 2 |
| 18 | `10` | Read seven extra bits; append 11 plus their value zeros |
| 17 | `110` | Read three extra bits; append 3 plus their value zeros |
| 0 | `1110` | Append one zero length |
| 1 | `1111` | Append one code length equal to 1 |

Description symbol 2 is itself encoded with **one bit**, `0`, and it writes the number **2** into a data-code-length array. The description symbol, its Huffman code length, its Huffman bits and the data-code length it produces are four different objects. Keeping them visible prevents the phrase “encode the code lengths” from hiding a layer.

The following ten description symbols recover all 263 positions. The raw extra values are numbers; the next section explains how numbers and Huffman words are placed into bytes.

| Description symbol | Raw extra value | Lengths appended | Count after this step |
| --- | --- | --- | --- |
| 18 | 54 | 65 zeros | 65 |
| 2 | None | One 2: literal A's length | 66 |
| 2 | None | One 2: literal B's length | 67 |
| 18 | 127 | 138 zeros | 205 |
| 18 | 40 | 51 zeros | 256 |
| 2 | None | One 2: end-of-block's length | 257 |
| 17 | 0 | 3 zeros | 260 |
| 2 | None | One 2: length-6 symbol's length | 261 |
| 0 | None | One zero: distance symbol 0 is unused | 262 |
| 1 | None | One 1: distance symbol 1's length | 263 |

At count 261, the literal/length array is complete. The last two entries are the distance array. The receiver constructs the two canonical books and can now decode `00 | 01 | 11 | 0 | 10` into the eight original bytes. The header needs code lengths, rather than the original frequency counts. The chosen instructions travel in the following payload, without a second copy of their record array.

To finish the header description itself, the receiver needs its counts and the small description book. After the three block-header bits, DEFLATE provides them in this order:

| Field | How to read it | Our example |
| --- | --- | --- |
| Literal/length position count | Five-bit value + 257 | `4 + 257 = 261` |
| Distance position count | Five-bit value + 1 | `1 + 1 = 2` |
| Description lengths provided | Four-bit value + 4 | `14 + 4 = 18` |
| Those description-code lengths | Three raw bits each, in the prescribed symbol order | 18 lengths, shown below |

The lower bound 257 includes the end-of-block position 256. The description alphabet's order puts useful repeat symbols early:

```text
Symbol order: 16,17,18, 0,8,7,9,6,10,5,11,4,12,3,13,2,14,1,15
Our lengths:  0, 3, 2, 4,0,0,0,0, 0,0, 0,0, 0,0, 0,1, 0,4
```

Only the first 18 lengths are supplied here. The omitted last position, symbol 15, gets length zero. Canonical assignment now reconstructs the five-row description book above, after which its symbols expand the 263 lengths. The field for distance positions can express 1–32 positions, while distance symbols 30–31 remain reserved. The selected default zlib decoder rejects counts above 30; our two-position example fits its ordinary path. The actual [`TABLE`, `LENLENS` and `CODELENS` stages in `inflate.c`](https://github.com/madler/zlib/blob/757f0527154291bcf6bfbd6396ecde6bedd2db95/inflate.c#L792-L926) read the counts, construct the description book and recover the two data books in exactly this dependency order.

The scene below walks that whole construction. Advance until the description tree appears, then expand the zero runs and watch the array fill. The split at 261 gives the two payload books. Only after that step does the same cursor begin interpreting the nine payload bits.

<div class="zl-demo-mount"><zlib-demo kind="deflate-header"><p>This dynamic block announces 261 literal/length positions and two distance positions. Raw three-bit code lengths first construct a temporary description tree: symbol 2 has code 0, 18 has 10, 17 has 110, 0 has 1110, and 1 has 1111. Its ten symbols expand to 263 lengths: the literal/length array has length 2 at symbols 65, 66, 256 and 260; the distance array is [0,1]. Canonical assignment gives A=00, B=01, end=10, length 6=11 and distance 2=0. The payload 00|01|11|0|10 therefore reconstructs ABABABAB. The complete 16-byte stream is 25 c1 31 11 00 00 00 40 c0 6c f4 0f 65 70 8f 0b.</p></zlib-demo></div>

This chosen header takes 116 bits: 3 block bits, 14 count bits, 54 raw description-length bits and 45 bits for the compressed 263-length sequence. Add the nine payload bits and three final zero padding bits to obtain 16 bytes:

```text
25 c1 31 11 00 00 00 40 c0 6c f4 0f 65 70 8f 0b
```

The smaller payload has a larger description. The complete dynamic representation here exceeds the five-byte fixed block below. Both decode to the same original. Choosing between complete block costs, rather than just payload lengths, will be one of the next article's optimization problems.

Header parsing also checks the representation before using it: the supplied code lengths must form permitted prefix codes, repeats must stay within the declared total, and symbol 16 needs an earlier length to repeat. The literal/length book must include end-of-block, and data-code lengths may not exceed 15. During payload decoding, a reserved symbol, a missing required bit or an unavailable match source is an error. The receiver does not repair such a stream by guessing a book or a source byte.

### Stored blocks represent bytes directly {#deflate-stored}

Some data would pay more for coding than it saves. A stored block gives that data a direct representation. After its three-bit block header, skip to the next byte boundary. Read a sixteen-bit byte count and another sixteen-bit field with every bit of that count inverted, equivalently `65535 − count`. Both fields put the low byte first. Check that they agree, then copy exactly the announced number of raw bytes.

The count ends this block, so a stored block has neither a Huffman payload nor a coded end-of-block symbol. Its bytes still extend the output used by later matches. The inverted count detects inconsistent length fields; it does not establish that the raw content is the intended content. End-to-end content checks will be a separate feature in the third article.

### Decode the same eight bytes in a real fixed block {#fixed-example}

Return to the fixed books and the same instructions: literal A, literal B, length 6/distance 2, end-of-block. The first field selects a final fixed block. The words below are written **in the order the Huffman tree encounters their bits**, with the first printed character read first:

| Field | Meaning | Bit sequence in reading order |
| --- | --- | --- |
| Header | Final flag 1, fixed type 1 | `1`, then `1 0` |
| Literal/length word | Literal A, symbol 65 | `01110001` |
| Literal/length word | Literal B, symbol 66 | `01110010` |
| Literal/length word | Length 6, symbol 260 | `0000100` |
| Distance word | Distance 2, symbol 1 | `00001` |
| Literal/length word | End-of-block, symbol 256 | `0000000` |

Length 6 and distance 2 require no extra bits. The meaningful bit count is `3 + 8 + 8 + 7 + 5 + 7 = 38`. The distance word still uses its own tree; the header did not collapse the two books into one.

Now place those bits in bytes. Each byte has positions numbered 0–7, with position 0 contributing 1 and position 7 contributing 128. DEFLATE fills position 0 first, then 1, through 7, then position 0 of the next byte. A byte printed conventionally in binary puts position 7 on the left. The order in which we fill a byte is consequently opposite to the order in which its eight digits are printed.

The first eight arriving bits are `1 1 0 0 1 1 1 0`: the three header bits followed by the first five bits of A's word. Place them in these positions:

<figure class="df-figure">
<table><thead><tr><th>Byte bit position</th><th>7</th><th>6</th><th>5</th><th>4</th><th>3</th><th>2</th><th>1</th><th>0</th></tr></thead><tbody>
<tr><th>Arrival number</th><td>8</td><td>7</td><td>6</td><td>5</td><td>4</td><td>3</td><td>2</td><td>1</td></tr>
<tr><th>Bit stored</th><td>0</td><td>1</td><td>1</td><td>1</td><td>0</td><td>0</td><td>1</td><td>1</td></tr>
</tbody></table>
<figcaption class="df-caption">Read the bottom row from bit 7 to bit 0 to print the byte: 01110011, hexadecimal 73. Consuming its bits from bit 0 upward recovers the original arrival order.</figcaption>
</figure>

Continue without aligning between fields. A's remaining three bits share the second byte with the beginning of B's word. After all 38 meaningful bits, two zero bits occupy the remaining positions in the last byte. The complete raw DEFLATE stream is:

```text
73 74 82 40 00
```

There is one further bit-order rule. A multi-bit **number field** supplies its low-valued bit first: the numeric block type 1 is read as `1,0`, giving `1 + 0 × 2 = 1`. A **Huffman word** instead supplies its code bits in the canonical word's order: A is encountered as `0,1,1,1,0,0,0,1`. Both kinds of field fill the next available byte positions in exactly the same low-to-high order. What differs is how each field supplies those successive bits. Reversing every printed binary field indiscriminately loses that distinction.

A fresh decoder now has everything it needs. Its bit reader supplies the three header bits, which select the fixed books. At the literal/length root, it reads A and B, then length 6. At the distance root it reads distance 2. It performs six dependent byte copies, returns to the literal/length root, and reads end-of-block. The final flag says there is no next block. It has recovered eight bytes from five compressed bytes, using only the stream and the format's rules.

This is one legal selected encoding. A particular run of zlib's compressor can choose a different valid match or block. The receiver follows the choices actually represented in the input, whichever legal encoder produced them.

The actual decoder represents the same copy with moving pointers. In the branch that copies directly from already produced output, `put` points at the next output byte and `state->offset` holds the decoded distance. The source begins that distance before `put`. `from` names its current position; `copy` counts how many bytes this part will append. The core [`inflate.c` copy loop](https://github.com/madler/zlib/blob/757f0527154291bcf6bfbd6396ecde6bedd2db95/inflate.c#L1063-L1075) retains the sequential meaning we derived:

```c
            do {
                *put++ = *from++;
            } while (--copy);
```

Each iteration copies one source byte to the destination and advances both pointers. Bytes written earlier by the same loop can become its later source, just as in the distance-2 table. Efficient decoding must preserve this meaning even when it processes several bytes per iteration.

## Improve the codec, then extend its job {#roadmap}

We now have the complete basic picture. The encoder chooses literals and matches, codes the resulting symbols, supplies or identifies its books, and delimits the encoded message. The decoder reconstructs those books, parses the actual bits, expands matches from its own output, and recognizes completion. Every item is needed before the receiver can work independently.

The next question is efficiency. Searching every earlier position is expensive. Trying more matches can improve the compression ratio while taking more time. A custom book can shorten the payload while making a small block larger overall. A decoder that follows one tree edge per bit is easy to understand but spends work that a lookup table can avoid. The [next article on time, memory and compression ratio](/read/optimizations.html) develops those tradeoffs for both `deflate` and `inflate` from this complete codec.

After those optimizations, [the third article on practical features](/read/features.html) extends the task: accept data in batches, pause and continue with limited output storage, request flush boundaries, reuse a dictionary, and place DEFLATE inside zlib or gzip framing with Adler-32 or CRC-32 checks. Those additions depend on the byte transformation already established here. They let the same compression mechanism serve real applications with different delivery, reuse and integrity requirements.
