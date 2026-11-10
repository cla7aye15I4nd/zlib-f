<p class="zl-kicker">An essay you can take apart</p>

A compression library takes bytes and produces other bytes. Behind that small interface are match searches, codes, bit buffers, and a state machine that can pause between calls. We will take them apart with small examples, then ask how to know that the actual program gets them right.

Part one explains zlib’s algorithms and implementation. Part two introduces formal verification, using the same bytes, tables, and buffers. Expand a detail when you want more depth, or start by changing something in a diagram.

# Part one: algorithms and interfaces {#how-zlib-works}

<p class="zl-part-intro">Start with eight bytes. Build the compression and decoding process before discussing proofs.</p>

## Literals and back-references {#bytes}

Take a look at this string: `ABABABAB`.

We could send all eight bytes. Another option is to send `A` and `B`, then add an instruction: **go back two bytes and copy one byte at a time, until six more bytes have been produced.**

There are two numbers here. The distance, `2`, tells the receiver where to read. The length, `6`, tells it how many bytes to produce. Together, they describe a match. A single byte sent directly is called a literal.

<div class="zl-token-line"><span>literal A</span><span>literal B</span><b>match · length 6 · distance 2</b></div>

It is too early to count the savings. We have only replaced the bytes with a sequence of symbols. Those symbols still need an encoding, and the stream may need a wrapper. For an input this short, the final compressed representation could easily be larger than the original.

But we have made the main problem smaller. If the receiver can execute these three symbols, it can reconstruct the string. Try copying just one byte at a time.

<div class="zl-demo-mount"><zlib-demo kind="copy">
  <p>Start with AB. A match of length 6 and distance 2 extends the output to ABA, ABAB, ABABA, ABABAB, ABABABA, and finally ABABABAB.</p>
</zlib-demo></div>

The first copy reads the original `A`. The second reads `B`. The third reads an `A` that this very match has just written.

The instruction does not take a six-byte snapshot of the original two-byte history. Each step goes back two positions, reads a byte, and adds it to the output. As the history grows, the read position moves forward. That is why the match length can exceed its distance.

Change the distance to `1` to see another familiar pattern: one `A` keeps producing more copies of itself.

This is the LZ77 idea used by DEFLATE. Previously seen content can be reproduced by referring back to history. The example explains the meaning of a valid symbol sequence; it does not claim that real zlib will choose exactly these symbols for this short input.

<p class="zl-proof-link">Related interfaces and formats：<a href="./reference/functions/inflate.html">inflate</a></p>

## Library and formats {#layers}

We can now put the names back into the picture.

**zlib is a C library.** It provides compression, decompression, checksums, and interfaces for buffers and streams. Its core streaming compression interface is called `deflate`; the decompression interface is `inflate`.

**DEFLATE is a data format.** It describes how literals, matches, and blocks become bits, and how to recover those symbols from the bits. It does not prescribe how a compressor must find its matches. Two compressors can choose different representations of the same input and still produce valid streams.

**zlib and gzip are also wrapper formats.** They put different headers and trailers around a DEFLATE payload. Raw DEFLATE has no such wrapper.

<figure class="zl-layers">
  <div><span>zlib</span><i>Header</i><b>DEFLATE payload</b><i>Adler-32</i></div>
  <div><span>gzip</span><i>Header and optional fields</i><b>DEFLATE payload</b><i>CRC-32 · size</i></div>
  <div><span>raw</span><b>DEFLATE payload</b></div>
  <figcaption>Wrappers carry identification, parameters, and integrity checks. These checksums detect data corruption; they do not provide cryptographic authentication.</figcaption>
</figure>

Producing the last data byte does not necessarily finish the stream. The decoder may still need to read an end-of-block symbol, check a checksum, or validate the gzip size field. We will return to this distinction when we split decompression across calls.

The original format definitions are [DEFLATE / RFC 1951](https://www.rfc-editor.org/rfc/rfc1951), [zlib / RFC 1950](https://www.rfc-editor.org/rfc/rfc1950), and [gzip / RFC 1952](https://www.rfc-editor.org/rfc/rfc1952).

## Windows and hash chains {#search}

Once a decoder receives a length and a distance, it can follow the instruction. The compressor has the harder job: where do those numbers come from?

The most direct approach is to try every earlier position. Compare the first byte, then the second, and continue until they differ. On a long input, repeating this search at every position becomes expensive.

zlib narrows the search using a hash of three starting bytes. A `head` table points to the most recently inserted position in a hash bucket. A `prev` table links that position to an earlier candidate. Following these links lets the compressor compare possible matches one at a time.

The same hash does not guarantee the same content. It only suggests where to look. The actual match length still comes from comparing bytes.

Here, the most recent candidate is at position `4`, starting with `ABCR`. An earlier candidate is at position `0`, starting with `ABCQ`. The input we are about to process is `ABCQABCX`.

```text
position  0    4    8
          ABCQ ABCR ABCQABCX
          ↑    ↑    ↑
        earlier latest current
```

Checking only the latest candidate finds `ABC`, a match of length `3`. Following the chain once more finds `ABCQABC`, a match of length `7`. Both candidates begin with the same three bytes; the later bytes determine how far the match can extend.

<div class="zl-demo-mount"><zlib-demo kind="search">
  <p>With a budget of 1, the simplified chain search checks only the latest candidate and finds a length-3 match. A budget of 2 reaches the earlier candidate and finds a length-7 match. This illustrates a search budget, not the actual hash function.</p>
</zlib-demo></div>

Searching farther costs more comparisons. zlib's settings include a candidate budget and a match length that is good enough to stop early. Higher compression levels can spend more time searching, but this is still a bounded search. It does not promise a globally optimal compressed representation.

<details class="zl-deep"><summary>In depth · Windows and position tables</summary>
<p>The byte window stores content. <code>head</code> and <code>prev</code> store clues about where to find that content. The former is indexed by hash bucket; the latter uses circular slots derived from positions.</p>
<p>When the window slides, retained bytes move to smaller positions, so positions in the chains must move too. Links outside the retained range are discarded. Moving the bytes without updating the links would make the next comparison start at the wrong place.</p>
<p>This illustration uses logical positions and allows position 0 to be a candidate. The real implementation reserves 0 for NIL and also handles window size, search distance, and circular slots. Compression level controls search strategy; <code>memLevel</code> controls a different set of storage sizes.</p>
</details>

<p class="zl-proof-link">Related interfaces and formats：<a href="./reference/functions/deflate.html">deflate</a> · <a href="./reference/functions/deflateTune.html">deflateTune</a></p>

## Lazy matching {#lazy}

Suppose we have already found a match of length `3`. Taking it immediately seems reasonable. But what if a much longer match starts at the next position?

Let the history contain `XABZ` and `ABCDEFGH`. The current input is `XABCDEFGQ`.

```text
history: !XABZ!ABCDEFGH!
input:    XABCDEFGQ
          ↑ current position
```

At the current position, `XAB` matches the history. The comparison then stops because the historical `Z` differs from the current `C`. The match length is `3`.

Move forward one position. The remaining input is now `ABCDEFGQ`. It matches `ABCDEFG` in the history, stopping where `H` differs from `Q`. This match has length `7`.

We can therefore emit a literal `X` and use the longer match from the next position. That is the idea behind lazy matching: delay the current decision long enough to see whether the next position offers a better match.

<div class="zl-lazy-comparison">
  <div><span>Take the match now</span><b>XAB</b><i>CDEFGQ</i><small>Start with a length-3 match</small></div>
  <div><span>Look one step ahead</span><i>X</i><b>ABCDEFG</b><i>Q</i><small>Emit X, then use a length-7 match</small></div>
</div>

zlib's slow strategy keeps the match found at the previous position. If the new position does not offer a longer match, it uses the saved one. If the new match is longer, it emits the previous position's first byte as a literal and keeps considering the new match. Search conditions also limit when this extra work is worthwhile.

The example compares available matches. It does not claim that the second path always has a smaller final bit cost. Literals, lengths, and distances have different encoding costs. A local match decision and the minimum cost of an entire block are different questions.

<p class="zl-proof-link">Related interfaces and formats：<a href="./reference/functions/deflate.html">deflate.c</a></p>

## Huffman trees {#huffman-tree}

We have avoided sending some repeated bytes, but the remaining symbols still need an encoding. If every symbol takes the same number of bits, common symbols receive no advantage.

Start with four abstract symbols. Suppose a block contains `A` eight times, `B` four times, and `C` and `D` twice each. Encoding every symbol in two bits takes `32` bits.

We would like to give the common `A` a shorter code. But the receiver must still decode a continuous stream without separators. A prefix code makes this possible: no complete symbol's code is the beginning of another symbol's code.

Huffman construction repeatedly merges the two lowest-weight nodes. Here, it first combines `C:2` and `D:2` into a node of weight `4`. That node combines with `B:4` to make `8`. Finally, the result combines with `A:8` to form the root.

```text
2 + 2 → 4
4 + 4 → 8
8 + 8 → 16
```

Each tree level adds one bit to a leaf's code. `A` ends up at depth `1`, `B` at depth `2`, and `C` and `D` at depth `3`. The data now costs:

```text
8 × 1 + 4 × 2 + 2 × 3 + 2 × 3 = 28 bits
```

The fixed two-bit comparison only explains this four-symbol example. It is not DEFLATE's fixed Huffman table, which has a larger alphabet and specific code-length rules.

## Canonical Huffman codes {#canonical}

We could flip the left and right branches of the tree and get different bit patterns with the same lengths. If the compressor and decoder choose their trees independently, how can they agree on the codes?

DEFLATE uses canonical Huffman codes. Both sides follow the same rule: order symbols by code length, then by symbol value, and assign consecutive codes. The compressor does not need to send a complete tree. It only needs to let the decoder recover each symbol's length.

For `A:1, B:2, C:3, D:3`, that rule gives:

```text
A →   0
B →  10
C → 110
D → 111
```

To move from `0` to `10`, first advance past the code already used at the shorter length, then shift left to make room for another bit. Symbols at the same length simply receive consecutive numbers.

<div class="zl-demo-mount"><zlib-demo kind="huffman">
  <p>Lengths 1, 2, 3, 3 produce codes 0, 10, 110, 111. Change the lengths to see how a shorter code occupies more of the coding space, and which length assignments cannot form a prefix code at all.</p>
</zlib-demo></div>

A leaf of length `1` occupies half of the tree's coding space. A leaf of length `2` occupies one quarter. Adding `2⁻length` over the used symbols gives the Kraft sum. A sum of `1` fills the space exactly; a sum greater than `1` means that some codes must conflict.

This gives a decoder an early check. If a length description is impossible, it does not have to wait until data decoding to discover the contradiction. Real zlib also distinguishes complete tables, empty tables, and certain single-symbol cases. The decoding chapters will return to those details.

<details class="zl-deep"><summary>In depth · Dynamic code-length descriptions</summary>
<p>DEFLATE has a literal/length alphabet and a distance alphabet. Literal values represent bytes directly. A length symbol, together with any extra bits, gives a match length. Distances also use symbols and extra bits. A dedicated symbol in the literal/length alphabet marks the end of a block.</p>
<p>A dynamic block describes the lengths for those two alphabets. Repeated lengths and runs of zero lengths can themselves be represented by repeat symbols. Those symbols need another code. A dynamic description therefore involves three related codes: the code-length code, the literal/length code, and the distance code.</p>
<p>Real Huffman trees also have length limits. An unconstrained merge can make a tree too deep, so zlib adjusts the length counts and reassigns lengths. The four-symbol example does not exercise that repair; it explains the construction's motivation and the canonical assignment.</p>
</details>

<p class="zl-proof-link">Related interfaces and formats：<a href="./reference/docs/format/README.html">DEFLATE</a></p>

## Block types and costs {#blocks}

Our four-symbol example reduced the data cost from `32` bits to `28`. If explaining the new code to the receiver costs more than four bits, the complete representation has saved nothing.

A dynamic table is not free. It works best when enough data can share its description cost. A small block may do better with a code that both sides already know, or with the original bytes stored directly.

DEFLATE therefore provides three block forms:

| Block form | How the receiver interprets it | Main costs |
| --- | --- | --- |
| stored | Read the original bytes using the supplied length | Byte alignment, length and its complement, original data |
| fixed | Use code lengths prescribed by the format | Header, symbols, and extra bits |
| dynamic | Recover this block's code lengths, then decode symbols | Header, code description, symbols, and extra bits |

When flushing a block, zlib computes the fixed and dynamic coding costs, then considers whether it can use the stored form. The original bytes must still be available for that branch to copy. Strategy settings also influence the choice.

There are therefore two different decisions between the input and the compressed stream. First, choose the literals and matches that represent the input. Then choose how to encode that block of symbols. The next chapter follows the reverse direction: how does a receiver turn those bits back into the original bytes?

## Bit order and buffers {#bit-order}

Now move to the decoder’s side. It receives bytes, extracts their bits, and turns those bits back into symbols.

Positions within each byte are used from low to high. Ordinary numeric fields put their least significant bit first; a Huffman code puts its most significant code bit first. As a result, the same bits look reversed when shown in arrival order and in the usual notation for an integer.

Take C’s code, `110`. The first `1` goes into buffer bit 0, the second `1` into bit 1, and the final `0` into bit 2. Written with the highest bit on the left, the buffer value is `011`.

<figure class="zl-bit-order">
  <div><span>Arrival order</span><b>first → second → third</b></div>
  <div><span>Received values</span><b>1 → 1 → 0</b></div>
  <div><span>Buffer positions</span><b>bit 0 → bit 1 → bit 2</b></div>
  <div><span>Usual integer notation</span><b>bit 2 · bit 1 · bit 0 = 0 1 1</b></div>
  <figcaption>The arrival order has not changed. The first bit received lives in the integer’s lowest position.</figcaption>
</figure>

With that distinction, the bit buffer becomes less mysterious. zlib stores its value in `hold` and counts its valid bits in `bits`. Refills append bytes above the existing valid bits; interpreting a field or code removes the required number of bits from the low end.

<details class="zl-deep"><summary>Go deeper · Code representation and input bits</summary>
<p>The implementation does not have to reverse every received byte before passing it to another decoder. Instead, the table builder can arrange entries using reversed code values, so the decoder can index them directly with hold’s low bits. Ordinary counts, lengths, and extra-bit fields still follow their own numeric rules.</p>
</details>

## Decode tables {#lookup}

Reading one bit at a time and following the coding tree will decode a symbol. An implementation can combine several of those decisions into one array access: inspect a few low bits and look up the result.

Keep A=`0`, B=`10`, C=`110`, and D=`111`, and let the root table inspect two bits. There are only four slots:

| Lowest two bits of `hold` (highest shown on the left) | Result | Bits consumed |
| --- | --- | --- |
| `00` | A | 1 |
| `01` | B | 2 |
| `10` | A | 1 |
| `11` | Subtable | 2, before continuing |

Why does A occupy two slots? Its code is only one bit long. Once the lowest bit is `0`, the next bit can be either `0` or `1` without changing A’s meaning. The root table inspects two bits but consumes only one.

Try decoding `AD`. Concatenating the codewords gives `0 | 111`; written as a buffer integer, that is `1110`. The root index is `10`, yet the result is still A. Removing one bit leaves `111`: root index `11` follows the link, then subtable index `1` gives D.

<div class="zl-demo-mount"><zlib-demo kind="lookup">
  <p>The teaching message AD arrives as the bits 0, 1, 1, 1. Initially hold=1110 and bits=4. Root index 10 yields A and consumes one bit; the remaining 111 reaches D through root index 11 and subtable index 1.</p>
</zlib-demo></div>

This separates three things: **how many bits we inspect, how many we consume, and which symbol we emit.** Dropping two bits after finding A would swallow D’s first bit and misalign everything that follows.

C and D need a subtable because two root bits cannot distinguish them. A wider root can reduce subtable lookups, but uses more space. The real `inflate_table` builds its root and subtables around the length distribution rather than expanding an entire fifteen-level tree.

<details class="zl-deep"><summary>Go deeper · Lookahead and consumption</summary>
<p>The bit buffer may hold bits for later symbols, and the fast decoder may prefetch bytes. Their presence in the buffer does not make them part of the current symbol. When leaving the fast path, the implementation returns unused whole bytes to the input cursor and retains fewer than eight buffered bits. Input cursor movement, buffered bits, and emitted symbols therefore need to be read together.</p>
</details>

<p class="zl-proof-link">Related interfaces and formats：<a href="./reference/functions/inflate.html">inflate</a></p>

## Streaming decode {#stream}

Return to `ABABABAB`. Two literals and a match of length 6, distance 2 can represent it. With an output buffer of five bytes, the decoder produces `ABABA` and pauses.

It has already decoded the instruction to copy six bytes, but completed only three of them. The next call needs to finish the remaining three, rather than parse the same match again.

<div class="zl-demo-mount"><zlib-demo kind="stream">
  <p>Teaching symbol stream: A, B, match(length=6, distance=2). Five output bytes on the first call produce ABABA, leaving length=3 and distance=2. The next call produces BAB. Together the logical output is ABABABAB.</p>
</zlib-demo></div>

Reducing the output capacity increases the number of calls without changing what this symbol sequence means. A pause can happen elsewhere too: partway through a field, before a dynamic table description is complete, or while waiting for a wrapper trailer. Each pause needs enough saved state to resume the unfinished work.

<div class="zl-stream-example">
  <p><strong>After the first call:</strong> logical output ABABA; mode MATCH; remaining match length 3; distance 2.</p>
  <p><strong>At the next call:</strong> supply a new writable output buffer; read B from saved history first, then continue byte by byte to produce BAB.</p>
</div>

There is a physical change here: the caller can replace the output buffer. The first call’s `ABABA` may no longer be directly available in the next call’s output object. The stream therefore needs its own history window, retaining a suffix of earlier output for later back-references. Once the new call has produced enough bytes, a match source can move back into the current output.

The logical history is one continuous sequence, but its physical source can switch between the saved window, current output, and a preset dictionary. This is one of the most useful transitions to make visible in a streaming animation.

Finally, producing these eight payload bytes is different from completing the whole stream. The real `inflate` must reach the end of the blocks and, where applicable, process the checksum and other wrapper fields before reporting `Z_STREAM_END`. The demonstration executes only the given symbol sequence, without simulating the entire bit parser or its return codes.

`Z_FINISH` cannot create more output space. The caller still has to provide room for the unfinished result. When a preset dictionary is required, the decoder likewise needs the corresponding history before it can continue interpreting back-references.

<p class="zl-proof-link">Related interfaces and formats：<a href="./reference/functions/inflate.html">inflate</a> · <a href="./reference/docs/api/streams.html">Stream rules</a></p>

# Part two: formal verification {#verifying-zlib}

<p class="zl-part-intro">We now know what the program is trying to do. What justifies each step?</p>

The first half followed an input through the algorithm. The program also has to handle a different input, a smaller output buffer, a failed allocation, and every operation sequence that its interface permits.

Formal verification brings these variations into one precise question. We will start with a single write, then see how its reasoning extends to tables, buffers, and a stream's entire lifetime.

## Execution and loop invariants {#write-proof}

Return to the match with length 6 and distance 2. The loop has copied `i` bytes and is about to write another. Knowing that the final output should be `ABABABAB` is not enough. The current destination must belong to live, writable memory.

First reduce the question to a small arithmetic fact. If `i < length` and `length ≤ capacity`, then `i < capacity`. In Lean:

```lean
theorem next_write_in_bounds (i length capacity : Nat)
    (running : i < length) (room : length ≤ capacity) :
    i < capacity :=
  Nat.lt_of_lt_of_le running room
```

Here, `running` and `room` are two available facts. The proof term combines them to establish an upper bound on the write index. Lean's kernel checks that inference.

The real C program, however, has no abstract object called a “natural-number capacity.” It has pointers, arrays, machine integers, and a heap. We must also connect `capacity` to the actual destination object's valid extent, show that the object is still live, and establish permission to write. Reading the source requires its own justification.

Functional correctness asks one more question: is the value being written the right one? The bytes already produced must agree with an independently defined back-reference semantics. When the source reaches output produced by this very match, the next read must still yield the required byte.

A loop invariant keeps these facts available whenever the loop starts another iteration. It records completed work and prepares the conditions for the next step: the first `i` bytes are correct, the next accesses are valid, and the remaining length is accurate. After one step, the proof establishes the corresponding facts for `i + 1`.

<details class="zl-deep"><summary>Deeper · Access bounds and termination</summary>
<p>A loop can remain inside an array forever. A copy loop can use its decreasing remaining length to justify termination. The main decoder also has mode transitions that consume no input and produce no output. Those silent steps need an additional control rank; counting input bytes alone is insufficient.</p>
<p>The project's runtime uses finite loop fuel. Its proofs must exclude exhaustion of the actual fuel bound, beyond showing that a mathematical loop eventually ends. Termination and leak freedom are part of this project's safety goal, although neither is itself an instance of C undefined behavior.</p>
</details>

<p class="zl-proof-link">Contracts and detailed arguments：<a href="./reference/functions/inflate.html#formal-target">Goal.inflate</a> · <a href="./reference/functions/deflate.html#formal-target">Goal.deflate</a> · <a href="./reference/docs/proof/method.html">Method</a></p>

## Table safety and meaning {#table-proof}

In Part I, `C` had the code `110`. A lookup examines the low two buffer bits in the root table, then selects `C` through a subtable.

Now change exactly one thing: replace the result in that subtable entry with `D`. Keep the index and code length unchanged. Every access remains inside the arrays, but the decoder produces the wrong symbol.

<div class="zl-demo-mount"><zlib-demo kind="table-proof">
  <p>Keep the same root link and subtable index, changing only C's entry value to D. The access remains bounded. Input 110 now yields D instead of C, so the table no longer agrees with the canonical code.</p>
</zlib-demo></div>

Table safety and table correctness therefore require two arguments. The first says that the next entry is initialized, its index is bounded, and any link leads to a valid subtable. The second says that the entry implements the corresponding code: it yields the right literal when one is required, and does not disguise an invalid code as a successful result.

Both arguments must refer to the same table. Proving that a mathematical function generates a correct table does not show that the translated `inflate_table` wrote those entries into the heap.

The producer and consumer need a bridge. The constructor's actual execution establishes a relation over the entries; the decoder's actual pointer identifies those entries; the lookup proof then uses that relation. The project's [decode-table guide](https://github.com/cla7aye15I4nd/zlib-f/blob/main/docs/proof/inftrees.md) develops this distinction.

<details class="zl-deep"><summary>Deeper · Initialization coverage</summary>
<p>A short code is replicated into several root entries. Longer codes need subtables. To permit every reachable lookup, the constructor's proof must cover every entry the reader might reach. Showing that each individual write was in bounds does not establish that coverage.</p>
<p>Empty tables and permitted single-symbol incomplete tables also need separate cases. They cannot be treated as complete prefix codes and justified by claiming that every input prefix falls below a valid leaf.</p>
</details>

<p class="zl-proof-link">Contracts and detailed arguments：<a href="./reference/docs/proof/inftrees.html">Decode tables</a> · <a href="./reference/docs/proof/inffast.html">Fast decode</a></p>

## Shared buffers and prefix bounds {#overlay}

The compressor has a more subtle memory problem. Symbols awaiting encoding and bytes awaiting output can share storage. Once a symbol has been read, the space it occupied becomes available for compressed output.

A plausible proof goal is that the final compressed result fits inside the buffer.

Let's test whether that condition is enough. The following model shrinks memory to 32 cells, with three-byte symbols beginning at offset 8. Each step reads one symbol before writing the output it produces. Run the safe and front-loaded schedules side by side, and take just one step.

<div class="zl-demo-mount"><zlib-demo kind="overlay">
  <p>In this artificial plan, two output bytes already exist. After reading the first symbol, unread symbols begin at offset 11. Writing twelve more bytes brings output to offset 14 and overwrites cells 11, 12, and 13. The final output occupies only 20 of 32 bytes, but the earlier damage remains.</p>
</zlib-demo></div>

The last number fits, while the first dangerous prefix has already destroyed future input. These are two different conditions.

The small dimensions and write plans are constructed to demonstrate that distinction. They are neither evidence that zlib can produce such a block nor a vulnerability reproduction.

In the actual shared-symbol branch, let `B = lit_bufsize`. Pending storage occupies `4B` bytes. Symbols begin at offset `B` and occupy three bytes each. After the first `q` symbols have been read, the unread region starts at:

```text
R(q) = B + 3q
```

Let `P(q)` be the number of output bytes written by then. Knowing only that the final `P(K) ≤ 4B` is like looking only at the animation's last frame. Symbol emission needs control over the intermediate `P(q)` values. The project uses a sufficient bound of the following form:

```text
P(q) < R(q)       at the corresponding symbol-emission boundaries
```

Every intermediate write must also avoid the unread suffix. Tree descriptions and headers emitted before the first symbol, along with the end code and final alignment, need their own space arguments.

<details class="zl-deep"><summary>Deeper · Strict bounds and overlap</summary>
<p>If written output occupies the half-open interval <code>[0, P)</code> and unread storage starts at <code>R</code>, then <code>P = R</code> does not itself overlap that storage. The project uses a strict inequality as a sufficient bound here. Failure of this stronger proof condition must not automatically be drawn as an illegal write that already occurred.</p>
<p>The animation marks the cells actually touched by writes. A mathematical budget and the data the program has actually damaged are different things.</p>
</details>

<p class="zl-proof-link">Contracts and detailed arguments：<a href="./reference/docs/proof/trees.html">F9 / trees.c</a></p>

## Huffman frequency bounds {#huffman-bound}

Fixed codes give direct bounds on the cost of each symbol, so a conservative output budget can be accumulated. Dynamic codes are harder: early symbols can have long codes, while frequent symbols later in the block have short ones.

“The entire dynamic block is smaller than the fixed block” is therefore still only a total-cost fact. It does not constrain an early prefix by itself. The Kraft condition establishes a valid code, but says nothing about the relationship between those code lengths and this block's frequencies.

Useful facts come from the actual Huffman construction. It repeatedly selects nodes with small weights and merges them. For a leaf to end up very deep, enough surrounding merge structure and weight must exist. That relationship between depth and frequency can help bound the contribution of long codes to prefix cost.

One mathematical route in the project uses Fibonacci weight growth, together with repair when lengths exceed the format's limit. Its eventual purpose is a prefix budget that protects unread symbols.

The budget's inputs cannot simply be assumed. Its premises must come from the actual symbol counts, queue selections, merges, and length repair, then connect to the actual bit buffer and writes. Establishing those bridges is often the central work, beyond proving another property of an abstract tree.

See the [shared-buffer argument](https://github.com/cla7aye15I4nd/zlib-f/blob/main/docs/proof/trees.md#the-overlay-lemma-f9) for the detailed route. Current completion scope is recorded in the overview.

<p class="zl-proof-link">Contracts and detailed arguments：<a href="./reference/docs/proof/trees.html">Tree construction</a></p>

## Invariants across calls {#history-proof}

The earlier decoder paused after `ABABA`. Three match bytes remained, with distance still equal to 2. The next call supplies another output buffer and should continue the work.

A correct output prefix does not mean that the old output pointer remains valid forever. The caller may replace buffers, while the decoder's own history window retains bytes needed later. The proof tracks a relation between logical history and the actual storage available now.

At an API return, the call must leave a representation invariant that the next call can use. It includes memory and algorithmic facts: stream-owned blocks remain live; tables and window pointers have valid origins; consumed input corresponds to produced output; an unfinished match retains its precise pending work.

Where does that relation come from? Initialization must establish it. Every permitted operation then preserves it or produces a terminal state with the interface's specified meaning. Writing down a strong-looking invariant and assuming that every call starts from it does not establish that actual calls reach such a state.

Helpers follow the same rule. First prove the specification of the actual translated helper. Its caller then establishes the helper's premises from the current state. “The helper is correct” cannot be an unproved assumption.

<details class="zl-deep"><summary>Deeper · Premises for composition</summary>
<p>One lemma may bound cursors stored in the heap, while another needs the current cursors held in local registers. These are not necessarily equal throughout execution: a function can load fields into locals and write them back only at the end. The connecting relation must describe the correct execution point.</p>
<p>Similarly, premises preserved by ordinary data calls can be changed by reset, dictionaries, copy, or recovery. A theorem about complete call sequences must cover the transitions the interface permits, rather than repeating only the common data path.</p>
</details>

<p class="zl-proof-link">Contracts and detailed arguments：<a href="./reference/docs/proof/stream-composition.html">Stream composition</a> · <a href="./reference/docs/proof/inflate.html">inflate.c</a> · <a href="./reference/docs/proof/deflate.html">deflate.c</a></p>

## Ownership and failure cleanup {#ownership}

The successful path hands a state to the next call. A failure path must also account for what remains.

Consider a teaching initializer with two resources. It allocates `state`, then `window`. If the second allocation fails, the first block already exists. Returning an error immediately can still leak that block.

<div class="zl-demo-mount"><zlib-demo kind="ownership">
  <p>This teaching model allocates state before window. If window allocation fails, it frees the state it already owns before returning an error. Successful initialization retains both resources until end releases them. Each real API needs an argument about its own allocation order.</p>
</zlib-demo></div>

Successful initialization should not restore the original heap. It should acquire resources and retain clear ownership. Failed initialization and normal teardown must release those resources, each exactly once.

The animation also contains “other objects” that never move. They represent memory the caller already owned and this operation has no permission to modify. Proving that these objects remain unchanged is the frame condition. Merely counting the final number of live blocks does not show that someone else's data was preserved.

A real lifecycle also includes copying and partial failure. Copy acquires independent destination storage and must relocate internal pointers. A failed copy cleans up resources acquired by that attempt while preserving the source stream. Memory effects of error returns must be stated for each branch.

<p class="zl-proof-link">Contracts and detailed arguments：<a href="./reference/functions/deflateInit_.html">deflateInit_</a> · <a href="./reference/functions/inflateEnd.html">inflateEnd</a></p>

## Scope and trust boundaries {#trust}

We have been discussing executions and proofs. In zlib-f, Lean's kernel checks propositions about Lean computations. Those computations translate selected C source statement by statement and execute under the project's semantics for heaps, pointers, arithmetic, and loops.

Two connections therefore need independent review: whether the translation faithfully represents the selected C, and whether the runtime adequately represents the relevant C operations. The kernel checks the reasoning without automatically checking either connection.

<div class="zl-proof-chain" aria-label="Connections from source to conclusions"><span>Selected C</span><i>Translation and semantic review</i><span>Lean execution</span><i>Kernel-checked proof</i><span>Independent specification</span></div>

This distinction creates concrete obligations. Fresh pointer fields are NULL in the model. If an initialization write is omitted, a later read and NULL comparison may not trigger a model fault. The argument must separately establish that the corresponding pointer field was written before being read.

Fresh integer cells instead contain arbitrary values, and the theorem must hold for all of them. Repeated reads of an uninitialized cell agree in the model; an argument cannot rely on that agreement to justify more general C behavior. The object heap also lacks a complete machine-address and ABI byte-layout model. The [trusted base](https://github.com/cla7aye15I4nd/zlib-f/blob/main/docs/trusted-base.md) records those boundaries.

Differential tests can reveal behavior differences between C and its translation, providing evidence of fidelity. Proof mutation tests change a translation and check whether the corresponding function proof fails. Audits check permitted axioms, registration, and other acceptance requirements. These forms of evidence complement one another without replacing one another.

This article's interactions run independently written teaching models. They make particular executions visible; they neither run Lean proofs nor execute zlib's C translation. General correctness claims require the precise propositions and their proofs.

The project's first target is the default x86_64 Linux/LP64 static build with the default allocator. Malformed inputs, error returns, and allocation failures remain within the work to cover. Full verification is not complete. Current results, blockers, and remaining work have one home: the [project overview](https://github.com/cla7aye15I4nd/zlib-f/blob/main/docs/overview.md). Acceptance requires the evidence and CI on a named commit.

<p class="zl-proof-link">Contracts and detailed arguments：<a href="./reference/docs/safety.html">Safety</a> · <a href="./reference/docs/trusted-base.html">Trusted base</a></p>

## Further reading {#reading}

- [The format guide](https://github.com/cla7aye15I4nd/zlib-f/blob/main/docs/format/README.md): complete alphabets, wrappers, and acceptance rules.
- [Proving one function](https://github.com/cla7aye15I4nd/zlib-f/blob/main/docs/proof/method.md) and [composing stream calls](https://github.com/cla7aye15I4nd/zlib-f/blob/main/docs/proof/stream-composition.md): connecting local arguments to public interfaces.

