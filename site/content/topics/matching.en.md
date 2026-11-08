## From repeated bytes to a reference {#connection}

In the [complete process](/algorithms/index.html), the compressor chooses symbols to represent input before encoding those symbols. Repetition gives that first step a saving: `ABABABAB` can be represented by literals `A`, `B`, followed by “go back 2 bytes and copy 6.” We select these three symbols to explain their meaning; an actual call's choices also depend on input batches, strategy and search limits.

The reference does not carry six bytes. The decoder copies one byte at a time from the recovered `AB`. Each copied byte extends the available output, eventually adding `ABABAB`. The compressor must therefore find a source with **the same content**. Choosing a shorter match may compress less; choosing the wrong source changes the data.

<figure class="bk-route-flow" aria-label="Processing bytes into symbols"><ol><li><strong>Retain possible source bytes</strong><span>The window holds processed content and input still awaiting a representation decision.</span></li><li><strong>Narrow the candidates</strong><span>A three-byte hash finds possible positions; byte comparison rejects collisions.</span></li><li><strong>Commit a record</strong><span>A strategy selects a literal or length/distance pair; lazy matching also considers the next starting position.</span></li><li><strong>Hand it to block encoding</strong><span>A record saves the choice, while frequency tables count the symbols to encode.</span></li></ol><figcaption>The window and hash help find a source. A choice becomes a pending record only when the strategy commits it.</figcaption></figure>

## Retention, search and selection {#mechanisms}

The window first solves a memory problem. Input can keep arriving, while the compressor retains only recent sources. Byte comparison uses a contiguous array; a batch move frees space near its end. [The window and candidate index](/sample/window.html) starts with `0123ABCDABCDwxyz` and follows retention, lookahead, moving bytes and hash chains. Its separated `ABCD` passages make the source and current input easy to locate.

Keeping the bytes does not identify the most useful reference. [Candidate search and lazy decisions](/sample/match-search.html) gives current input `ABCQABCX` two sources: a nearer position matches 3 bytes, while an older one matches 7. It then explains quick rejection, search budgets and delaying a decision by one byte. Each optimization changes work or compression ratio while retaining the condition that the selected passage equals the input.

[References and input agreement](/sample/match-proof.html) checks that condition along the same process: moving bytes preserves their identity; candidate links still name the corresponding positions; a returned length does not exceed real input; and the strategy commits a match from the correct starting point. It also develops overlapping copies, because distance 2, length 6 is not a non-overlapping array copy.

## After symbols reach the encoder {#handoff}

Committing a match produces two kinds of data. Three record bytes save its distance and length offset for emission; frequency tables count the corresponding length and distance codes. A length-6 match does not become six literal counts. These are the statistics used by [Huffman coding](/verification/huffman.html). [Block encoding](/verification/output.html) keeps the record order and turns each record into fields the receiver can read.

Continue with the window to understand how arrays support search. Go directly to candidate search if references are familiar and you want to understand the tradeoffs. Follow references and input agreement to check why those tradeoffs preserve content. All three follow one handoff: **input becomes records, and independent expansion of those records recovers those bytes.**
