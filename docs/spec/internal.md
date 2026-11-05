# Internal functions

What the functions inside the library promise to each other. These are not part of `zlib.h`.
The text comes from the C code and its comments. Every promise has an identifier, so that a proof
can cite it. A promise that the code does not check, and that its caller must meet, is marked
**caller** (the callee assumes it). The proofs show that each caller meets it.

## 1. `inflate_table` (inftrees.c)

Builds a two-level decoding table for a canonical Huffman code.

`inflate_table(type, lens, codes, &table, &bits, work)`

| Id | Statement |
| --- | --- |
| `I-it-pre-lens` **caller** | `lens[0 .. codes-1]` are readable and each is at most 15. For `type = CODES` each is at most 7 and `*bits` is 7 or more |
| `I-it-pre-codes` **caller** | `codes` is at most 19 for `CODES`, 288 for `LENS`, 32 for `DISTS` (the base and extra tables have that many entries) |
| `I-it-pre-work` **caller** | `work` has room for `codes` entries |
| `I-it-pre-table` **caller** | `*table` has room for 128 entries (`CODES`), 852 entries (`LENS`), or 592 (`DISTS`) |
| `I-it-ret` | returns 0 (table built), -1 (the lengths are over-subscribed, or incomplete and not the allowed single-code case), or 1 (the table would need more than 852/592 entries, `LENS`/`DISTS` only) |
| `I-it-writes` | writes only inside `[*table, *table + used)`, where `used ≤ 852` for `LENS`, `≤ 592` for `DISTS`, `≤ 128` for `CODES` |
| `I-it-advance` | on return 0, `*table` advances by `used` and `*bits` is the root index width |
| `I-it-complete` | on return 0 and a complete code, every entry in the table that was built is written. For an incomplete code (one symbol of length 1) the second root entry is written as an invalid marker |
| `I-it-links` | on return 0, a root entry that points to a sub-table has its offset and width such that the whole sub-table lies in `[*table, *table + used)` |
| `I-it-canonical` | the decoded symbol for a code is the one given by the canonical assignment ([format.md](format.md) section 2.4) |
| `I-it-term` | the call ends |

On return -1 or 1 the contents of the table are not specified; the caller does not use it.

## 2. `inflate_fast` (inffast.c)

The fast path of `inflate`, for the case with plenty of input and room.

| Id | Statement |
| --- | --- |
| `I-if-pre-room` **caller** | `avail_in ≥ 6` and `avail_out ≥ 258` |
| `I-if-pre-bits` **caller** | the state's `bits` is less than 8 |
| `I-if-pre-tables` **caller** | `lencode`, `distcode` point to tables built by `inflate_table` (or the fixed tables) with root widths `lenbits`, `distbits` |
| `I-if-pre-window` **caller** | `whave ≤ wsize`, `wnext < wsize`, and if `whave > 0` then `window` points to `wsize` bytes |
| `I-if-reads` | reads input only in `[next_in, next_in + avail_in)` |
| `I-if-writes` | writes output only in `[next_out, next_out + avail_out)` |
| `I-if-post` | on return, `next_in`, `next_out`, `avail_in`, `avail_out`, `hold`, `bits` describe the position after the last whole symbol; `bits` is less than 8; `mode` is `LEN`, `TYPE` (end of block) or `BAD` |
| `I-if-dist` | a back-reference farther than the output of this call plus `whave` makes the mode `BAD` |

## 3. `updatewindow` (inflate.c)

`updatewindow(strm, end, copy)` appends the last `copy` output bytes (the ones just before `end`)
to the sliding window.

| Id | Statement |
| --- | --- |
| `I-uw-pre` **caller** | `copy` is at most the number of bytes the current call has written before `end` |
| `I-uw-alloc` | allocates the window on first use; returns 1 if allocation fails, else 0 |
| `I-uw-inv` | afterwards `whave ≤ wsize`, `wnext < wsize`, and `whave < wsize` implies `wnext = whave` |
| `I-uw-content` | the window holds the last `min(whave, wsize)` bytes of output in ring order, ending at `wnext` |

## 4. `fill_window`, `slide_hash`, `read_buf` (deflate.c)

| Id | Statement |
| --- | --- |
| `I-fw-pre` **caller** | `lookahead < MIN_LOOKAHEAD`; `strstart + lookahead ≤ window_size` |
| `I-fw-post-room` | afterwards `strstart ≤ window_size - MIN_LOOKAHEAD`, or no more input is available |
| `I-fw-post-lookahead` | afterwards `lookahead ≥ MIN_LOOKAHEAD` or the input is exhausted |
| `I-fw-slide` | when `strstart ≥ w_size + MAX_DIST`, the upper half of the window moves down by `w_size`; `strstart`, `match_start`, `block_start` decrease by `w_size`; every `head` and `prev` entry decreases by `w_size`, or becomes 0 (`NIL`) if it would be negative |
| `I-sh-total` | `slide_hash` reads and rewrites every `head` and every `prev` entry once; the result for a given entry depends only on that entry |
| `I-rb-copy` | `read_buf(buf, size)` copies `min(avail_in, size)` input bytes to `buf`, updates `avail_in`, `next_in`, `total_in`, and updates the checksum for the wrapper |

## 5. Hash chains and `longest_match`

`I-hc-inv` (invariant, kept by `INSERT_STRING`, `slide_hash`, `CLEAR_HASH`, `fill_window`,
`deflateSetDictionary`):

1. every `head` entry is 0 (`NIL`) or a position that has been inserted, and is less than `strstart`
   plus the lookahead already hashed;
2. for every inserted position `p` that is within `MAX_DIST` of `strstart`, the entry
   `prev[p mod w_size]` has been written, and holds 0 or a smaller inserted position.

`I-lm-pre` **caller**: `cur_match < strstart` and `strstart ≤ window_size - MIN_LOOKAHEAD`.
`I-lm-reads`: reads window bytes only at indices below `strstart + 258`, and `prev` only at
indices that `I-hc-inv` says were written.
`I-lm-ret`: returns a length at most `lookahead`, and sets `match_start` to a position of a real
match of that length (or leaves it).
`I-lm-term`: the chain walk ends within `max_chain_length` steps, since the position strictly
decreases.

## 6. `trees.c`

| Id | Statement |
| --- | --- |
| `I-bt-pre` **caller** | `desc` describes one of the three trees, with `elems` 286, 30 or 19; `Freq` is set for symbols `0 .. elems-1` |
| `I-bt-heap` | every heap and tree index written is below `HEAP_SIZE = 573` (or the tree's own array size) |
| `I-bt-forest` | after building, the nodes form a full binary tree over the symbols that have a non-zero frequency, plus forced symbols so that there are at least two leaves; parents have a larger frequency than their children |
| `I-gb-len` | `gen_bitlen` sets `Len` to at most `max_length` (15, or 7 for the bit-length tree) for every leaf, with the Kraft sum equal to 1 |
| `I-gb-count` | `bl_count[l]` is the number of leaves of length `l`, for `l` from 1 to `max_length`; `bl_count[0]` is 0 |
| `I-gc-code` | `gen_codes` assigns the canonical code to each leaf, bit-reversed, with `next_code` indices at most 15 |
| `I-cb-reads` | `compress_block` reads the symbol buffer in order, from `sym_buf[0]` up to `sym_next` |
| `I-cb-pending` | after `compress_block` has finished emitting symbol number `k` (counting from 0), `pending < lit_bufsize + 3(k+1)`. This is the assertion that the C code states in the loop. The unread symbols start at byte `lit_bufsize + 3(k+1)`, so the pending output never reaches an unread symbol |
| `I-tf-choice` | `_tr_flush_block` writes a stored block if `stored_len + 4 ≤ opt_lenb`; else a fixed block if `static_lenb = opt_lenb`; else a dynamic block. Here `opt_lenb` is the smaller of the dynamic and fixed sizes |

`I-cb-pending` is the overlay lemma. [proof/deflate-overlay.md](../proof/trees.md)
proves it for the fixed block, and states what is known for the dynamic block.

## 7. `flush_pending` and the pending buffer

| Id | Statement |
| --- | --- |
| `I-fp-inv` | `pending_out + pending ≤ pending_buf + pending_buf_size` at all times |
| `I-fp-copy` | `flush_pending` copies `min(pending, avail_out)` bytes from `pending_out` to `next_out`, and advances both and `total_out`; when `pending` becomes 0, `pending_out` returns to `pending_buf` |
| `I-pb-room` | the writers (`put_byte`, `put_short`, `send_bits`) do not check the bound; `I-fp-inv` and `I-cb-pending` are what make them safe |
