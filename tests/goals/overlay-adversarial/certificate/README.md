# The memLevel 2 overlay certificate

This directory holds the tools behind the `lit_bufsize = 256` (memLevel 2) case of the dynamic
overlay room (`TinyOverlayAt 256`). The proof is in Lean; these tools find the certificate and
test the statement on the real C. They are evidence and generators, not proof.

## What is proved

`ZlibF/Math/DeflateOverlayCertificate.lean`, theorem `certificate` (checked):

    71 + Σ_v entryCost(ll v) + Σ_v entryCost(dl v) + E ≤ 1852

for the code lengths `ll` (286 literal/length entries) and `dl` (30 distance entries) and the
actual frequencies of one block with at most 255 symbols. `E` is the excess per occurrence:
`x + e − 9` for a length code with `e` extra bits at length `x`, `x + e − 15` for a distance code.
`entryCost` is 2 for a zero length and `max(κ0[x], 3)` for a length `x`, where `κ0` is the
reference bit-length code `[2,7,7,5,5,4,4,4,4,3,4,4,7,7,7,7,7,3,7]`.

The facts it uses:

- Kraft in each tree: `Σ 2^(15 − x) ≤ 2^15` over the nonzero lengths;
- the Fibonacci bound for every used code: `f·F(x+1) + F(x) ≤ 258` and `1 ≤ x ≤ 15`;
- a code with a nonzero length and no occurrence has index ≤ 2 (zlib's forced leaves);
- the end-of-block frequency is 1, there are at most 255 symbols, and there are as many length
  codes as distance codes.

`ZlibF/Proof/trees.c.overlay-scan-cost.lean`, theorem `scan_cost_le` (checked): the bit-length
symbols that `scan_tree` counts, each at its `κ0` length plus extra bits, cost at most the entry
costs of the lengths.

So if the header is at most `71 + Δ + Σ_k f_k·(κ0_k + xbits_k)` (batch 1's reference-code bound,
`f` the bit-length frequencies), the header plus the excess is at most `1852 + Δ`. The budget is
`8·256 − 25 = 2023`, so the room holds when Δ ≤ 171.

## The certificate

`overlay_cert.py` solves a small linear programme over the multipliers (`lpsolve.c`, a dense
simplex): a Kraft multiplier per tree, a symbol multiplier, a balance multiplier, an allowance per
class of entries (by tree, kind and extra bits) and one per forced leaf. It rounds them to
multiples of 1/8, raises each allowance to the least value that makes every entry fit, and
checks every inequality again with exact rational arithmetic. With `--lean` it writes the Lean
replay: each class is a sixteen-case `omega` check (one case per length), and the shares are
summed with `mass` lemmas. No `decide` on a large term is used.

## Tests

- `regenerate.sh`: regenerates the Lean file and compares it with the repository copy.
- `check.sh` (with `ZLIB_SRC` set to the pinned zlib checkout): the statement test on the real C.
  `check.c` hooks `_tr_flush_block` after `build_bl_tree` (any block, dynamic or not), checks each
  fact above on the actual code lengths and frequencies, the scan bound, and the final bound, and
  searches for the tightest block. In about 940,000 blocks every fact held, with at least 609
  bits of slack against an earlier bound of 1892 (so at least 569 against 1852).
- `header_lp.py`: batch 1's first programme over length histograms, kept for comparison.
