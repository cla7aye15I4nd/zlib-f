# Repair caps: the 7-bit repair term of the bit-length tree

`repair_caps.py` generates the Lean case analyses `ZlibF/Math/RepairCap13*` and
`ZlibF/Math/RepairCap15*`. They are part of the TinyOverlay header bound (batch 1, H2b). The
script finds nothing by search: it enumerates every histogram and writes one small lemma per
case. The Lean kernel checks every lemma; the script is not trusted.

## What is proved

`repairExtra_cap13` (and `repairExtra_cap15`): for a clamped bit-length histogram `c` with the
shape the first pass of `gen_bitlen` leaves at the limit 7 (`RepairShape`: no leaf at level 0,
none above 7, `N` leaves, clamped Kraft sum `128 + M`, at least `M + 1` leaves at level 7),
`M ≥ 1`, at most 13 (15) leaves, a tree weight `W ≤ 316`, and ranks that obey their Fibonacci caps
`w r ≤ (W − F(d))/F(d+1)` (`RankCaps`, `d` the `r`-th smallest clamped depth):

    repairExtra 7 w M c ≤ 29 + W / 2        (at most 13 leaves)
    repairExtra 7 w M c ≤ 245               (at most 15 leaves)

`repairExtra` is the sum of the weights of the ranks that the `M` repair steps lengthen
(`ZlibF/Math/HuffmanRepairCost.lean`). The caps come from `LeafRank.fib_bound` through
`rank_cap` (`ZlibF/Math/HuffmanRepairCap.lean`); the use on the tree `build_tree` returns is in
`ZlibF/Proof/trees.c.build.rank-cap.lean`.

## The case analysis

There are 164 histograms with at most 13 leaves and 535 with at most 15. For each, a lemma
computes the moved ranks and their depths by `rfl` and closes the inequality in `W` with `omega`
(the divisors are literals). A tree of case-split lemmas covers every histogram: each node splits
the next count by `omega`. The script checks every bound for every `W ≤ 316` before writing;
both bounds are tight (slack 0 at `c = [0,1,1,1,1,1,1,7]`, `W = 309`, and
`c = [0,1,1,1,1,1,1,9]`, `W = 313`). The modules hold at most 60 lemmas each and build in a few
seconds with under 1.5 GB.

## Tests

`regenerate-caps.sh` regenerates both case analyses and compares them with the repository.
