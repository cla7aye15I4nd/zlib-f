# Targeted adversarial blocks for the dynamic overlay room (fact F9)

This test complements `tests/goals/overlay`. Both look for an overwritten symbol in a dynamic
block at a small `memLevel`, and both use the real `_tr_tally` and `_tr_flush_block`.
`tests/goals/overlay` anneals over symbol sequences. This test constructs blocks instead.

## How the blocks are built

- For a fixed multiset of symbols, the worst order puts the symbols in decreasing dynamic cost.
  The tightest prefix room is then `8 * lit_bufsize - 25 - H - E`. Here `H` is the header bits
  after the 3-bit tag, and `E` is the total excess `sum(max(0, d_i - 24))`.
- `adversarial.c` therefore searches over histograms, not sequences. A histogram has
  literal counts, length-code counts and distance-code counts.
- The seeds are built analytically:
  - Many distinct literals, spaced to make the zero runs in the header costly.
  - A few far matches on rare codes, which give a large excess.
  - Copies of one cheap match. Their gain pays for the header, so the dynamic branch is still
    chosen.
- In each block, long length codes are paired with long distance codes, and the symbols are
  ordered by decreasing cost.

## What the run checks

`run.sh` does the following:

1. Builds the patched zlib copy.
2. Instruments `trees.c` the way `tests/goals/overlay` does. A hook also records the header
   size and the code lengths.
3. Compiles with AddressSanitizer and UndefinedBehaviorSanitizer.
4. Replays the saved tightest blocks in `cases/`.
5. Runs the search at `memLevel` 1 and 2.

A negative gap means a symbol was overwritten before it was read. The program then prints the
block and exits 1.

The saved cases are `dist lc` pairs, one per line, as recorded by `_tr_tally`:

| Case | Origin | Worst-order room | Smallest gap |
| --- | --- | --- | --- |
| `cases/memlevel1-room266.txt` | this search | 266 bits | 37 bytes |
| `cases/memlevel1-anneal-room296.txt` | `tests/goals/overlay`-style annealing | 296 bits | 40 bytes |
| `cases/memlevel2-room1023.txt` | this search | 1023 bits | 131 bytes |

## Run

```bash
ZLIB_SRC=$PWD/zlib bash tests/goals/overlay-adversarial/run.sh 300000 2
```

## Results

Results on 2026-11-12, with 3,000,000 rounds per seed: 24 seeds at `memLevel` 1 and 12 seeds at
`memLevel` 2, under both sanitizers.

- No negative gap, and no sanitizer report.
- At `memLevel` 1 the best worst-order room was 266 bits, with header 645 and excess 88. The
  smallest gap was 37 bytes.
- At `memLevel` 2 the best was 1023 bits. The smallest gap was 131 bytes.

This is evidence about the blocks visited, not a proof.

## Header and excess programme

`certificate/header_lp.py` bounds `H + E` over relaxed histograms of code lengths. Build the
solver first with `cc -O2 -o certificate/lpsolve certificate/lpsolve.c`.

The variables are, per length class, the code count and the occurrence count. They are taken
separately for literals, for length codes by extra bits, and for distance codes by extra bits.

The constraints:

- Kraft ≤ 1 for each tree;
- the number of codes in each class;
- `c ≤ F ≤ c * fmax(x)`, the Fibonacci frequency bound;
- `Σ F ≤ lit_bufsize - 1`;
- the counts of zero runs and of zeros.

The header is bounded by the cost under complete reference bit-length codes `κ`, added as
cutting planes. The excess is bounded per occurrence.

The solution is a numerical bound, not a proof. A Lean proof needs these facts:

- the bit-length cost of zlib is at most `Σ f κ + Δ`, where `Δ` is the excess of the 7-bit repair
  over Huffman;
- the scan facts;
- one linear combination of the constraints.

Results on 2026-11-12, without `Δ`:

| Run | Bound | Budget |
| --- | --- | --- |
| `256 0 nochoice` | 1839 | 2023 |
| `256 0 nochoice`, single reference code | 1863 | 2023 |
| `128 0 choice` | 1020 | 999 (open) |
