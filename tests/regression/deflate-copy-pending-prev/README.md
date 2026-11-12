# deflateCopy after deflateResetKeep: longest_match follows an uninitialised prev slot

`copy.c` runs `deflateResetKeep`, `deflate(Z_BLOCK)` and `deflateCopy`, then on the copy a `Z_RLE`
flush with no input and a default-strategy `deflate`. `run.sh` checks two reports:

- zlib built under ASan and UBSan, with an allocator that fills fresh memory with the 16-bit value
  1030: AddressSanitizer reports a `heap-buffer-overflow` READ of size 1 in `longest_match`
  (`deflate.c:1511`), past the window of the copy.
- When valgrind is installed, zlib built without sanitizers and `copy plain` (default allocator):
  memcheck reports a conditional jump on an uninitialised value in `longest_match`
  (`deflate.c:1555`, the loop test on the next candidate), created by the `prev` allocation of
  `deflateCopy` (`deflate.c:1362`).

`report.txt` is the raw output of one run on x86_64 Linux, the project's target (GCC 14, process
ids replaced, paths relative to the repository or the zlib root). An earlier run on arm64 macOS
gave the same AddressSanitizer report.

The history is outside the proved domain: a direct `deflateResetKeep` is not a deflate stream
operation ([deviations](../../../docs/deviations.md)). The analysis is in
[docs/findings/deflate-copy-pending-prev](../../../docs/findings/deflate-copy-pending-prev/README.md).
