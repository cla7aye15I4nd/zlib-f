# deflateCopy after deflateResetKeep: longest_match follows an uninitialised prev slot

`copy.c` runs `deflateResetKeep`, `deflate(Z_BLOCK)` and `deflateCopy`, then on the copy a `Z_RLE`
flush with no input and a default-strategy `deflate`. AddressSanitizer reports a
`heap-buffer-overflow` READ of size 1 in `longest_match` (`deflate.c:1511`), past the window of the
copy. `run.sh` builds zlib under ASan and UBSan and requires that report. `report.txt` is the raw
output of one run on arm64 macOS (process id replaced); the run on x86_64 Linux, the project's
target, is still to be done.

The history is outside the proved domain: a direct `deflateResetKeep` is not a deflate stream
operation ([deviations](../../../docs/deviations.md)). The analysis is in
[docs/findings/deflate-copy-pending-prev](../../../docs/findings/deflate-copy-pending-prev/README.md).
