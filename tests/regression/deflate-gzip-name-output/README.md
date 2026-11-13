# Deflate gzip header name outside the domain of Goal.deflate

Two caller layouts on the real C. In both, the name loop of `deflate()` (`deflate.c`, line 1177
of the pinned source) reads the gzip header name one byte at a time until its NUL. At the call
the name is a valid C string, but bytes the same call writes overwrite its NUL with a nonzero
byte, and the loop reads past the end of the buffer. zlib.h does not say whether either layout
is permitted.

| Case | Layout | Sanitizer report |
| --- | --- | --- |
| `output.c` | `head->name` is the caller's output buffer (1024 bytes, NUL at 505), `memLevel` 1 | `heap-buffer-overflow`: a 1-byte read just after the 1024-byte buffer |
| `pending.c` | `head->name` points into the stream's own `pending_buf` (NUL at `name[4]`) | `heap-buffer-overflow`: a 1-byte read just after `pending_buf` |

In `output.c`, each flush of the full `pending_buf` writes the 10 header bytes and the name bytes
already read to `next_out`, which reaches 10 bytes past the read position. The original NUL is
replaced by a name byte, and the loop runs off the buffer. In `pending.c`, the header byte `OS`
is written over the NUL; the loop then reads to the end of `pending_buf`.

The comment loop is the same code. The extra field needs no such clause: its reads are bounded
by `extra_len`, so an overwrite only changes the bytes copied, which is defined.

`Goal.deflate` states the caller domain as `DeflateHeaderApart`, a conjunct of `ActiveHeader`
(`ZlibF/Spec/Public/History.lean`): while `deflate` writes an attached gzip header, the input, the
output, the extra field, the name and the comment (each string through its NUL) are pairwise
separate byte ranges, and the extra field, name and comment lie outside the storage the stream
owns. Both layouts above violate it. Listed in [deviations](../../../docs/deviations.md). The Lean
regression `tests/verification/regressions/deflate-gzip-name-output.lean` checks that the
layout of `output.c` violates the clause.
Confidence: high (both reproduced with sanitizers on the pinned source). Scope: a caller
`gz_header` whose name or comment overlaps `next_out .. next_out + avail_out` or `pending_buf`
while `deflate` still has to read it.

```bash
ZLIB_SRC=$PWD/zlib bash tests/regression/deflate-gzip-name-output/run.sh
```
