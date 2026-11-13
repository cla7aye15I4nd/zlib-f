# Deflate histories outside the documented call order

Four call histories on the real C. Each one is outside what zlib.h documents, and each one
makes the C read memory it must not read. Before the correction, `StreamReachable`, `StreamArguments`
and `ActiveHeader` (`ZlibF/Spec/Public/History.lean`) admitted all three, so `Goal.deflate` and
`Goal.deflate_sequence` were false for the real C (the fourth until a later correction).

| History | zlib.h | Sanitizer report |
| --- | --- | --- |
| `prime.c`: raw, `memLevel` 1; `deflate(Z_NO_FLUSH)` records symbols; 200 × `deflatePrime(16)`; `deflate(Z_FINISH)` | `deflatePrime` "must be used before the first deflate() call after a deflateInit2() or deflateReset()" | `trees.c`: index 767 out of bounds for `_dist_code[512]`; what follows depends on the byte read (macOS: a signed left-shift overflow; x86_64 Linux: a load with insufficient space) |
| `header.c 1`: gzip, `memLevel` 1, a 2000-byte extra field; the first `deflate` stops inside it; `deflateSetHeader(strm, NULL)`; `deflate` | `deflateSetHeader` "may be called ... before the first call of deflate()" | `deflate.c`: member access through a `NULL` `gz_header` |
| `header.c 2`: the same, then the caller sets `extra_len` to 10, below the 500 bytes written | the caller provides the header for the stream; shrinking it during writing is not documented | `deflate.c`: heap buffer overflow reading the extra field |
| `clear.c`: gzip, `memLevel` 1, a 1500-byte extra field and a 3-byte name; the first `deflate` stops inside the extra field; the caller sets `extra` to `NULL`; `deflate` | changing the header record during writing is not documented | `deflate.c:1177`: heap buffer overflow reading the name: the extra stage is skipped without resetting `gzindex`, and the name loop starts at `name[gzindex]` |

The pending buffer and the symbol buffer share one allocation (`sym_buf = pending_buf +
lit_bufsize`). `deflatePrime` in the pinned source checks only `pending_buf_size - pending`, so
after symbols were recorded the primed bytes overwrite them; the next block decodes a distance
of 65535 from the overwritten bytes.

The correction admits `deflatePrime` and `deflateSetHeader` only before the stream has started
(`DeflateNotStarted`: status `INIT_STATE` or `GZIP_STATE`, which every documented call order
satisfies), and requires at each `deflate` call that a non-`NULL` header still covers the part
already written, and that `gzindex` is 0 in `EXTRA_STATE`, `NAME_STATE` or `COMMENT_STATE` when that
field of the record is `NULL` (`DeflateHeaderProgress`). These are the documented call orders, not a narrower
domain. Confidence: high (reproduced with sanitizers). Scope: undocumented call orders only;
this is not a defect of zlib under its documented use.

```bash
ZLIB_SRC=$PWD/zlib bash tests/regression/deflate-history-domain/run.sh
```
