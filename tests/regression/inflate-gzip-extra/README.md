# Inflate gzip extra field outside the dispatch theorem's domain

Two caller layouts on the real C. In both, `case EXTRA` of `inflate()` copies the gzip extra
field into the caller's `head->extra` with `zmemcpy` (`inflate.c`, line 626 of the pinned
source), and the copy is undefined behaviour. zlib.h does not say whether either layout is
permitted.

| Case | Layout | Sanitizer report |
| --- | --- | --- |
| `overlap.c` | `head->extra` points into the input buffer and overlaps the extra field being read | `memcpy-param-overlap` in `inflate` |
| `shrink.c` | `extra_max` is `2^32 - 1`; the first call stops inside the extra field; the caller then sets `head->extra_len` to 0 | `heap-buffer-overflow`: a 4-byte write at the end of the 4294967295-byte buffer |

In `shrink.c`, `len = extra_len - state->length` wraps to `2^32 - 4`, still below `extra_max`, and
the guard `len + copy > extra_max` wraps to `0 > extra_max`, so all four bytes are copied from
`extra + 2^32 - 4`. With an unchanged record, `len + copy` never exceeds `extra_len`, which is at
most 65535.

The translation faults in the same places (`memcpyB` checks overlap and bounds). The gzip header
dispatch theorem `inflate_dispatch_gzip_header_rank` therefore assumes that the extra buffer is
separate from the unread input (`ExtraApart`) and that, in `EXTRA`, the record's `extra_len` is
not below the remaining length. Both are listed in [deviations](../../../docs/deviations.md).
Whether `Goal.inflate` keeps them as caller-domain clauses is the inflate owner's decision.
Confidence: high (both reproduced with sanitizers on the pinned source). Scope: a caller
`gz_header` whose extra buffer overlaps `next_in`, or whose `extra_len` the caller lowers while
inflate is inside the extra field. The name and comment buffers may overlap the input: they are
written byte by byte, which is defined and is covered by the theorem.

```bash
ZLIB_SRC=$PWD/zlib bash tests/regression/inflate-gzip-extra/run.sh
```
