# zutil.c: function by function

Source: `zlib/zutil.c`, `zlib/zutil.h`. The allocators and the error strings are used by every
other file.

| Function | Statement | Argument |
| --- | --- | --- |
| `zcalloc(opaque, items, size)` | returns `malloc(items * size)` or null; the block is **not** zeroed (on LP64 it is `malloc`, not `calloc`) | `items * size` is computed in `unsigned` (32 bits) and wraps modulo 2^32. The proof must show that it does not wrap at any call site, otherwise the block is smaller than the code expects (§1) |
| `zcfree(opaque, ptr)` | `free(ptr)` | `ptr` is a block returned by `zcalloc` and not yet freed (ownership invariant) |
| `zError(err)` | returns `z_errmsg[(err) < -6 \|\| (err) > 2 ? 9 : 2 - (err)]` | the index is 0 to 9 for **every** `int` `err`; the table has 10 entries. Safe for any argument |
| `zlibVersion` | returns a constant string | none |
| `zlibCompileFlags` | returns a constant | none |

## The idea in short

Everything here is either a constant or a thin wrapper around `malloc` and `free`. The one thing to check is that the product of the two size arguments never wraps at 32 bits. The largest allocation in the whole library is 131,072 bytes.

## 1. The allocation sizes (U1, and the leak bookkeeping U12)

Every call of `ZALLOC(strm, items, size)` in the default build:

| Call site | `items` | `size` | Largest product |
| --- | --- | --- | --- |
| `deflateInit2_` state | 1 | `sizeof(deflate_state)` = 5,968 | 5,968 |
| `deflateInit2_` window | `w_size` (at most 32,768) | 2 | 65,536 |
| `deflateInit2_` prev | `w_size` | 2 (`sizeof(Pos)`) | 65,536 |
| `deflateInit2_` head | `hash_size` (at most 2^16) | 2 | 131,072 |
| `deflateInit2_` pending buffer | `lit_bufsize` (at most 32,768) | 4 (`LIT_BUFS`) | 131,072 |
| `inflateInit2_` state | 1 | `sizeof(inflate_state)` = 7,176 | 7,176 |
| `updatewindow` window | `1U << wbits` (at most 32,768) | 1 | 32,768 |
| `deflateCopy`, `inflateCopy` | the same as above | | the same |

All are far below 2^32. The sizes of the structures are constants of the LP64 layout; the
translation records them and a differential test checks them against the real compiler.

## 2. Allocation and ownership

With the default allocator, every `zcalloc` is a `malloc`. The runtime records, for each block, who
owns it. This gives the leak-freedom statement of [../safety.md](../safety.md) section 2: after a failed init,
the live blocks are the ones that existed before. In `deflateInit2_` there are five allocations, and the
code checks all four of the buffers together after the last one; if any is null it calls `deflateEnd`, which
frees the others. [deflate.md](deflate.md) section 6 states the exact obligation.

## 3. Status

Proved on paper. In the earlier attempt `zError`, `zcalloc`-related allocation lemmas and the five `zutil`
functions were classified as complete.
