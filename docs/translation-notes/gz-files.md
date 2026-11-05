# gz*.c, gzclose.c, uncompr.c: the Lean translation and its file model

Files: `ZlibF/Zlib/gzguts.h.lean` (header content and helpers), `gzlib.c.lean`, `gzread.c.lean`, `gzwrite.c.lean`,
`gzclose.c.lean`, `uncompr.c.lean`, and `gzfs.lean` (the model of the C library calls). Source: the verified source
(`zlib/` plus `patches/*.patch`; no patch touches these files). Configuration: default x86_64 Linux, with
`STDC`, `STDC99`, `HAVE_VSNPRINTF`, `_LARGEFILE64_SOURCE`, `O_CLOEXEC`, `O_NONBLOCK`, `O_EXCL`, `O_LARGEFILE` (0)
defined (checked with `gcc -dM -E`), and `WIDECHAR`, `UNDER_CE`, `NO_GZCOMPRESS`, `NO_snprintf`, `NO_vsnprintf`,
`O_BINARY` undefined. So `gz_strwinerror`, the `fd == -2` branches, the `#ifndef O_EXCL` block, and the old-style
`gzprintf` (twenty `int` arguments) are not translated.

## 1. The external world is trusted base: `gzfs.lean`

The runtime heap has no file system, no `errno` and no `printf`. `gzfs.lean` adds them without touching `Runtime/`.

* **Monad.** `G α = StateT Fs C.M α`. A heap computation lifts into `G`; a fault is still `Fault.ub`. The world `Fs`
  is a record beside the heap (not part of `Heap`).
* **Files.** Paths are flat byte strings (no directories); a node is a byte array or a directory marker. An open file
  description has a node, a position, read/write/append flags. Descriptors are numbered from 3, lowest free first.
  `fsOpen`, `fsRead`, `fsWrite`, `fsLseek`, `fsClose` set `errno` (ENOENT, EBADF, EEXIST, EISDIR, EINVAL, EFBIG,
  EOVERFLOW) and return `-1` as the system call does. `fsFcntl` does nothing.
* **Printf.** `formatBytes`/`vsnprintf` implement `%%`, `%c`, `%s`, `%d`, `%i`, `%u`, `%x`, `%X`, `%o` with flags
  `-0+ #`, width, precision and the length modifiers `l`, `ll`, `z`, `j`, `t`. The variadic arguments are a list
  `VaArg` (`int`, `uint`, `long`, `ulong`, `str`). `strerror` is a table of the glibc texts of the errno values the model
  can produce.
* **String literals** are fresh read-only blocks (`strLit`), as in `zutil.c.lean`.

### Narrowings (each one is a place where the model is smaller than the C library)

| # | Narrowing | Consequence |
| --- | --- | --- |
| N-1 | Only regular files and directories. No pipes, sockets, terminals | `read` never returns less than asked except at end of file, never `EAGAIN`; `state->again` is never set by the model (the code that handles it is translated and not reached by the tests) |
| N-2 | `O_NONBLOCK`, `O_CLOEXEC`, `O_LARGEFILE` and the `fcntl` calls do nothing | as N-1 |
| N-3 | Permissions, ownership, parent directories, symbolic links, file locking are not modelled | `open` never fails with `EACCES`, `ENOTDIR`, `ELOOP` |
| N-4 | Write failures come from one source: the size limit `fsizeLimit` (like `RLIMIT_FSIZE` with `SIGXFSZ` ignored): a write that crosses the limit is short, a write at the limit fails with `EFBIG` | no `ENOSPC`, `EIO`, `EINTR` |
| N-5 | `printf` conversions other than the list above (`%f`, `%p`, `%n`, `%*d`, `%hd`, `%ls`) are a fault | the C library accepts them |
| N-6 | Wrong argument kinds and too few arguments for a conversion are a fault (they are undefined in C) | `%d` needs `int`, `%ld` `long`, `%s` a pointer (NULL prints `(null)`), unsigned conversions accept `int` or `unsigned` |
| N-7 | `read`/`write` of a buffer outside its object is a fault (the C gives `EFAULT` or crashes) | |
| N-8 | `lseek` results above `2^63 - 1` are `EOVERFLOW`; seeking past the end is allowed, a later write zero-fills | as Linux |
| N-9 | A pointer to a scalar (`int *errnum`, `z_size_t *destLen`, `uLong *sourceLen`) is a pointer to a 4 or 8 byte block, little endian (`load32`, `store64`, ...), because the runtime has no pointer to a single cell | the driver passes such blocks |
| N-10 | `unsigned *have` of `gz_load` is returned by the function and stored by the caller right after the call | `gz_load` never observes its aliased cell, so the order of effects is the same |
| N-11 | `memchr` (`memchrB`) reads only the bytes up to the first match and faults if one of them is outside the object | as the C library |
| N-12 | `storeBytes` (the bytes a `read` or `vsnprintf` writes) is one block copy, not a store per byte | same result; avoids a deep heap function in the interpreter |

## 2. Decisions in the translation

* `gzFile` is `GzFilePtr` (`some (.in_gzstate_x id)`), `gz_statep` is `GzStatePtr` (`some (.tab id)`), `(gz_statep)file`
  is `castState`, `&state->strm` is `strmOf`. A field write is a load, a record update and a store.
* Locals whose address is taken (`unsigned char buf[1]`, `z_stream stream`, `got`, `used`, `stream.reserved`) are
  blocks made by the runtime allocators outside the allocation oracle (`allocLocal`, `allocLocalZ`) and freed before every
  return.
* Signed arithmetic on `z_off64_t` is checked (`i64add`, `i64sub`, `i64neg`: overflow is `Fault.ub`).
* `GT_OFF(x)` is `(sizeof(int) == sizeof(z_off64_t) && (x) > gz_intmax())`, which is false (4 != 8); `gz_intmax` is
  not called.
* A `return` inside a loop is a control tag in the loop state (`Option Int32`); `break`/`continue` likewise.
  `continue` in `gz_read` skips the progress update and goes to the loop condition, as in C.
* `inflateInit2(&strm, 15 + 16)`, `deflateInit2(...)`, `inflateInit(&stream)` pass `ZLIB_VERSION` as a literal block and
  `sizeof(z_stream) == 112`.
* `gzprintf` takes the variadic list; `gzvprintf` is the same function (`va_list`).
* `gzgetc` is the function (the macro of `zlib.h` is for the application).

## 3. Places that need a patch, kept as in the unpatched C

The workspace has no patch for these files. The translation is the unpatched C, so each of these is a `Fault.ub`
(or the C behaviour) where the earlier repository patched:

| Id | Function | What | Earlier fix |
| --- | --- | --- | --- |
| R-1 | `gzseek64` | signed overflow with a negative `x.pos` (after `gzungetc` right after `gzopen`) and near `GZ_OFF_MAX` | `0004`, upstream PR 1361 |
| R-2 | `gz_fetch`, `case COPY` | `x.next` is set after `gz_load`; a failing `read` that returned data leaves `x.have != 0` with a stale `x.next` | `0002`, upstream PR 1363 |
| R-3 | `gz_reset` | `x.next` not written; a fresh state has `x.next = NULL` in the model, so `x.next += 0` is `NULL + 0` (allowed) and does not fault | `ub.patch` hunk |
| R-4 | `gz_read` direct decompression | `x.next` points into the user's buffer after the call; `Ptr.add` on it faults once the buffer is freed | proposed, not applied |

The tests avoid these: no `seek` after `ungetc` at the start of a file, no failing `read` after data, no freed user
buffer.

## 4. Candidate finding (not confirmed): `gzsetparams` ignores `deflateParams`

`gzsetparams` (`gzwrite.c`) calls `deflateParams(strm, level, strategy)` and ignores its result. `deflateParams` returns
`Z_BUF_ERROR` and keeps the old parameters when the block flush it needs does not fit in `avail_out`, but `gzsetparams`
still stores the new `state->level` and `state->strategy` and returns `Z_OK`. Reproduction idea: write `n` pseudo-random
bytes with `"wb6"`, call `gzsetparams(f, 0, 0)`, write 200000 zero bytes; for some `n` (those that leave the 8192-byte
output buffer almost full) the file is about `n` bytes instead of `n` plus the stored size of the zeros, so level 0 was
not applied. The data stays valid; only the level is wrong. This is from the notes of the `gz` side; it has not been
reproduced in this workspace. Unconfirmed: it goes to `docs/TODO.md` §4, not to the findings.

## 5. Differential tests

`tests/c/gz.c`, `tests/lean/Driver/Gz.lean`, `tests/gen/gz.py`, entry `gz` in `tests/list.txt`. A line is a scenario on
temporary files (`gz OP OP ...`, the ops are in `gen/gz.py`) or an `uncompress2` call (`unc HEX DESTLEN [SRCLEN]`). The C side
runs the real library on real files in a fresh directory (the output is built in memory so that `RLIMIT_FSIZE` does not
affect it); the Lean side runs the translation on the `Fs` model. Every op prints one token; the lines must be identical.
This is evidence of fidelity, not proof. The file model is part of what is tested only where the real C library and the
model are compared: the tests compare the gz layer and the model together against Linux.
