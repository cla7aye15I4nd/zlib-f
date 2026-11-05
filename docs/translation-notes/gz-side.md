# Translation notes: `gzlib.c`, `gzread.c`, `gzwrite.c`, `gzclose.c`, `gzguts.h`

Analysis for the people who translate the `gz*` layer. It reads the C; it contains no proofs. Where a reading of the C
still has to be checked by a proof or a test it is marked **to confirm**. Facts were taken from the source and from
the output of the C preprocessor; some facts were also checked by running the real C (marked **run**; a run is
evidence, not proof). The deflate-side files are in [deflate-side.md](deflate-side.md), the inflate files in
[inflate-side.md](inflate-side.md). Sections 6 and 7 are a proposal (the model of the operating system and of
`va_list`), not facts about the C.

## 0. Source, line numbers, conventions

* Verified source: zlib commit `757f0527154291bcf6bfbd6396ecde6bedd2db95` (`ZLIB_VERSION "1.3.2.1-motley"`). The only
  patch in this workspace, `patches/0003-adler32-null-one.patch`, does not touch these files. **None of the four `gz*.c`
  files is patched in the workspace.** The earlier repository had three patches that do touch them: `0002`
  (`gz_fetch`, upstream PR 1363), `0004` (`gzseek64`, upstream PR 1361) and the `gz_reset` hunk of `ub.patch`. The live
  code **needs all three** for the `_safe` theorems of the functions named in section 2.4.
* **Line numbers are those of the original, unpatched files.** A line of the preprocessed file is `pp:` plus its number in
  the `gcc -E -P` output. "Lines" is the number of lines from the signature to the closing brace, comments and blank
  lines included.
* Configuration: default x86_64 Linux, LP64, `./configure --static` (`CFLAGS=-O3 -fPIC -D_LARGEFILE64_SOURCE=1
  -DHAVE_HIDDEN`; `configure` found `vsnprintf` with the C99 return value). Every `#ifdef` was decided by running
  `gcc -E -P -D_LARGEFILE64_SOURCE=1 -DHAVE_HIDDEN -DHAVE_UNISTD_H=1 -DHAVE_STDARG_H=1 -I <tree>` on each file and reading
  what is left (gcc 15.2, Ubuntu, glibc).
* Types: as in deflate-side.md. `z_off64_t` = `off64_t` = `long` = `Int64`; `z_off_t` = `off_t` = `long` (`sizeof` 8, **run**);
  `ssize_t` is `long`; `size_t`, `z_size_t` = `UInt64`; `gz_state` is 248 bytes (**run**).
* Names: `have`, `in`, `end` are Lean keywords: `have_`, `in_`, `end_` (renaming only). The C field names `x.have`, `x.next`, `x.pos`
  stay as record fields (`x` is a nested record `gzFile_s`).

### 0.1 Which branches of the C are live

| Macro | Value in the default build | Live / dead consequence |
| --- | --- | --- |
| `_LARGEFILE64_SOURCE` | defined, so `_LFS64_LARGEFILE` is true | `LSEEK` is `lseek64` (`gzlib.c` L12-13); `gzopen64`, `gzseek64`, `gztell64`, `gzoffset64` are the real functions and `gzopen`, `gzseek`, `gztell`, `gzoffset` wrap them (the prototypes at `gzguts.h` L156-161 are not compiled) |
| `O_CLOEXEC`, `O_NONBLOCK`, `O_EXCL`, `O_LARGEFILE` | defined; `O_LARGEFILE` is 0 on x86_64 glibc (**run**) | modes `'e'` (L132-136) and `'N'` (L155-159) are live; the `#ifndef O_EXCL` block (L195-201) is dead; `O_LARGEFILE \|` adds 0 |
| `O_BINARY` | undefined | its `#ifdef` (L238-240) is dead |
| `WIDECHAR`, `_WIN32`, `UNDER_CE`, `__DJGPP__` | undefined | `gzopen_w`, `gz_strwinerror`, the `fd == -2` paths (L204-211, L218-224, L254-257) are dead |
| `NO_GZCOMPRESS` | undefined | modes `'w'` and `'a'` live; `gzclose` (gzclose.c L12-19) picks `gzclose_r` or `gzclose_w` |
| `NO_snprintf`, `NO_vsnprintf` | undefined | `snprintf` is used at `gzlib.c` L227, L310, L583; the `strcpy`/`strcat`/`sprintf` alternatives (L229, L312, L586-588) are dead |
| `HAS_vsnprintf_void`, `NO_vsnprintf` + `ZLIB_INSECURE` | undefined | `gzvprintf` calls `len = vsnprintf(next, state->size, format, va);` (gzwrite.c L485) |
| `STDC`, `Z_HAVE_STDARG_H` | defined | the `va_list` version of `gzprintf` (L416-521) is live; the `int a1 ... a20` version (L523-635) is dead |
| `gz_vacate` guard (gzwrite.c L389-392) | true | `gz_vacate` is compiled |
| `STDC` for `<string.h>` etc. | defined | `strlen`, `memcpy`, ... are the libc functions |
| `NO_STRERROR` | undefined | `zstrerror()` is `strerror(errno)` (`gzguts.h` L135) |
| `UNDER_CE` | undefined | `zstrerror` is not `gz_strwinerror` |
| `EAGAIN`, `EWOULDBLOCK` | both 11 (**run**) | `BLOCKED(e)` is `((e) == EAGAIN \|\| (e) == EWOULDBLOCK)` (L143) |
| `INT_MAX` | defined (`<limits.h>`) | `gz_intmax()` returns `INT_MAX` = 2147483647 (L596-598) |
| `GT_OFF(x)` | `(sizeof(int) == sizeof(z_off64_t) && (x) > gz_intmax())`: `sizeof(int) == 4`, `sizeof(z_off64_t) == 8`, so the first operand is **constant false** | `gz_intmax` is never called (short-circuit); `GT_OFF(x)` is `0`. Used at gzlib.c L428, gzread.c L296, gzwrite.c L171 |
| `CHAR_BIT` | 8 (`<limits.h>`) | `GZ_OFF_MAX` = `((((z_off64_t)1 << 62) - 1) * 2 + 1)` = `2^63 - 1` (`gzguts.h` L238-239); no overflow in the intermediate |
| `_POSIX_C_SOURCE` | already defined by `<stdio.h>` (glibc) before `gzguts.h` L40 | no effect |
| `Z_PREFIX_SET` | undefined | `#undef gzgetc` (gzread.c L513) |
| `HAVE_HIDDEN` | defined | `ZLIB_INTERNAL` hidden; `gz_error` and `gz_intmax` are internal-linkage-like; no semantic effect |
| `Z_SOLO` | undefined | the `gz*` layer is compiled |

## 1. (a) All functions: lines, count, difficulty

"Tr" is the difficulty of the **translation**, "Pf" of the **proof**. easy = straight-line, a few field tests;
medium = several libc calls, a loop, pointer arithmetic, or an out-parameter; hard = a state machine over `how`, `again`,
`eof`, `err`, `skip` and several buffers, or `va_list`, or an arithmetic with a documented overflow history.

49 functions are compiled (18 in gzlib.c, 16 in gzread.c, 14 in gzwrite.c, 1 in gzclose.c). Not compiled: `gz_strwinerror`,
`gzopen_w` (Windows). The macros `gzgetc` (zlib.h) and `GT_OFF` are in section 5.

### gzlib.c (609 lines)

| Function | Lines | Count | Tr | Pf | Why |
| --- | --- | --- | --- | --- | --- |
| `gz_reset` (local) | L69-84 | 16 | easy | easy | field writes; calls `gz_error`; **does not set `x.next`** (R-3) |
| `gz_open` (local) | L87-290 | 204 (pp: 128) | medium | medium | `while (*mode)` over a caller string with a `switch` that returns; 8 `free` exits; `malloc`, `strlen`, `snprintf`, `open`, `fcntl`, `lseek64`; leak freedom on every early return |
| `gzopen` | L293-295 | 3 | easy | easy | `gz_open(path, -1, mode)` |
| `gzopen64` | L298-300 | 3 | easy | easy | same |
| `gzdopen` | L303-317 | 15 | medium | medium | `malloc(7 + 3 * sizeof(int))`, `snprintf("<fd:%d>")`, `free` after `gz_open` |
| `gzbuffer` | L327-348 | 22 | easy | easy | `(size << 1) < size` overflow test |
| `gzrewind` | L351-369 | 19 | easy | easy | `lseek64`, `gz_reset` |
| `gzseek64` | L372-439 | 68 | **hard** | **hard** | signed `z_off64_t` arithmetic with a negative position (R-1), three code paths, calls `gzrewind`, `gz_error`, `lseek64` |
| `gzseek` | L442-447 | 6 | easy | easy | cast and `ret == (z_off_t)ret` (always true) |
| `gztell64` | L450-462 | 13 | easy | easy | signed sum |
| `gztell` | L465-470 | 6 | easy | easy | |
| `gzoffset64` | L473-491 | 19 | medium | medium | `lseek64`; `offset -= state->strm.avail_in` |
| `gzoffset` | L494-499 | 6 | easy | easy | |
| `gzeof` | L502-514 | 13 | easy | easy | |
| `gzerror` | L517-532 | 16 | easy | easy | returns pointers to string literals or to `state->msg` |
| `gzclearerr` | L535-551 | 17 | easy | easy | |
| `gz_error` | L559-590 | 32 | medium | medium | `free`, `malloc(strlen + strlen + 3)`, `snprintf("%s%s%s")`; state change on allocation failure |
| `gz_intmax` | L596-609 (live L597-598) | 14 | easy | easy | `return INT_MAX` |

### gzread.c (727 lines)

| Function | Lines | Count | Tr | Pf | Why |
| --- | --- | --- | --- | --- | --- |
| `gz_load` (local) | L18-47 | 30 | medium | medium | `read` loop, `errno`, out-parameter `*have`, `BLOCKED` |
| `gz_avail` (local) | L56-82 | 27 | medium | medium | `do { *p++ = *q++; } while (--n)` overlapping forward copy inside one buffer; calls `gz_load` |
| `gz_look` (local) | L93-177 | 85 (pp: 58) | **hard** | medium | allocation of two buffers and `inflateInit2`, three outcomes, `memcpy` into the output buffer, header sniffing of four bytes |
| `gz_decomp` (local) | L187-247 | 61 (pp: 49) | **hard** | **hard** | `do ... while` with three `break`s and error mapping; pointer difference; writes `x.next` into whatever buffer `next_out` points to (R-4/D-13) |
| `gz_fetch` (local) | L255-289 | 35 (pp: 31) | medium | **hard** | `switch` inside `do ... while`, `break` leaves the switch only; stale `x.next` (R-2) |
| `gz_skip_have` (local) | L293-303 | 11 | easy | medium | `x.next += n` on a pointer that may be uninitialised (R-3) or dangling (D-13) |
| `gz_skip` (local) | L307-335 | 29 | medium | medium | `do ... while (state->skip)` with `if / else if / else` and a `break` |
| `gz_read` (local) | L343-422 | 80 (pp: 51) | **hard** | **hard** | `do ... while (len && !err)` with `break` and `continue` (the `continue` skips the progress update), four ways to get data, `got/len/buf` bookkeeping |
| `gzread` | L425-471 | 47 (pp: 28) | medium | medium | error ordering, `(int)len < 0` |
| `gzfread` | L474-507 | 34 | medium | medium | `nitems * size` overflow test, division |
| `gzgetc` | L515-544 | 30 (pp: 20) | medium | medium | local `unsigned char buf[1]`, `*(state->x.next)++` |
| `gzgetc_` | L546-548 | 3 | easy | easy | calls `gzgetc` |
| `gzungetc` | L551-615 | 65 (pp: 45) | medium | **hard** | backward slide of the output buffer, `x.pos` becomes negative, `x.next` pointer set at the end of `out` |
| `gzgets` | L618-681 | 64 (pp: 43) | medium | medium | `memchr`, `memcpy`, `if (left) do { ... } while (left && eol == NULL)` with uninitialised `eol` before the first iteration |
| `gzdirect` | L684-701 | 18 | easy | medium | calls `gz_look`, `gz_skip_have` (R-3) |
| `gzclose_r` | L704-727 | 24 (pp: 20) | medium | medium | frees; `inflateEnd`; `close` |

### gzwrite.c (735 lines)

| Function | Lines | Count | Tr | Pf | Why |
| --- | --- | --- | --- | --- | --- |
| `gz_init` (local) | L11-57 | 47 (pp: 35) | medium | medium | two `malloc`, `deflateInit2`, three failure exits that free |
| `gz_comp` (local) | L65-148 | 84 (pp: 66) | **hard** | **hard** | two loops with `return -1`, pointer **relational** comparison `next_out > x.next` and difference, `write` loop that must make progress, `deflate` loop `do ... while (have)` |
| `gz_zero` (local) | L154-193 | 40 (pp: 30) | medium | medium | `do ... while (state->skip)`, `memset`, calls `gz_init`, `gz_comp` |
| `gz_write` (local) | L199-267 | 69 (pp: 53) | **hard** | **hard** | `for (;;)` with `break`, pointer difference `(next_in + avail_in) - in`, two paths (copy / direct) that leave `strm.next_in` pointing into the user's buffer until reset |
| `gzwrite` | L270-292 | 23 | easy | easy | |
| `gzfwrite` | L295-319 | 25 | easy | medium | overflow test and division |
| `gzputc` | L322-362 | 41 (pp: 30) | medium | medium | local `unsigned char buf[1]` passed to `gz_write` |
| `gzputs` | L365-387 | 23 | easy | medium | `strlen(s)`; `(int)len < 0 \|\| (unsigned)len != len` |
| `gz_vacate` (local) | L398-413 | 16 | medium | medium | pointer **relational** comparison, `memmove` |
| `gzvprintf` | L420-511 | 92 (pp: 46) | **hard** | **hard** | `va_list`, `vsnprintf` into the input buffer, buffer-room invariants |
| `gzprintf` | L513-521 | 9 (pp: 8) | medium | easy | `va_start` / `va_end` |
| `gzflush` | L638-662 | 25 | easy | easy | |
| `gzsetparams` | L665-699 | 35 (pp: 24) | medium | medium | ignores the result of `deflateParams` (section 10, item 1) |
| `gzclose_w` | L702-735 | 34 (pp: 26) | medium | medium | `gz_zero`, `gz_comp(Z_FINISH)`, `deflateEnd`, three `free`, `close` |

### gzclose.c (23 lines)

| Function | Lines | Count | Tr | Pf | Why |
| --- | --- | --- | --- | --- | --- |
| `gzclose` | L11-23 | 13 (live L13-19) | easy | easy | dispatch on `mode` |

## 2. (b) Undefined behaviour and sites that need a decision

Classes as in [inflate-side.md](inflate-side.md): **R** = a call that `zlib.h` allows reaches UB in the C; **P** = UB only if the
caller breaks a precondition; **I** = the C is correct only because an invariant excludes it; **D** = defined behaviour that
needs a model decision. The translation raises `Fault.ub` at R, P, I.

### 2.1 Class R

| Id | Site | What | Handled by |
| --- | --- | --- | --- |
| R-1 | `gzlib.c` L393-399 (`gzseek64`), L403, L424, L437 | after `gzungetc()` right after `gzopen()`, `x.pos` is `-1`. Then `pos = x.pos + (past ? 0 : skip)` can be negative and `GZ_OFF_MAX - pos` is `2^63` = signed overflow (L395), and `pos - state->x.pos` (L403, L424) overflows for `pos` near `GZ_OFF_MAX`. Reproduced by the earlier repository with UBSan | `0004` (upstream PR 1361): `if (pos > 0 && offset > GZ_OFF_MAX - pos)` and `if (state->x.pos < 0 && pos > GZ_OFF_MAX + state->x.pos) return -1;`. **Needed for `gzseek64`, `gzseek`** |
| R-2 | `gzread.c` L271-276 (`gz_fetch`, `case COPY`) | `gz_load(state, state->out, ..., &(state->x.have))` writes `x.have` while it runs. If `read` returns some bytes and then fails with a non-blocking-unrelated error, `gz_load` returns `-1` **with `x.have != 0`** and `x.next` has not been set yet (`state->x.next = state->out` is after the call). The callers see `x.have != 0` and copy from the stale `x.next` (gz_read L369, gzgets L661-666, gz_skip_have L300): an overread. Reproduced with ASan in the earlier repository | `0002` (upstream PR 1363): `state->x.next = state->out;` moved **before** `gz_load`. **Needed for `gz_fetch`, `gz_read`, `gz_skip`, `gzgets`, `gzread`, `gzfread`, `gzgetc` and every reader** |
| R-3 | `gzlib.c` L431 (`gzseek64`, read mode: `state->x.next += n`) and `gzread.c` L300 (`gz_skip_have`, reached from `gzdirect` L696) | `gz_open` mallocs the state and never writes `x.next`; `gz_reset` sets `x.have = 0` but not `x.next`. With `n == 0` (nothing buffered) the code still computes `x.next += 0` on an indeterminate pointer. Reachable with documented calls: `gzopen(r)` then `gzseek(f, 0, SEEK_CUR)`, or `gzdirect(f)` right after `gzopen`. No observable effect, so the earlier repository removed it | `ub.patch` hunk: `state->x.next = Z_NULL;` after `state->x.have = 0;` in `gz_reset` (so the `+= 0` is `NULL + 0`, allowed by the model). **Needed for `gz_reset` callers: `gzseek64`, `gzdirect`** (in the heap model reading an uninitialised pointer is a fault) |
| R-4 | `gzread.c` L236 (`gz_decomp`: `state->x.next = strm->next_out - state->x.have`) with `gz_read` L401-407 (direct decompression into the user's buffer), then `gz_skip_have` L300 or `gzseek64` L431 later | after a `gz_read` that decompressed straight into the user's buffer, `x.have` is set back to 0 but `x.next` keeps pointing into the user's buffer. The user may free that buffer; a later `gzseek` or `gzdirect` evaluates `x.next += 0` on a pointer to a dead object (formally an indeterminate value, C17 6.2.4p2). No observable effect | **not patched** (the earlier repository did not report it). Options: (i) the model allows `p + 0` on a pointer to a freed block (no dereference); (ii) an `ub.patch` hunk `state->x.next = Z_NULL;` after `state->x.have = 0;` at gz_read L406. Recommended: (ii), the same class as the `gz_reset` hunk. See also D-13 |

### 2.2 Class P: caller preconditions that the C does not check

| Id | Site | Precondition |
| --- | --- | --- |
| P-1 | every `gz*` function taking a `gzFile` | `file` is `NULL` or a pointer returned by `gzopen`/`gzdopen` and not yet closed (the mode field is read to validate, which is itself a read of freed memory after `gzclose`). `gzclose` frees the state: use after close is UB |
| P-2 | `gzlib.c` L94 `gz_open` | `path` and `mode` are NUL-terminated (`strlen(path)` L212, `*mode` L111). `gzdopen(fd, mode)` L307: `mode` NUL-terminated |
| P-3 | `gzread.c` L343-422, L425 | `buf` points to at least `len` writable bytes; for `gzfread` `size * nitems` bytes; for `gzgets` `len` bytes |
| P-4 | `gzwrite.c` L199-267, L270 | `buf` points to at least `len` readable bytes; `gzputs` `s` is NUL-terminated (L380) |
| P-5 | `gzwrite.c` L420-511 `gzvprintf` | the `format` and the arguments agree (types, count); `format` is NUL-terminated; `%n` writes through a pointer argument |
| P-6 | `gzlib.c` L307 `gzdopen` | `fd` is a valid open descriptor; the caller does not close it and does not use it for I/O while the `gzFile` exists (not UB in the C; an assumption of the oracle model) |
| P-7 | `gzwrite.c` L77, L82 etc. | the `gzFile` is used by one thread at a time |
| P-8 | `gzlib.c` L442-447 `gzseek` | none (the cast `ret == (z_off_t)ret` is always true on LP64) |
| P-9 | all | no `gzFile` function may be called from inside a custom allocator (not applicable: the default allocator is used) |

### 2.3 Class I: sites excluded by an invariant (obligations for the proofs)

| Id | Site | What must hold |
| --- | --- | --- |
| I-1 | `gzwrite.c` L110 `strm->next_out > state->x.next` and L113-114 `strm->next_out - state->x.next` | both pointers lie in `state->out` (size `size`): `out <= x.next <= next_out <= out + size`. The model faults on a relational comparison of pointers into different blocks |
| I-2 | `gzwrite.c` L403 `strm->next_in + strm->avail_in <= state->in + state->size` | `next_in` points into `state->in` (block of `2 * size` bytes) **or is NULL (tested first, L402)**; it must not point into the user's buffer at this point. It does not: L258 and L262 reset it after every direct write, L178 and L188 after `gz_zero` |
| I-3 | `gzwrite.c` L223-224 and L348 `(next_in + avail_in) - state->in` | `next_in` in `in` (it is set to `in` when `avail_in == 0`, L221-222, L346-347), result `<= 2 * size` and, at L225, `<= size` (**to confirm**: `gzvprintf` leaves `avail_in` at most `size`, L494-509, because `gz_vacate` runs after it) |
| I-4 | `gzwrite.c` L225 `copy = state->size - have` | `have <= size` (I-3). With `have > size` the `unsigned` subtraction wraps |
| I-5 | `gzwrite.c` L470-471 `next = ...; next[state->size - 1] = 0;` and L485 `vsnprintf(next, state->size, ...)` | `next + size <= in + 2 * size`, i.e. the first half-plus is free: `gz_vacate` (L455) returned 0, or `state->err != 0` caused a return (L456-467). If `gz_vacate` returned 1 and `state->err == 0` the write at `next[size - 1]` could be out of the block; the code shows `ret == 1` implies `gz_comp` failed and set `err` (**to confirm**) |
| I-6 | `gzread.c` L605 `src > state->out` | `src` points into `out` (it is `out + x.have`) |
| I-7 | `gzread.c` L67 `q != p` (equality only) | none (equality is defined) |
| I-8 | `gzread.c` L236 `strm->next_out - state->x.have` | `x.have <= had - avail_out <=` the number of bytes written starting at `next_out`'s old value; the result stays in the buffer |
| I-9 | `gzread.c` L172 `memcpy(state->x.next, strm->next_in, strm->avail_in)` | `avail_in <= size < 2 * size` (the `out` buffer is double-sized, L100) and the two blocks differ |
| I-10 | `gzread.c` L76 `state->size - strm->avail_in`, L75 `state->in + strm->avail_in` | `avail_in <= size` |
| I-11 | `gzread.c` L586 `state->out + (state->size << 1) - 1` | `size != 0` when reached (L569-571 returns when the error is serious and `size == 0`; `gz_look` at L562-563 allocates when `how == LOOK`) and `size << 1` does not wrap (`gzbuffer` L342-343 rejects `size >= 2^31`; default `want` is 8192) |
| I-12 | `gzlib.c` L342 `(size << 1) < size` | detects a wrap of `size << 1` in `unsigned`: intended wrap |
| I-13 | `gzread.c` L99-100, `gzwrite.c` L16, L25 `malloc(state->want << 1)` | `want << 1` does not wrap (I-12) |
| I-14 | `gzread.c` L30 `read(state->fd, buf + *have, get)` | `buf + *have + get <= buf + len` (the buffer has `len` bytes): `get = min(len - *have, 2^30)` |
| I-15 | `gzlib.c` L403, L424, L437 and every `x.pos += n`, `x.pos--`, `x.pos -= len`: gzread.c L301, L413, L538, L588, L612; gzwrite.c L181, L230, L254, L352, L495, L502; gzlib.c L432 | `x.pos` stays in `[-1, GZ_OFF_MAX]`: a signed `Int64` that would need `2^63` bytes to overflow; the theorem states `x.pos + 2^32 <= GZ_OFF_MAX` (unreachable in practice; **narrower than a program-level guarantee, to list as a precondition**) |
| I-16 | `gzlib.c` L461 `state->x.pos + (state->past ? 0 : state->skip)` | the sum does not overflow (follows from `pos <= GZ_OFF_MAX`, which `gzseek64` checks) |
| I-17 | `gzlib.c` L489 `offset -= state->strm.avail_in` | `offset` came from `lseek64` (`>= 0`), so the result `> -2^32`; no overflow |
| I-18 | `gzlib.c` L428-433 `(unsigned)offset` | `0 <= offset < x.have` (the other branch of the conditional), so the cast is exact |
| I-19 | `gzread.c` L296-302 and `gz_skip_have` | `n <= x.have` and `n <= skip`, so `x.have -= n` and `skip -= n` do not wrap |
| I-20 | `gzwrite.c` L171-172, L180 | `n = min(size, skip)`, `n -= avail_in` with `avail_in <= n` |
| I-21 | `gzlib.c` L113 `state->level = *mode - '0'` | `*mode` is a digit (tested), level 0..9 |
| I-22 | `gzread.c` L159-160 `strm->next_in[0..3]` | `avail_in > 3` (tested at L158) |
| I-23 | `gzwrite.c` L174 `memset(state->in, 0, n)` | `n <= size` and `in` has `2 * size` bytes |
| I-24 | `gzwrite.c` L497-509 | after `strm->avail_in += len` the data in `in` is `<= 2 * size - 1`; `gz_vacate` brings it to `<= size` or reports a stall |
| I-25 | `gzlib.c` L577, L583 `strlen(state->path) + strlen(msg) + 3` | `state->path` is a NUL-terminated owned block (set at L213-227) |
| I-26 | `gzread.c` L104, L119, L217, gzwrite.c L18, L28, L41 `gz_error(state, Z_MEM_ERROR, "...")` | `gz_error` frees `state->msg` first and for `Z_MEM_ERROR` allocates nothing |

### 2.4 The earlier repository's patches, per function

| Patch | Hunk | Functions that need it (for `_safe`) |
| --- | --- | --- |
| `0002` | `gzread.c` `gz_fetch` `case COPY`: `state->x.next = state->out;` before `gz_load` (L272) | `gz_fetch`, and through it `gz_read`, `gz_skip`, `gzread`, `gzfread`, `gzgetc`, `gzgets`, `gzungetc` (via `gz_skip`) |
| `0004` | `gzlib.c` `gzseek64`: `pos > 0 &&` at L395 and the new test `state->x.pos < 0 && pos > GZ_OFF_MAX + state->x.pos` after L399 | `gzseek64`, `gzseek` |
| `ub.patch` (`gz_reset`) | `state->x.next = Z_NULL;` after L70 | `gz_reset` (so `gz_open`, `gzrewind`), `gzseek64` (read mode), `gzdirect`, `gz_skip_have` |
| `ub.patch` (R-4, **proposed**) | `state->x.next = Z_NULL;` after `state->x.have = 0;` at `gzread.c` L406 | `gz_read` (so the same set) |
| `0001`, `0003`, `ub.patch` (`inflateCopy`) | not in the `gz*` files | none; `gz*` calls `deflate`, `inflate`, `inflateReset`, `deflateReset`, `deflateParams`, `deflateEnd`, `inflateEnd` whose own theorems apply |

The numbers of the line references in the rest of this file are those of the **unpatched** files.

### 2.5 Class D: defined behaviour that needs a model decision

| Id | Site | Decision |
| --- | --- | --- |
| D-1 | `&(state->strm)` at gzread.c L58, L94, L115, L190, L256, L717; gzwrite.c L13, L68, L157, L332, L401, L437, L673, L724; gzlib.c none | a pointer to the **embedded** `z_stream` of the state, passed to `inflate*`/`deflate*` and compared by them (`s->strm != strm`, deflate.c L543; inflate does the same). Use the schema's constructor for a struct inside its owner (`in_gz_state_strm`) so that the pointer has an identity; the `z_stream` record is part of the `gz_state` record |
| D-2 | `gz_load(state, buf, len, unsigned *have)` called with `&got` (gzread L76), `&(state->x.have)` (L272), `&n` (L398, where `n` is also the by-value `len` argument) | the schema says an address of a scalar is passed as a result. Because `gz_load` writes `*have = 0` at the start, again while looping, and the caller reads the field after an **error** return (R-2/gz_read L388-390), pass `have` as a **returned value** and have each caller store it back into its target in all return paths (including `-1`). The pair `(ret, have)` is the result |
| D-3 | `unsigned char buf[1]` (gzgetc L516, gzputc L324) | a stack array whose address is passed to `gz_read`/`gz_write`: allocate a 1-byte block at the declaration and free it before every return (guide: address-taken local) |
| D-4 | `errno` (L24, L36, gzwrite L77, L82, L111, L117) | a thread-local integer cell of the world (section 6); `errno = 0` writes it, `BLOCKED(errno)` reads it |
| D-5 | string literals passed to `gz_error`, returned by `gzerror`; `strm->msg` read at gzread.c L229 | static read-only byte blocks; a pointer to one is a constructor like the static tables. `strm->msg` is a pointer to one of the literals of `inflate.c` or NULL |
| D-6 | `(gz_statep)file` cast between `struct gzFile_s *` and `gz_state *` | the same reference; `gzFile_s` is the first member `x` of `gz_state`. The exposed view (`have`, `next`, `pos`) is `state.x` |
| D-7 | `gz_read(state, voidp buf, ...)`: `(unsigned char *)buf` (L398, L403), `(char *)buf + n` (L411); `gz_write(state, voidpc buf, ...)`: `(const char *)buf + copy` (L231), `(z_const Bytef *)buf` (L245); `memcpy(buf, ...)` with `buf` a `char *` | `void *` is a byte pointer in the schema; the casts are identities |
| D-8 | `fcntl(fd, F_SETFL, fcntl(fd, F_GETFL) \| O_NONBLOCK)` (L261), `fcntl(fd, F_SETFD, fcntl(fd, F_GETFD) \| FD_CLOEXEC)` (L265) | the result of `F_GETFL` (possibly `-1`) is used in an `int` expression; model `fcntl` as returning an `Int32` (section 6) |
| D-9 | `strm->next_in += writ` (gzwrite L88), `state->x.next += writ` (L122), `strm->next_in += ...` | `writ >= 0` was tested; the result stays in the block (I-1) |
| D-10 | `NULL + 0` | `x.next += 0` where `x.next` is NULL after the `ub.patch` hunk, and `strm->next_in + strm->avail_in` with `next_in == NULL` (guarded at gzwrite L402 and L221-222) |
| D-11 | `(int)len < 0` (gzread L447, gzwrite L285, L381): conversion of a value `> INT_MAX` to `int` | implementation-defined (modular in gcc), not UB; model as `toInt32` |
| D-12 | `ret = (int)read(...)`, `writ = (int)write(...)` | `ssize_t` to `int`: the byte count is `<= 2^30`, so the cast is exact; the model's `read`/`write` return values satisfy `|r| <= count` (section 6) |
| D-13 | pointer left dangling in `x.next` (R-4); the `strm.next_out`/`next_in` of the embedded stream left pointing into a user buffer after `gz_read` L403 and `gz_write` L245 | pointers to freed or foreign blocks that are only overwritten later. If the model faults on **any** use of a freed-block pointer, a `gzseek` after `free(userbuf)` would fault; this is why R-4 asks for a patch or a rule that arithmetic by 0 on such a pointer is allowed |
| D-14 | `free(NULL)` (e.g. `free(state->out)` at gzread L102 when the `malloc` failed) | defined, no-op |
| D-15 | `state->start == -1` (L282) after `lseek64` | the model's `lseek` returns `-1` for non-seekable descriptors |

## 3. (c) Static data and constants

There are **no static tables** in the `gz*` files. The data are string literals, small constants and libc constants.

| Name | Where | Value |
| --- | --- | --- |
| `GZBUFSIZE` | `gzguts.h` L172 | 8192 (default `want`; the input buffer is `2 * want`, the output buffer when reading is `2 * want`) |
| `GZ_NONE`, `GZ_READ`, `GZ_WRITE`, `GZ_APPEND` | L175-178 | 0, 7247, 31153, 1 |
| `LOOK`, `COPY`, `GZIP` | L181-183 | 0, 1, 2 (the `how` field; **the same name `GZIP` is also a macro of `deflate.h`, but the two headers never meet**) |
| `max` in `gz_load` and `gz_comp` | gzread.c L21, gzwrite.c L67 | `((unsigned)-1 >> 2) + 1` = 1,073,741,824 = 2^30 |
| `GZ_OFF_MAX` | `gzguts.h` L238 | `2^63 - 1` |
| `DEF_MEM_LEVEL`, `MAX_WBITS + 16`, `15 + 16` | gzwrite.c L37, gzread.c L115 | 8, 31, 31 |
| `0666` | gzlib.c L253 | the creation mode |
| `O_*`, `SEEK_*`, `F_*`, `FD_CLOEXEC`, `EAGAIN` | libc | `O_RDONLY` 0, `O_WRONLY` 1, `O_CREAT` 0100, `O_EXCL` 0200, `O_TRUNC` 01000, `O_APPEND` 02000, `O_NONBLOCK` 04000, `O_CLOEXEC` 02000000, `O_LARGEFILE` 0; `SEEK_SET` 0, `SEEK_CUR` 1, `SEEK_END` 2; `F_GETFD` 1, `F_SETFD` 2, `F_GETFL` 3, `F_SETFL` 4; `FD_CLOEXEC` 1; `EAGAIN` = `EWOULDBLOCK` = 11 (**run**, glibc x86_64) |
| string literals (error messages) | see below | static, read-only |
| `sizeof(gz_state)` | **run** | 248; offsets: `x` 0 (24 bytes: `have` 0, `next` 8, `pos` 16), `mode` 24, `fd` 28, `path` 32, `size` 40, `want` 44, `in` 48, `out` 56, `direct` 64, `junk` 68, `how` 72, `again` 76, `start` 80, `eof` 88, `past` 92, `level` 96, `strategy` 100, `reset` 104, `skip` 112, `err` 120, `msg` 128, `strm` 136 (112 bytes) |

String literals used as values: `"out of memory"` (gzread L104, L119, L217; gzwrite L18, L28, L41; gzlib L530),
`"unexpected end of file"` (gzread L202, L317, L380), `"internal error: inflate stream corrupt"` (L213),
`"compressed data error"` (L229), `"state corrupt"` (L284), `"request does not fit in an int"` (L449),
`"request does not fit in a size_t"` (gzread L501, gzwrite L313), `"out of room to push characters"` (L596),
`"internal error: deflate stream corrupt"` (gzwrite L136), `"requested length does not fit in int"` (L286),
`"string length does not fit in int"` (L382), `"stalled write on gzprintf"` (L462, L504), `""` (gzerror L531, empty string),
and the separators `": "` (L584). Format strings: `"%s"` (gzlib L227), `"<fd:%d>"` (L310), `"%s%s%s"` (L584).

## 4. (d) Struct fields that the code touches

### 4.1 `gz_state` (248 bytes), 22 fields (in declaration order)

| Field | C type | Written by | Read by |
| --- | --- | --- | --- |
| `x.have` | `unsigned` | `gz_reset` L70, `gz_look` L173, `gz_decomp` L235, `gz_fetch` (via `gz_load`), `gz_skip_have`, `gz_read` L371, L406, `gzgetc` L537, `gzungetc` L585, L609, `gzgets` L667, `gzseek64` L407, L430 | everywhere in reading; `gzungetc` L584, L594; `gzdirect` L694 |
| `x.next` | `unsigned char *` | `gz_look` L171, `gz_decomp` L236, `gz_fetch` L275, `gz_skip_have` L300, `gz_read` L370, `gzgetc` L539, `gzungetc` L586, L607, L610, `gzgets` L668, `gzseek64` L431, `gz_init` L54, `gz_comp` L122, L127; **not initialised by `gz_open`** (R-3) | `gz_read` L369, `gzungetc` L601, `gzgets` L661-666, `gz_comp` L110-115, `gz_skip_have` L300 |
| `x.pos` | `z_off64_t` | `gz_reset` L82, `gz_read` L413, `gz_skip_have` L301, `gzgetc` L538, `gzungetc` L588, L612, `gzgets` L669, `gzseek64` L413, L432, `gz_write` L230, L254, `gz_zero` L181, `gzputc` L352, `gzvprintf` L495, L502 | `gzseek64`, `gztell64` |
| `mode` | `int` | `gz_open` | every function |
| `fd` | `int` | `gz_open` | `gz_load`, `gz_comp`, `lseek64` callers, `gzclose_*` |
| `path` | `char *` | `gz_open` L213, L227 | `gz_error` L577, L583; freed at `gzclose_*` |
| `size` | `unsigned` | `gz_open` (0), `gz_look` L107, L118, `gz_init` L48 | `gz_look` L97, `gz_avail`, `gz_fetch`, `gz_read`, `gzungetc`, `gz_comp`, `gz_write`, `gzputc`, `gzvprintf`, `gzclose_*` |
| `want` | `unsigned` | `gz_open` (8192), `gzbuffer` L346 | `gz_look` L99-100, `gz_init` L16, L25, L48 |
| `in` | `unsigned char *` | `gz_look` L99, `gz_init` L16 | `gz_avail`, `gz_look`, `gz_vacate`, `gz_zero`, `gz_write`, `gzputc`, `gzvprintf` |
| `out` | `unsigned char *` | `gz_look` L100, `gz_init` L25 | `gz_look` L171, `gz_fetch`, `gzungetc`, `gz_comp`, `gzclose_*` |
| `direct` | `int` | `gz_open` L110, L153, L161, L185, `gz_look` L138, L164 | `gz_look`, `gzdirect`, `gz_init` L23, `gz_comp` L75, `gzsetparams`, `gzclose_w` |
| `junk` | `int` | `gz_reset` L75, `gz_look` L137, L163, `gz_decomp` L210, L240 | `gz_look` L127-129, `gz_decomp` L221 |
| `how` | `int` | `gz_reset` L74, `gz_look` L136, L162, L175, `gz_decomp` L224, L241 | `gz_fetch` L264, `gz_read`, `gz_skip`, `gzungetc` L562, `gzdirect` L694, `gzseek64` L402 |
| `again` | `int` | `gz_reset` L79, `gz_load` L23, L37, `gz_comp` L78, L83, L112, L118, `gzseek64`? no | `gz_look` L150, `gz_decomp` L201, `gz_fetch` L260, `gzread`/`gzgets`/`gzgetc`/`gzungetc`/`gzwrite`... |
| `start` | `z_off64_t` | `gz_open` L281-282 | `gzrewind` L365 |
| `eof` | `int` | `gz_reset` L73, `gz_load` L45, `gz_decomp` L223, `gzseek64` L408, `gzclearerr` L547 | `gz_avail` L62, `gz_fetch` L287, `gz_skip` L315, `gz_read` L378, L417 |
| `past` | `int` | `gz_reset` L71, `gz_skip` L319, `gz_read` L418, `gzgets` L655, `gzungetc` L589, L613, `gzseek64` L409, `gzclearerr` L548 | `gzseek64` L394, `gztell64` L461, `gzeof` L513 |
| `level`, `strategy` | `int` | `gz_open` L108-109, L113, L141-150, `gzsetparams` L696-697 | `gz_init` L36-37, `gzsetparams` L682 |
| `reset` | `int` | `gz_reset` L78 (write mode), `gz_comp` L100, L144 | `gz_comp` L94 |
| `skip` | `z_off64_t` | `gz_reset` L80, `gz_skip_have` L302, `gz_skip` L318, `gz_zero` L182, `gzseek64` L410, L437 | `gz_read` L353, `gzgets`, `gzungetc`, `gzwrite` paths, `gzseek64`, `gztell64` |
| `err` | `int` | `gz_error` L568, L579 | all |
| `msg` | `char *` | `gz_error` L564, L577 | `gz_error`, `gzerror` L530-531 |
| `strm` | `z_stream` (112 bytes, nested) | see 4.2 | |

### 4.2 `z_stream` fields used by the `gz*` code (the nested `state->strm`)

`next_in` (R/W: gzread L114, L79, L65-72; gzwrite L45, L88, L178, L188, L222, L245, L258, L262, L347, L402-411, L469, L586), `avail_in` (R/W: nearly everywhere),
`next_out` (R/W: gz_decomp L236 read, gz_fetch L279, gz_read L403, gz_init L53, gz_comp), `avail_out` (R/W), `zalloc`, `zfree`, `opaque`
(W: gz_look L110-112, gz_init L33-35), `msg` (R: gz_decomp L229). `total_in`, `total_out`, `adler`, `data_type`, `state`, `reserved` are not touched.

### 4.3 `gzFile_s` (the exposed prefix, 24 bytes)

`have`, `next`, `pos`: they are `gz_state.x` (see above). `gzgetc` in `zlib.h` L1977-1978 (the macro) reads and writes them from application code:
`((g)->have ? ((g)->have--, (g)->pos++, *((g)->next)++) : (gzgetc)(g))`. The library itself does not use the macro.

## 5. Macros: exact expansion, reads and writes

| Macro | Definition (file, lines) | Reads | Writes | Notes |
| --- | --- | --- | --- | --- |
| `LSEEK(fd, off, whence)` | `lseek64` (gzlib.c L13) | | | a function call |
| `BLOCKED(e)` | `((e) == EAGAIN \|\| (e) == EWOULDBLOCK)` (gzguts.h L143) | `errno` | | `EAGAIN == EWOULDBLOCK == 11`, so it is `errno == 11` |
| `zstrerror()` | `strerror(errno)` (gzguts.h L135) | `errno` | | returns a pointer to a NUL-terminated string owned by libc |
| `GT_OFF(x)` | `(sizeof(int) == sizeof(z_off64_t) && (x) > gz_intmax())` (L232) | | | constant `0` here |
| `GZ_OFF_MAX` | `((((z_off64_t)1 << (sizeof(z_off64_t) * CHAR_BIT - 2)) - 1) * 2 + 1)` (L238-239) | | | `2^63 - 1` |
| `deflateInit2(strm, level, method, windowBits, memLevel, strategy)` | `deflateInit2_((strm),(level),(method),(windowBits),(memLevel),(strategy), ZLIB_VERSION, (int)sizeof(z_stream))` (`zlib.h` L1946-1948) | | | used at gzwrite.c L36-37 |
| `inflateInit2(strm, windowBits)` | `inflateInit2_((strm), (windowBits), ZLIB_VERSION, (int)sizeof(z_stream))` (L1949-1951) | | | gzread.c L115 |
| `gzgetc(g)` | the `zlib.h` macro above; `gzread.c` L513 does `#undef gzgetc` before defining the function | | | not used by the library |
| `local` | `static` | | | |
| `ZEXPORT`, `ZEXPORTVA`, `ZLIB_INTERNAL`, `FAR`, `z_const` | empty / hidden visibility | | | |
| `va_start`, `va_end` | compiler built-ins (`__builtin_va_start`, `__builtin_va_end`) | | | gzwrite.c L517, L519 |
| `Z_NULL` | 0 | | | |

No macro contains `return`, `goto` or `break` in the `gz*` files. There is no `goto` and no label.

## 6. The operating-system and libc calls

### 6.1 Complete list, with the exact use

Everything the `gz*` files call outside the library. (`grep` over the four files and the preprocessed output: there is no `getenv`, `fstat`,
`stat`, `fopen`, `fread`, `mmap`, `dup`, `fsync`, `ftruncate`, `time`, `printf` on the live path.)

| Call | Sites | Exact use | What is done with the result |
| --- | --- | --- | --- |
| `open` | gzlib.c L253 | `open((const char *)path, oflag, 0666)`; `oflag` = `[O_CLOEXEC] \| [O_NONBLOCK] \| 0 (O_LARGEFILE) \|` (`O_RDONLY` for read; `O_WRONLY \| O_CREAT \| [O_EXCL] \| (O_TRUNC for 'w', O_APPEND for 'a')`) | stored in `state->fd`; `== -1` => `free(path)`, `free(state)`, return NULL (L269-273) |
| `fcntl` | gzlib.c L261 (if `oflag & O_NONBLOCK`), L265 (if `oflag & O_CLOEXEC`); only for `gzdopen` | `fcntl(fd, F_SETFL, fcntl(fd, F_GETFL) \| O_NONBLOCK)`; `fcntl(fd, F_SETFD, fcntl(fd, F_GETFD) \| FD_CLOEXEC)` | the outer result ignored; the inner result is or-ed into the argument (D-8) |
| `lseek64` | L275 `LSEEK(fd, 0, SEEK_END)` (append); L281 `LSEEK(fd, 0, SEEK_CUR)` (read, saves `start`); L365 `LSEEK(fd, start, SEEK_SET)` (`gzrewind`); L403 `LSEEK(fd, pos - x.pos - have, SEEK_CUR)` (`gzseek64` COPY); L485 `LSEEK(fd, 0, SEEK_CUR)` (`gzoffset64`) | | L275 ignored; L281 `-1` becomes `start = 0`; L365 `-1` returns `-1`; L403 `-1` returns `-1`; L485 `-1` returns `-1` |
| `read` | gzread.c L30 | `read(state->fd, buf + *have, get)` with `1 <= get <= 2^30` | cast to `int`; `<= 0` leaves the loop; `> 0` is added to `*have` |
| `write` | gzwrite.c L80, L115 | `write(fd, strm->next_in, put)`, `write(fd, state->x.next, put)` with `1 <= put <= 2^30` | cast to `int`; `< 0` is an error; otherwise the position advances by `writ` (a result of `0` loops again) |
| `close` | gzread.c L724, gzwrite.c L731 | `close(state->fd)` | `gzclose_r`: `ret ? Z_ERRNO : err`; `gzclose_w`: `== -1` sets `Z_ERRNO` |
| `malloc` | gzlib.c L98 `sizeof(gz_state)` (248), L213 `len + 1`, L307 `19`, L577 `strlen(path) + strlen(msg) + 3`; gzread.c L99 `want`, L100 `want << 1`; gzwrite.c L16 `want << 1`, L25 `want` | | `NULL` is the failure case at each site |
| `free` | gzlib.c L128, L171, L179, L189, L215, L270-271, L315, L563; gzread.c L102-103, L116-117, L718-719, L723, L725; gzwrite.c L27, L39-40, L725, L727, L730, L733 | `free(NULL)` happens (e.g. `free(state->out)` after a failed `malloc`) | |
| `strlen` | gzlib.c L212 (path), L577 (path, msg), L583 (path, msg); gzwrite.c L380 (`s`) | | |
| `snprintf` | gzlib.c L227 `snprintf(state->path, len + 1, "%s", path)`; L310 `snprintf(path, 19, "<fd:%d>", fd)`; L583 `snprintf(state->msg, strlen(path)+strlen(msg)+3, "%s%s%s", state->path, ": ", msg)` | result cast to `void` or ignored | |
| `vsnprintf` | gzwrite.c L485 | `len = vsnprintf(next, state->size, format, va);` | checked at L490 |
| `memcpy` | gzread.c L172, L369, L666; gzwrite.c L228 | | |
| `memmove` | gzwrite.c L410 | `memmove(state->in, strm->next_in, strm->avail_in)` | |
| `memset` | gzwrite.c L174 | `memset(state->in, 0, n)` | |
| `memchr` | gzread.c L661 | `memchr(state->x.next, '\n', n)` | a pointer into `x.next[0..n)` or NULL |
| `strerror` (via `zstrerror()`) | gzread.c L41, L464; gzwrite.c L84, L119 | `strerror(errno)` right after a failed `read`/`write` | the string is passed to `gz_error` which copies it with `snprintf` |
| `errno` | gzread.c L24 (`errno = 0`), L36; gzwrite.c L77, L82, L111, L117 | thread-local lvalue | tested against `EAGAIN`/`EWOULDBLOCK` only |
| `va_start`, `va_end` | gzwrite.c L517, L519 | | |

### 6.2 Proposed model: an explicit world in the heap

Goal: every `gz*` theorem holds for **every** behaviour of the operating system that the standard allows (safety), and says more about
reading back what was written when the world is a concrete file system (functional). Two layers:

* **L1, an abstract contract (for safety).** Each call returns a result chosen by an *oracle*; only the post-condition that POSIX
  guarantees is assumed. Theorems quantify over the oracle.
* **L2, a concrete file system (for functional theorems).** Files are byte arrays; the oracle only chooses short counts and
  injects failures. L2 behaviours are a subset of L1 behaviours, so every L1 theorem holds for L2.

```lean
structure OFD where                 -- open file description
  file : FileId; pos : Int64
  readable writable append nonblock : Bool
structure World where
  files   : FileId → Option File    -- File: kind (regular | other) and contents : ByteArray (L2) or just `size : Nat` (L1)
  names   : Array UInt8 → Option FileId   -- path name (a flat map; no directories needed)
  ofds    : Nat → Option OFD
  fds     : Int32 → Option Nat      -- descriptor -> OFD (several descriptors may share one)
  cloexec : Int32 → Bool
  errno   : Int32                   -- the thread-local errno
  osCalls : Nat                     -- number of OS calls so far (index into the oracle)
```
`Oracle : Nat → Choice` gives the `n`-th OS call its decision (success / which errno / how many bytes). Allocation uses the same
idea: the heap's allocation counter and oracle (`malloc` returns NULL or a fresh block). An *error oracle for each call* is the
function `Oracle` restricted to the call.

What each call must do in the model (fault = the model raises `Fault.ub`; the C would be UB or `EFAULT`):

| Call | Arguments checked (fault if wrong) | Outcomes (L1) | Effect on the world in L2 |
| --- | --- | --- | --- |
| `malloc(n)` | none (`n > 0` at every site) | NULL, or a fresh block of `n` bytes, uninitialised | allocation counter + 1 |
| `free(p)` | `p` NULL, or the start of a live block | none | the block is freed; double free faults |
| `strlen(p)` | a NUL occurs inside the live block | `index of the first NUL` | none |
| `memcpy`, `memmove`, `memset`, `memchr` | ranges inside live blocks; `memcpy` ranges disjoint; destination not read-only | as C | as C (`memchr` returns an offset or NULL) |
| `snprintf(dst, n, fmt, ...)` for the three formats | `dst` has `n` bytes (`n >= 1`) | writes `min(L, n - 1)` bytes of the formatted text `T` and a NUL; returns `L = |T|` | `T` = `s`; `"<fd:" ++ decimal(fd) ++ ">"`; `s1 ++ s2 ++ s3` |
| `vsnprintf(dst, n, fmt, va)` | `dst` has `n` bytes; `fmt` NUL-terminated; arguments agree (P-5) | section 7 | as section 7 |
| `strerror(e)` | none | a pointer to a NUL-terminated read-only string, a pure function of `e` | none |
| `open(path, flags, 0666)` | `path` NUL-terminated | `-1` with `errno` from a set (`ENOENT` if no such file and no `O_CREAT`; `EEXIST` with `O_CREAT|O_EXCL`; `EACCES`, `EISDIR` for write; `EMFILE`, `ENFILE`, `ENOMEM`, `EINTR`, ...), or the **lowest unused descriptor** `fd >= 0` | creates an OFD at `pos = 0`; `O_TRUNC` empties a regular file; `O_CREAT` creates it; `O_APPEND`, `O_NONBLOCK`, `O_CLOEXEC` recorded |
| `fcntl(fd, cmd, arg)` | none | `-1`/`EBADF` if `fd` is not open; `F_GETFL` returns the flag word (access mode, `O_APPEND`, `O_NONBLOCK`); `F_SETFL` sets `O_APPEND`/`O_NONBLOCK`; `F_GETFD`/`F_SETFD` the close-on-exec bit; returns `0` for the setters | updates the flags |
| `lseek64(fd, off, whence)` | `whence` in {0, 1, 2} | `-1`/`EBADF`; `-1`/`ESPIPE` if not seekable; `-1`/`EINVAL` if the result is negative; `-1`/`EOVERFLOW`; otherwise the new position | regular file: `pos := (base + off)`; positions beyond the end allowed |
| `read(fd, buf, n)` | `buf[0..n)` inside a live writable block; `n >= 1` | `-1` with `errno` in {`EBADF` (not readable), `EISDIR`, `EIO`, `EINTR`, `EAGAIN` (only if non-blocking)}; `0` at end of file (`pos >= size`); otherwise `k` with `1 <= k <= min(n, size - pos)` (**the oracle picks `k`; a short read is allowed**) | copies `k` bytes from `contents[pos ..]` to `buf`, `pos += k` |
| `write(fd, buf, n)` | `buf[0..n)` inside a live readable block; `n >= 1` | `-1` with `errno` in {`EBADF` (not writable), `EAGAIN` (non-blocking), `EINTR`, `EIO`, `ENOSPC`, `EFBIG`, `EPIPE`, ...}; otherwise `k` with `1 <= k <= n` (**short write allowed; never `0` for `n >= 1` on a regular file**) | writes at `pos` (at the end for `O_APPEND`), extends with zeros if `pos > size`, `pos += k`; on `-1` nothing is written |
| `close(fd)` | none | `0`, or `-1` with `EBADF`/`EIO`/`EINTR` | the descriptor is released **even when `-1` is returned** (Linux); the OFD is dropped when its last descriptor closes |

`errno` is only ever *compared* with `EAGAIN` by the library and *printed* through `strerror`; so a world with `errno : Int32` and a
two-valued predicate "is `EAGAIN`" is enough for safety. Each failing call writes `errno`; a successful call leaves it unchanged
(POSIX), and the library writes `errno = 0` before `read`/`write`. The model must therefore **not** set `errno` on success.

Termination needs a fairness hypothesis, stated once as `Fair oracle`: `write` with `n >= 1` returns `>= 1` or `-1`; the number of
consecutive `EAGAIN` results is not constrained (the library returns to the caller on `EAGAIN`, so no loop depends on it). The loops that
depend on OS progress: `gz_comp` L76-89 and L110-123 (a `write` returning `0` loops forever), `gz_load` L26-34 (terminates for any `read`: each positive result
adds to `*have`, and `<= 0` leaves).

### 6.3 What a `gz*` theorem can then say

1. **Safety (L1, any oracle).** For a well-formed `gz_state` (`GzInv`) and a well-formed world (`WorldWF`: fd table consistent, the `fd` of
   the state is open or the state is fresh), every `gz*` function runs without fault, terminates (under `Fair`), preserves `GzInv`
   and `WorldWF`, and only changes the fields and blocks it should (frame).
2. **No leaks.** After `gzclose`/`gzclose_r`/`gzclose_w` the set of live heap blocks is the set before `gzopen`/`gzdopen`; the
   descriptor opened by `gzopen` is closed exactly once (for `gzdopen` the descriptor is closed by `gzclose`). After a failed
   `gzopen` (`NULL`) nothing leaked and no descriptor stays open. Every early `return NULL` in `gz_open` (L95, L100, L129, L172, L180, L190, L216-217, L272) frees what it allocated.
3. **Error state.** `GzInv` includes: `msg != NULL` implies `err` is neither `Z_OK` nor `Z_MEM_ERROR` and `msg` is an owned NUL-terminated block of
   the form `path ++ ": " ++ text`; `gzerror` returns `"out of memory"` for `Z_MEM_ERROR`, `msg` or `""` otherwise; `gzclearerr` establishes `err = Z_OK`.
4. **Read/write functional (L2).** (i) *Write then read*: `gzopen(p, "wb")`, any chunking of `gzwrite`/`gzputc`/`gzputs`/`gzprintf`, `gzclose`, then `gzopen(p, "rb")` and any
   chunking of `gzread`/`gzgetc`/`gzgets`/`gzungetc` returns exactly the written bytes, and the file is a valid gzip member (the `deflate` spec). (ii) *Transparent reads*: a file that does not start with a
   gzip header is returned byte for byte (`direct == 1`). (iii) *Concatenated members and trailing garbage* (`junk`). (iv) *Position*: `gztell` = bytes
   read or written; `gzseek` forward and backward; `gzoffset` = file position minus buffered input. (v) *Append and `gzdopen`*.
5. **Non-blocking.** After `again` is set, a retry resumes (the output is the same as in a blocking run): a statement about the pair of runs.
6. **API-sequence safety**: any interleaving of the public functions on one `gzFile` (with `gzclose` last) is safe: this is the deliverable theorem that needs the non-vacuity
   witness (a concrete world with a file and an oracle).

What is lost by the abstraction: concurrency and signals (an interrupted `read` is reported as an error, never retried by zlib, so
`EINTR` is just another errno); other processes changing the file; real file-system semantics beyond a flat name space (permissions, symbolic links, directories, `O_EXCL` races, sparse files, quotas);
special files (pipes, terminals) beyond "not seekable"; timing and blocking; the exact `errno` numbers and the text of `strerror` (the message text is
an uninterpreted function of `errno`); memory exhaustion beyond the oracle; `fork`/`exec` and `O_CLOEXEC` effects; `lseek` beyond `2^63`; `gzdopen` on a descriptor that is closed or reused behind zlib's back (P-6).

## 7. `gzprintf` / `gzvprintf` and `va_list`

`gzvprintf(file, format, va)` (L420-511) uses `va` once, in `vsnprintf(next, state->size, format, va)` (L485); `gzprintf` (L513-521) builds `va` with `va_start(va, format)` and ends it with `va_end(va)`.
The control flow around the call does not depend on the arguments except through two values: the returned `len` and the bytes written.
So the library's behaviour is determined by `vsnprintf`'s result `(len, bytes)`.

**Model.** `va_list` is a list of argument values:
```lean
inductive VaArg | i32 (v : Int32) | u32 (v : UInt32) | i64 (v : Int64) | u64 (v : UInt64) | ptr (p : BPtr) | dbl (d : Float)
structure VaList where args : List VaArg
```
`gzprintf` translates to a function taking `VaList` (the test and the callers supply the list); `va_start` is the identity on the list, `va_end` the identity. `vsnprintf` is a function
`vformat : (fmt : Array UInt8) → VaList → Option (Array UInt8)`: it returns `none` for an unsupported conversion or a mismatch, and `some T` for the formatted text.

* **A bounded format language.** Supported: literal text, `%%`, `%c`, `%d`, `%i`, `%u`, `%x`, `%X`, `%o`, `%s` (a NUL-terminated string read from the heap through the pointer
  argument; `%.Ns` truncation), with the length modifiers `l`, `ll`, `z`, `h`, `hh`, `j`, `t`, the flags `-`, `0`, `+`, space, `#`, an optional decimal width and precision and `*` (taking an `int` argument).
  Not supported in the first version: `%f %e %g %a` (floating point), `%n` (writes through a pointer argument), `%p` (implementation text), `%ls`, `%m`, positional arguments `%1$d`.
* **Specification of the call.** With `size = state->size`, `T = vformat fmt va`:
  if `T = some t` then the model writes the first `min(|t|, size - 1)` bytes of `t` into `next[0..)` followed by a NUL, and returns `|t|` (the C99 result, which is the length that
  would have been written, not the truncated length). If `T = none` (unsupported or invalid), the call is **demonic**: `len` is any `Int32`, the buffer receives any bytes with a NUL at some position `<= size - 1`.
  The library then runs the check of L490: `len == 0 || (unsigned)len >= state->size || next[state->size - 1] != 0` returns 0.
* **Why a demonic fallback is sound for safety.** After the call the library reads only `len` and `next[size - 1]`, and then adds `len` (a value known to be in `1 .. size - 1`) to `avail_in`
  (L494). The writes of `vsnprintf` are limited to `next[0 .. size - 1]` (the C99 contract; a pre-C99 `vsnprintf` would be the reason for the sentinel at L471). So the safety theorem holds for every
  `(len, bytes)` that satisfies `len = 0 || len >= size || next[size-1] != 0 || (1 <= len < size && bytes[len] = NUL ...)`. In particular the theorem does not need `vformat` at all.
* **What the functional theorem says.** For a supported `(fmt, va)` with `1 <= |T| < size`: `gzprintf` returns `|T|` and the bytes of `T` are appended to the uncompressed stream (`x.pos += |T|`); for `|T| = 0` or `|T| >= size` it returns `0` and the stream is unchanged
  (L490-491); after a `gz_vacate` stall it returns the error code with the formatted output discarded (L499-506).
* **What is lost.** Floating-point output (`vformat` returns `none`; the theorem is only about the library's handling, not about the text), locale-dependent output, `%n`, and any
  behaviour for formats that do not match their arguments (UB in the C; the model requires agreement as a precondition P-5). The `va_list` object itself (its internal pointer) is not modelled; it is a value.
* The non-`STDC` version of `gzprintf` with twenty `int` arguments (L526-635) is dead.

## 8. Cross-cutting decisions for the translators

1. **`x.next` and the other pointers in the state.** Every pointer field of `gz_state` (`path`, `in`, `out`, `msg`, `x.next`, and the pointers inside the embedded `strm`) must be a pointer value that can be NULL, a pointer into a live block, or a pointer to a freed or foreign block (R-4/D-13). Decide D-13 once, before translating `gz_read`.
2. **Control-flow tags.** There is no `goto`. `break` and `continue` appear in: `gz_load` (`break` L32), `gz_decomp` (`break` x5), `gz_fetch` (`break` inside `switch` x2, `return` x6), `gz_skip` (`break` L320), `gz_read` (`break` L381, `continue` L391), `gzgets` (`break` L653, L656), `gz_look` (none), `gz_write` (`break` L234). `continue` in a `do ... while` (`gz_read` L391) jumps to the loop condition and **skips the progress update at L410-413**. `break` inside a `switch` inside a `do ... while` (`gz_fetch` L270, L282) leaves the `switch` only, not the loop.
3. **Mode checks.** Every public function begins with `file == NULL` and a mode test (`mode != GZ_READ`, `!= GZ_WRITE` or both). Translate each as written; do not hoist.
4. **Return type mixing.** `gz_read`/`gz_write` return `z_size_t`; `gzread`/`gzwrite` cast to `int` (`(int)len`, L470; `(int)gz_write`, L291); `gzputs` returns `len && put == 0 ? -1 : (int)put`.
5. **Order of the error checks** at the start of `gzread`, `gzfread`, `gzgetc`, `gzgets`, `gzungetc` (L438-441 etc.): `err != Z_OK && err != Z_BUF_ERROR && !again && x.have == 0` returns first; then `if (again) gz_error(state, Z_OK, NULL)`. Keep the order.
6. **Allocation bookkeeping.** `state->size` is the flag "buffers allocated" (non-zero); `gz_look` and `gz_init` set it **after** both `malloc` calls succeed and reset it to 0 when `inflateInit2`/`deflateInit2` fail (gzread L118) while leaving `in`/`out` dangling; the frees at `gzclose_*` are guarded by `size`.

## 9. Function by function

Each section has the six items: (1) signature and size, (2) callees, (3) control flow that needs a decision, (4) memory behaviour, (5) integer rules, (6) proposed translation.
`M` is the runtime monad; `W` stands for the world of section 6.2.

### 9.1 `gzlib.c`

#### `gz_reset` (L69-84; 16 lines)
1. `local void gz_reset(gz_statep state)`. 2. Lib: `gz_error(state, Z_OK, NULL)`. 3. `if (mode == GZ_READ) {...} else ...` (L72-78). 4. Writes `x.have`, `past`, `eof`/`how`/`junk` (read) or `reset` (write), `again`, `skip`, `x.pos`, `strm.avail_in`; **not `x.next`** (R-3). 5. none. 6. Direct; with the `ub.patch` hunk add `x.next := null` after `x.have := 0`.

#### `gz_open` (L87-290; 204 lines)
1. `local gzFile gz_open(const void *path, int fd, const char *mode)`. 2. Lib: `gz_reset`. libc: `malloc`, `free`, `strlen`, `snprintf`, `open`, `fcntl`, `lseek64`.
3. `while (*mode)` (L111-167): `if (digit) level = ...; else switch (*mode) {...}` then `mode++`; `case '+'` does `free(state); return NULL;` (L127-129) from inside the switch; other cases `break` out of the switch only. After the loop: returns NULL at L95, L100, L172, L180, L190, L216, L272, then `gz_reset` and `return (gzFile)state`. `if (fd == -1) open ... else { fcntl...; state->fd = fd; }`.
4. Allocates `gz_state` (248 bytes; fields not set stay uninitialised: `in`, `out`, `x.next`, `start` (write), `eof`/`how`/`junk` (write), `reset` (read), `strm` except `avail_in`); `path` copy: `malloc(len+1)` + `snprintf("%s")`; reads the caller's `path` (NUL-terminated) and `mode` string.
5. `*mode - '0'` (`char` is signed: a byte `>= 0x80` is negative and falls into the `switch` default); `oflag |=` bit flags; `len = strlen(path)` `z_size_t`; `len + 1` no wrap.
6. One `def` with the loop as recursion on the mode pointer offset and tag `{cont, ret (none)}`; every `return NULL` frees exactly what is live at that point (state, path). Calls the OS functions through section 6.2.

#### `gzopen` (L293-295), `gzopen64` (L298-300)
1. `gzFile ZEXPORT gzopen(const char *path, const char *mode)`; same for `gzopen64`. 2. Lib: `gz_open(path, -1, mode)`. 3-5. none. 6. One call each.

#### `gzdopen` (L303-317; 15 lines)
1. `gzFile ZEXPORT gzdopen(int fd, const char *mode)`. 2. Lib: `gz_open`. libc: `malloc(19)`, `snprintf(path, 19, "<fd:%d>", fd)`, `free`. 3. `if (fd < 0 || (path = malloc(...)) == NULL) return NULL;`. 4. A 19-byte scratch block; `"<fd:"` + at most 10 digits + `">"` + NUL is at most 16 bytes. 5. `7 + 3 * sizeof(int)` is `size_t`. 6. Needs `decimal : Int32 → Array UInt8` in the `snprintf` model.

#### `gzbuffer` (L327-348; 22 lines)
1. `int ZEXPORT gzbuffer(gzFile file, unsigned size)`. 2. none. 3. four early `return -1`. 4. writes `want`. 5. `(size << 1) < size` is an intended unsigned wrap test; `size < 8` raises to 8. 6. Direct.

#### `gzrewind` (L351-369; 19 lines)
1. `int ZEXPORT gzrewind(gzFile file)`. 2. Lib: `gz_reset`; `lseek64`. 3. early `-1` returns. 4. reads `start`, `fd`. 5. none. 6. Direct.

#### `gzseek64` (L372-439; 68 lines)
1. `z_off64_t ZEXPORT gzseek64(gzFile file, z_off64_t offset, int whence)`. 2. Lib: `gz_error`, `gzrewind`; `lseek64`.
3. Early `-1` returns L379, L382, L386, L390, L396, L398, L406, L420, L422. Three paths: (a) raw area while reading with `how == COPY` (L402-415, returns `pos`), (b) rewind if `pos < x.pos` (L418-423), (c) skip buffered output then set `skip` (L424-438). The conditional expression at L428-429 is `(GT_OFF(have) || (z_off64_t)have > offset) ? (unsigned)offset : have`.
4. Reads/writes `x.have`, `x.next` (`+= n`, R-3/R-4), `x.pos`, `eof`, `past`, `skip`, `strm.avail_in`.
5. **Signed `z_off64_t` arithmetic**: L394 `x.pos + (past ? 0 : skip)`, L395 `GZ_OFF_MAX - pos` (R-1: overflows for `pos < 0`), L397 `-pos`, L403 `pos - x.pos - (z_off64_t)have`, L424 `pos - x.pos`, L433 `offset -= n`. With `0004` the checks at L395 and the new test make these safe.
6. One `def`; checked `Int64` arithmetic that faults on overflow (so the unpatched code faults exactly at R-1). Translate with the patch applied only when the workspace has `0004`.

#### `gzseek` (L442-447), `gztell64` (L450-462), `gztell` (L465-470), `gzoffset` (L494-499)
1. `z_off_t gzseek(gzFile, z_off_t, int)`; `z_off64_t gztell64(gzFile)`; `z_off_t gztell(gzFile)`; `z_off_t gzoffset(gzFile)`. 2. Lib: `gzseek64`, `gztell64`, `gzoffset64`. 3. `gztell64`: `file == NULL` and mode tests return -1. 4. `gztell64` reads `x.pos`, `past`, `skip`. 5. `ret == (z_off_t)ret ? (z_off_t)ret : -1` is always true on LP64; `x.pos + skip` signed (I-16). 6. Direct.

#### `gzoffset64` (L473-491; 19 lines)
1. `z_off64_t ZEXPORT gzoffset64(gzFile file)`. 2. `lseek64(fd, 0, SEEK_CUR)`. 3. early returns; `if (mode == GZ_READ) offset -= strm.avail_in`. 4. reads `strm.avail_in`. 5. `long -= unsigned` (I-17). 6. Direct.

#### `gzeof` (L502-514), `gzclearerr` (L535-551)
1. `int ZEXPORT gzeof(gzFile)`; `void ZEXPORT gzclearerr(gzFile)`. 2. `gzclearerr`: `gz_error(state, Z_OK, NULL)`. 3. early returns on NULL/mode. 4. `gzeof` reads `past`; `gzclearerr` writes `eof`, `past` (read mode). 5. none. 6. Direct.

#### `gzerror` (L517-532; 16 lines)
1. `const char * ZEXPORT gzerror(gzFile file, int *errnum)`. 2. none. 3. `if (errnum != NULL) *errnum = state->err;` then a nested conditional expression. 4. Returns a static literal (`"out of memory"` or `""`) or `state->msg`. 5. none. 6. Direct; static strings as constructors.

#### `gz_error` (L559-590; 32 lines)
1. `void ZLIB_INTERNAL gz_error(gz_statep state, int err, const char *msg)`. 2. libc: `free`, `malloc`, `strlen`, `snprintf`. 3. Early `return` at L570 (`msg == NULL`), L574 (`Z_MEM_ERROR`), L580 (allocation failure, sets `err = Z_MEM_ERROR`). 4. frees `msg` (not when `err == Z_MEM_ERROR`, L562: such a `msg` is never non-NULL), allocates `strlen(path)+strlen(msg)+3`, writes `"path: msg"`. 5. `size_t` sum. 6. Direct; `snprintf` of `"%s%s%s"` modelled as concatenation.

#### `gz_intmax` (L596-609)
1. `unsigned ZLIB_INTERNAL gz_intmax(void)`. 2-5. `return INT_MAX` (L598); the `#else` loop is dead; never called (GT_OFF). 6. Constant `0x7fffffff`.

### 9.2 `gzread.c`

#### `gz_load` (L18-47; 30 lines)
1. `local int gz_load(gz_statep state, unsigned char *buf, unsigned len, unsigned *have)`. 2. libc: `read`, `errno`; Lib: `gz_error(state, Z_ERRNO, zstrerror())`.
3. `do { ... if (ret <= 0) break; *have += ret; } while (*have < len);` then `if (ret < 0) { if (BLOCKED(errno)) { again = 1; if (*have != 0) return 0; } gz_error(...); return -1; } if (ret == 0) eof = 1; return 0;`.
4. Writes `*have` (D-2), `again`, `eof`, `errno := 0` at start; reads into `buf + *have`.
5. `max = 2^30`; `get = len - *have` (unsigned, `*have < len`); `(int)read(...)` exact; `*have += (unsigned)ret`.
6. Returns `(ret, have)`; loop state `(have, ret)`; the caller stores `have` in **all** paths (R-2).

#### `gz_avail` (L56-82; 27 lines)
1. `local int gz_avail(gz_statep state)`. 2. Lib: `gz_load`. 3. early `return -1` L61, L77. 4. forward byte copy `*p++ = *q++` `avail_in` times from `next_in` to `in` (same block, overlapping when `q > p`), then `gz_load(state, in + avail_in, size - avail_in, &got)`; writes `avail_in`, `next_in`. 5. `n = avail_in` `unsigned`, `do ... while (--n)` runs `n >= 1` times. 6. Loop on `(p, q, n)`; the pointer test `q != p` is equality only.

#### `gz_look` (L93-177; 85 lines)
1. `local int gz_look(gz_statep state)`. 2. Lib: `gz_error`, `gz_avail`, `inflateInit2`, `inflateReset`. libc: `malloc`, `free`, `memcpy`.
3. Returns at L105, L120, L131, L133, L139, L149, L153, L165, L176. `if (size == 0) {...}` (allocation), `if (direct == -1 || junk == 0) {...}`, header sniff, copy fallback.
4. Allocates `in` (`want`) and `out` (`want << 1`), frees both and resets `size = 0` when `inflateInit2` fails; sets `strm.zalloc/zfree/opaque/avail_in/next_in`; `memcpy(x.next, next_in, avail_in)`; reads `next_in[0..3]`.
5. `want << 1` (I-13); `state->junk = state->junk != -1` (a 0/1 value); `avail_in > 3`.
6. Direct, one `def`; results of `inflateReset` ignored.

#### `gz_decomp` (L187-247; 61 lines)
1. `local int gz_decomp(gz_statep state)`. 2. Lib: `gz_avail`, `inflate`, `gz_error`. 3. `do { ... } while (strm->avail_out && ret != Z_STREAM_END);` with `break` at L198, L203, L214, L218, L226, L230; after it the update and two `return`s.
4. Reads/writes the embedded stream; `x.have = had - avail_out`; `x.next = next_out - x.have` (a pointer into whatever buffer `next_out` points to: `out` or the user's buffer, R-4); reads `strm->msg`.
5. `had - strm->avail_out` unsigned.
6. Loop with tag `{go, brk}`; the `ret` local carries over the loop.

#### `gz_fetch` (L255-289; 35 lines)
1. `local int gz_fetch(gz_statep state)`. 2. Lib: `gz_look`, `gz_load`, `gz_decomp`, `gz_error`. 3. `do { switch (how) { case LOOK: ...; break; case COPY: ...; return 0; case GZIP: ...; break; default: ...; return -1; } } while (x.have == 0 && (!eof || avail_in));`: `break` leaves the `switch` only. 4. Sets `strm.avail_out`, `next_out`; `gz_load(.., &(x.have))`; `x.next = out` (R-2: must precede `gz_load`). 5. `size << 1`. 6. Loop with the `switch` as a `match`; returns inside the match are loop exits.

#### `gz_skip_have` (L293-303; 11 lines)
1. `local void gz_skip_have(gz_statep state)`. 2. none. 3. none. 4. `x.have`, `x.next += n`, `x.pos`, `skip`. 5. `(z_off64_t)x.have > skip ? (unsigned)skip : x.have`; `skip -= n` (`long -= unsigned`). 6. Direct (R-3/R-4 on `x.next`).

#### `gz_skip` (L307-335; 29 lines)
1. `local int gz_skip(gz_statep state)`. 2. Lib: `gz_skip_have`, `gz_error`, `gz_fetch`. 3. `do { if (x.have) ...; else if (eof && avail_in == 0) {...; break;} else { if (gz_fetch(state) == -1 && x.have == 0) return -1; } } while (state->skip);`. 4. fields only. 5. none. 6. Loop with tags.

#### `gz_read` (L343-422; 80 lines)
1. `local z_size_t gz_read(gz_statep state, voidp buf, z_size_t len)`. 2. Lib: `gz_skip`, `gz_fetch`, `gz_load`, `gz_decomp`, `gz_error`. libc: `memcpy`.
3. `if (len == 0) return 0;` `if (skip && gz_skip(state) == -1) return 0;` then `do { ... } while (len && !err);` with a four-way `if / else if ... / else` (L366-407): (a) copy from `x`, (b) at EOF `break` (L381), (c) `continue` (L391) to refill, (d) direct COPY `err = gz_load(state, buf, n, &n)` (D-2), (e) direct GZIP `strm.avail_out = n; next_out = buf; err = gz_decomp; n = x.have; x.have = 0` (R-4). Progress update L410-413 for (a), (d), (e) only. After: `if (len && eof) past = 1; return got`.
4. `memcpy(buf, x.next, n)` into the user buffer; `x.next += n`; `x.pos += n`.
5. `n = (unsigned)-1; if (n > len) n = (unsigned)len`; `n < (size << 1)`; `len -= n`; `buf = (char *)buf + n`; `got += n`; `x.pos += n` (I-15).
6. Loop state `(len, buf, got, err, n)`; tags `{go, cont, brk}` as in section 8, item 2.

#### `gzread` (L425-471; 47 lines), `gzfread` (L474-507; 34 lines)
1. `int ZEXPORT gzread(gzFile file, voidp buf, unsigned len)`; `z_size_t ZEXPORT gzfread(voidp buf, z_size_t size, z_size_t nitems, gzFile file)`. 2. Lib: `gz_read`, `gz_error`; `zstrerror()`. 3. sequences of early returns; the order of the checks matters (section 8, item 5). 4. fields. 5. `(int)len < 0`; `len = (unsigned)gz_read(...)`; `nitems * size` with `len / size != nitems` (divide only if `size != 0`); result `gz_read(..)/size` only when `len != 0`. 6. Direct.

#### `gzgetc` (L515-544; 30 lines), `gzgetc_` (L546-548)
1. `int ZEXPORT gzgetc(gzFile file)`; `int ZEXPORT gzgetc_(gzFile file)`. 2. `gz_read(state, buf, 1)`; `gzgetc_` calls `gzgetc`. 3. fast path `if (x.have) {...return *(x.next)++;}`. 4. local 1-byte array (D-3); `*(x.next)++` reads then increments. 5. `x.have--`, `x.pos++`; result is `unsigned char` widened to `int`; `gz_read(..) < 1 ? -1 : buf[0]`. 6. Direct.

#### `gzungetc` (L551-615; 65 lines)
1. `int ZEXPORT gzungetc(int c, gzFile file)`. 2. Lib: `gz_look`, `gz_error`, `gz_skip`. 3. early returns; three cases by `x.have`: `0` (put at the end of `out`), `== size << 1` (error), otherwise slide and insert (L601-614). The slide `while (src > out) *--dest = *--src;` is a backward copy. 4. writes `out[...]`, `x.next`, `x.have`, `x.pos--`, `past`. 5. `x.pos--` makes it `-1` (R-1); `(unsigned char)c`. 6. Direct; the relational compare `src > out` is inside one block (I-6).

#### `gzgets` (L618-681; 64 lines)
1. `char * ZEXPORT gzgets(gzFile file, char *buf, int len)`. 2. Lib: `gz_skip`, `gz_fetch`; libc `memchr`, `memcpy`. 3. `if (left) do { ... break at L653, L656 ... } while (left && eol == NULL);` 4. `memchr(x.next, '\n', n)` returns an offset; `memcpy(buf, x.next, n)`; final `buf[0] = 0`. 5. `left = (unsigned)len - 1`; `n = x.have > left ? left : x.have`; `(unsigned)(eol - x.next) + 1`. 6. Loop with `break` tags; `eol` is only read after being assigned in the same iteration.

#### `gzdirect` (L684-701; 18 lines)
1. `int ZEXPORT gzdirect(gzFile file)`. 2. Lib: `gz_look`, `gz_skip_have`. 3. one `if`. 4. R-3 via `gz_skip_have`. 5. none. 6. Direct.

#### `gzclose_r` (L704-727; 24 lines)
1. `int ZEXPORT gzclose_r(gzFile file)`. 2. Lib: `inflateEnd`, `gz_error`; libc `free` x4, `close`. 3. `if (size) {...}` frees; `ret ? Z_ERRNO : err`. 4. frees `out`, `in`, `path`, the state. 5. none. 6. Direct; leak-freedom anchor.

### 9.3 `gzwrite.c`

#### `gz_init` (L11-57; 47 lines)
1. `local int gz_init(gz_statep state)`. 2. Lib: `gz_error`, `deflateInit2`. libc: `malloc`, `free`. 3. returns -1 at L19, L29, L42. 4. allocates `in` (`want << 1`), `out` (`want`); sets zalloc/zfree/opaque, `next_in = NULL`, `size = want`, `avail_out`, `next_out`, `x.next`. 5. `want << 1`. 6. Direct.

#### `gz_comp` (L65-148; 84 lines)
1. `local int gz_comp(gz_statep state, int flush)`. 2. Lib: `gz_init`, `gz_error`, `deflateReset`, `deflate`. libc: `write`, `errno`.
3. returns -1 at L72, L85, L120, L137; direct-write `while (avail_in)` loop (L76-89); pending reset; `do { if (avail_out == 0 || (flush != Z_NO_FLUSH && (flush != Z_FINISH || ret == Z_STREAM_END))) { while (next_out > x.next) {... write ...} if (avail_out == 0) {...} } have = avail_out; ret = deflate(strm, flush); ...; have -= avail_out; } while (have);`.
4. pointer **relational** compare and difference (I-1); `x.next += writ`; reads `out`.
5. `max = 2^30`; `put` is `unsigned`; `(int)max`; `have -= avail_out`. 6. Two loops as recursions; fairness (`write` returning 0 loops).

#### `gz_zero` (L154-193; 40 lines)
1. `local int gz_zero(gz_statep state)`. 2. Lib: `gz_init`, `gz_comp`. libc `memset`. 3. `do { ... } while (state->skip);` with a `return -1`. 4. zeroes `in`, sets `next_in`, `avail_in`. 5. `n = (z_off64_t)size > skip ? (unsigned)skip : size`; `n -= avail_in`; `x.pos += n`; `skip -= n`. 6. Loop on the heap.

#### `gz_write` (L199-267; 69 lines)
1. `local z_size_t gz_write(gz_statep state, voidpc buf, z_size_t len)`. 2. Lib: `gz_init`, `gz_zero`, `gz_comp`. libc `memcpy`. 3. `if (len < size) { for (;;) {...break...} } else {...do ... while (len)...}`; returns `0`, `put - len`, `put`. 4. `memcpy(in + have, buf, copy)`; `next_in` points into the user's buffer in the second branch until reset (L258, L262). 5. `have = (unsigned)((next_in + avail_in) - in)`; `copy = size - have` (I-4); `n = (unsigned)-1; if (n > len) n = (unsigned)len`. 6. Two loops; the early `return` at L236 and L259 uses `again`.

#### `gzwrite` (L270-292), `gzfwrite` (L295-319), `gzputs` (L365-387)
1. `int ZEXPORT gzwrite(gzFile, voidpc, unsigned)`; `z_size_t ZEXPORT gzfwrite(voidpc, z_size_t, z_size_t, gzFile)`; `int ZEXPORT gzputs(gzFile, const char *)`. 2. Lib: `gz_write`, `gz_error`; `gzputs`: `strlen`. 3. early returns. 4. none beyond fields. 5. `(int)len < 0`; `nitems * size` overflow test; `len && put == 0 ? -1 : (int)put`; `(unsigned)len != len`. 6. Direct.

#### `gzputc` (L322-362; 41 lines)
1. `int ZEXPORT gzputc(gzFile file, int c)`. 2. Lib: `gz_zero`, `gz_write`. 3. fast path then fallback. 4. local 1-byte array (D-3); `in[have] = c`. 5. `have = (unsigned)((next_in + avail_in) - in)`; `c & 0xff`. 6. Direct.

#### `gz_vacate` (L398-413; 16 lines)
1. `local int gz_vacate(gz_statep state)`. 2. Lib: `gz_comp`; libc `memmove`. 3. returns 0 at L404, L408; final `return avail_in > size`. 4. `memmove` within `in`. 5. relational pointer compare (I-2). 6. Direct.

#### `gzvprintf` (L420-511; 92 lines), `gzprintf` (L513-521; 9 lines)
1. `int ZEXPORTVA gzvprintf(gzFile file, const char *format, va_list va)`; `int ZEXPORTVA gzprintf(gzFile file, const char *format, ...)`. 2. Lib: `gz_init`, `gz_zero`, `gz_vacate`, `gz_error`; libc `vsnprintf`; `va_start`/`va_end`. 3. many early returns of `state->err`; one live `vsnprintf` branch. 4. writes `next[0..size)` in `in`; `next[size-1] = 0` first (I-5). 5. `(unsigned)len >= size`; `avail_in += (unsigned)len`; `x.pos += len`. 6. Section 7: `VaList` parameter; `gzprintf` passes the list through.

#### `gzflush` (L638-662), `gzsetparams` (L665-699), `gzclose_w` (L702-735), `gzclose` (gzclose.c L11-23)
1. `int ZEXPORT gzflush(gzFile, int)`; `int ZEXPORT gzsetparams(gzFile, int, int)`; `int ZEXPORT gzclose_w(gzFile)`; `int ZEXPORT gzclose(gzFile)`. 2. Lib: `gz_zero`, `gz_comp`, `deflateParams`, `deflateEnd`, `gz_error`; libc `free`, `close`; `gzclose` -> `gzclose_r`/`gzclose_w`. 3. early returns; `gzclose_w` runs `gz_zero`, `gz_comp(Z_FINISH)`, frees, `close`. 4. frees `out` (if not direct), `in`, `path`, the state. 5. `flush > Z_FINISH`. 6. Direct. `gzsetparams` ignores the result of `deflateParams` (section 10).

## 10. Surprising or possibly buggy

1. **`gzsetparams` silently does not apply new parameters (L694-697), reproduced.** `deflateParams` returns `Z_BUF_ERROR` and keeps the old level when the block flush it must do does not fit in `avail_out`; `gzsetparams` ignores that result, still stores `state->level/strategy` and returns `Z_OK`. **Run**: write `n` random bytes at `"wb6"`, `gzsetparams(f, 0, 0)` returns 0, then write 200,000 zero bytes; for 4 of 242 values of `n` (n = 16650, 32869, 49419, ...) the file is about `n` bytes instead of about 200,000 more, i.e. level 0 was not applied (the data stays valid). Confidence: reproduced, effect is on compression level only; not reported upstream. Scope: `gzsetparams` after output that nearly fills the 8192-byte buffer.
2. The three real findings of the earlier repository (R-1, R-2, R-3) are live in this source: see section 2.1.
3. R-4 (dangling `x.next` after a direct decompression into the user's buffer) was not reported before.
4. `gzlib.c` L261: `fcntl(fd, F_SETFL, fcntl(fd, F_GETFL) | O_NONBLOCK)` uses the result of `F_GETFL` even if it is `-1`.
5. `gzclose_r` treats any non-zero `close` result as `Z_ERRNO` (L726); `gzclose_w` only `-1` (L731).
6. `gz_error` frees `msg` only when the old `err` is not `Z_MEM_ERROR` (L562); the case cannot occur, so the guard is dead.
7. `gzgets` leaves `eol` uninitialised when `left == 0`; it is never read then.
8. The hang of `write` returning 0 (`gz_comp` L76-89, L110-123) is excluded by the OS contract, not by the code.

## 11. The five hardest functions (gz side)

1. `gz_read` with `gz_fetch`, `gz_look`, `gz_decomp`: a state machine on `how/eof/again/err/skip/x.have` over three buffers with a `continue` that skips the progress update.
2. `gz_comp` (with `gz_write`, `gz_zero`): pointer comparisons into `out`, a progress assumption on `write`, `again` semantics.
3. `gzseek64`: signed overflow with a negative position, three paths.
4. `gzvprintf`: `va_list` and `vsnprintf` into a half-used double buffer.
5. `gz_open`: many exits that must free exactly what is live, plus the `fcntl`/`open`/`lseek64` oracle calls.

## 12. Reproduction for item 1 of section 10

```c
/* gcc -I<zlib> sp2.c libz.a */
#include <stdio.h>
#include <stdlib.h>
#include "zlib.h"
int main(void){
  unsigned char *r = malloc(80000), *z = calloc(1,200000); unsigned s = 12345, i;
  for (i = 0; i < 80000; i++) { s = s*1103515245+12345; r[i] = (s>>16)&0xff; }
  for (unsigned n = 100; n < 80000; n += 331) {
    gzFile f = gzopen("t.gz","wb6");
    gzwrite(f, r, n); int rc = gzsetparams(f, 0, 0);
    gzwrite(f, z, 200000); gzclose(f);
    FILE *g = fopen("t.gz","rb"); fseek(g,0,SEEK_END); long sz = ftell(g); fclose(g);
    if (rc == 0 && sz < 100000 + (long)n) printf("n=%u rc=%d size=%ld\n", n, rc, sz);
  }
  return 0; }
```
