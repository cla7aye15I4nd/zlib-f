# Translation notes: `crc32.c`, `zutil.c`, `deflate.c`, `trees.c`, `compress.c`, `uncompr.c` and their headers

Analysis for the people who translate these files. It reads the C; it contains no proofs. Where a reading of the C
still has to be checked by a proof or a test it is marked **to confirm**. Facts were taken from the source and from
the output of the C preprocessor; a few facts were also checked by running the real C (marked **run**). A run is
evidence, not proof. The `gz*` files are in [gz-side.md](gz-side.md), the inflate files in
[inflate-side.md](inflate-side.md).

## 0. Source, line numbers, conventions

* Verified source: zlib commit `757f0527154291bcf6bfbd6396ecde6bedd2db95` (`ZLIB_VERSION "1.3.2.1-motley"`,
  `zlib.h` L44; `ZLIB_VERNUM 0x1321`). The only patch in this workspace, `patches/0003-adler32-null-one.patch`, changes
  `adler32.c` and `test/example.c` only. **None of the files in this document is patched in the workspace.**
  The earlier repository also had `0001` (`deflateBound_z`), `0002` (`gz_fetch`), `0004` (`gzseek64`) and `ub.patch`
  (`gz_reset`, `inflateCopy`). Their effect on the functions here is listed in section 2.4. Short version: none of them is
  needed for the *safety* of any function in this document; `0001` matters for one *correctness* statement
  (`deflateBound_z`).
* **Line numbers are those of the original, unpatched files** (`deflate.c` L1000 is `int ZEXPORT deflate(...)`). A line
  of the preprocessed file is written `pp:` plus the line number in the `gcc -E -P` output; `pp:` is used only for
  macro expansions and for "lines left after preprocessing". "Lines" in tables is the number of lines from the
  signature to the closing brace, blank lines and comments included.
* Configuration: default x86_64 Linux build, LP64, `./configure --static`. `configure` writes `CFLAGS=-O3 -fPIC
  -D_LARGEFILE64_SOURCE=1 -DHAVE_HIDDEN` into the Makefile, and changes `zconf.h` only at L446 and L450
  (`#if HAVE_UNISTD_H-0` becomes `#if 1`, the same for `HAVE_STDARG_H`). It found `vsnprintf` with the C99 return value,
  so neither `NO_vsnprintf` nor `HAS_vsnprintf_void` is defined. Every `#ifdef` below was decided by running
  `gcc -E -P -D_LARGEFILE64_SOURCE=1 -DHAVE_HIDDEN -DHAVE_UNISTD_H=1 -DHAVE_STDARG_H=1 -I <tree>` on the file
  and reading what is left (gcc 15.2, Ubuntu).
* Generated data was reproduced: `crc32.h` (591,749 bytes) is byte-identical to the output of `crc32.c` compiled with
  `-DMAKECRCH` and run; `trees.h` (8,472 bytes, 128 lines) is byte-identical to the file written by `trees.c` compiled
  with `-DGEN_TREES_H` when `_tr_init` runs (**run**). Details in section 3.
* Types (translation guide): `unsigned char` = `UInt8`, `unsigned short` = `UInt16`, `unsigned` and `uInt` = `UInt32`,
  `unsigned long`, `uLong`, `ulg`, `size_t`, `z_size_t` = `UInt64`, `int` = `Int32`, `long`, `z_off_t`, `z_off64_t` =
  `Int64`, an `enum` = `UInt32`. A pointer difference is `Int64`. `z_crc_t` is `unsigned` (`UInt32`, `zconf.h`, **run**:
  `typedef unsigned z_crc_t` in `pp:` of `crc32.c`), `z_word_t` is `unsigned long` (`UInt64`).
* Names: `end`, `from`, `in`, `have`, `at` are Lean keywords. The skeletons use `end_`, `from_`, `in_`, `have_`. This is a renaming only.
* Sanitizer evidence (**run**): the real `deflate.c`/`trees.c`/`zutil.c`/`crc32.c`/`adler32.c` were built with
  ASan and UBSan (`-fsanitize=address,undefined,shift,signed-integer-overflow,pointer-overflow,bounds,object-size,alignment,null`,
  all fatal) and driven with 8,000 random sessions: input 0 to 400,000 bytes of five kinds (random, zeros, text,
  period 300, runs), level -1..9, strategy 0..4, `windowBits` 8..15 as zlib, raw and gzip, `memLevel` 1..9, random
  input and output chunking down to 1 output byte, random `Z_PARTIAL/SYNC/FULL_FLUSH/Z_BLOCK`, `deflateParams` in
  mid-stream, `deflateCopy` in mid-stream; the output was inflated and compared. **No sanitizer report and no
  mismatch.** This is a test, not a proof; it did not exercise `deflateSetDictionary`, `deflatePrime`, a custom gzip header
  or `deflate_stored` with a 1-byte window.

### 0.1 Which branches of the C are live

| Macro | Value in the default build | Live / dead consequence |
| --- | --- | --- |
| `GZIP` | defined (`deflate.h` L22-24, `NO_GZIP` is not) | live: `GZIP_STATE` 57, wrap 2 handling in `deflateInit2_` (L428-433), `deflateResetKeep` (L663-670), `deflateBound_z` case 2, `deflate()` L1084-1228 and L1286-1298, `read_buf` L231-235 |
| `LIT_MEM` | **not** defined (`deflate.h` L28 is a comment) | live: single buffer `sym_buf`, `LIT_BUFS 4`, 3 bytes per symbol, `sym_end = (lit_bufsize-1)*3`. Dead: `d_buf`, `l_buf`, every `#ifdef LIT_MEM` branch (L514-517, L1390-1394, trees.c L909-911, L1096-1098). The struct has no `d_buf`/`l_buf` field |
| `FASTEST` | undefined | live: `configuration_table[10]`, hash chains (`prev`), `deflate_slow`, the long `longest_match` (L1418-1559), `INSERT_STRING` with `prev`, `slide_hash` second loop. Dead: the L1566-1615 `longest_match`, `deflateParams` `if (level != 0) level = 1` |
| `UNALIGNED_OK` | undefined | live: byte-wise `longest_match` (L1509-1541). Dead: L1433-1439, L1475-1507, L1547-1548 (the `ushf *` casts) |
| `TOO_FAR` | 4096 (`deflate.c` L89) | live: `#if TOO_FAR <= 32767` in `deflate_slow` L2033-2036 |
| `ZLIB_DEBUG` | undefined | `Assert`, `Trace*` expand to nothing; `check_match` is an empty macro; `_tr_tally_lit/dist` are the inline versions (`deflate.h` L327-376); `trees.c` `send_bits` is the macro (L274-286), `send_code` is `send_bits(s, tree[c].Code, tree[c].Len)` (L239); `bits_sent`, `compressed_len`, `z_verbose`, `z_error` do not exist. `_tr_tally` (trees.c L1095-1119) is still compiled and exported but **nothing in the library calls it** |
| `GEN_TREES_H` | undefined, and `STDC` defined | the tables come from `trees.h` (trees.c L113-114). `tr_static_init` has an **empty body** (trees.c L295-374 is entirely inside `#if defined(GEN_TREES_H) \|\| !defined(STDC)`); `_tr_init` still calls it. `gen_trees_header` and `static_init_done` do not exist |
| `NO_INIT_GLOBAL_POINTERS` | undefined | `TCONST` is `const`; `static_l_desc`, `static_d_desc`, `static_bl_desc` are initialised statics (trees.c L131-138) |
| `FORCE_STATIC`, `FORCE_STORED`, `DUMP_BL_TREE` | undefined | L1034-1036 and L1044-1049 take the plain branch; no `fprintf` |
| `DYNAMIC_CRC_TABLE`, `MAKECRCH`, `Z_ONCE` | undefined | tables come from `crc32.h`; `make_crc_table`, `braid`, `write_table*`, `main`, `x2n_table` local array, `made`, `z_once` do not exist; `get_crc_table` has no `z_once` call |
| `W`, `N`, `z_word_t` | `W = 8` (L89-90, `__x86_64__`), `N = 5` (L64), `z_word_t = unsigned long` (`Z_U8`) | live: braided `crc32_z` L626-941 with `N = 5` branches; the `#if N > 1 ... N > 5` blocks are all live up to `crc4`; **`crc5`/`word5` (the `N > 5` blocks) are dead** |
| `ARMCRC32` | undefined (`__aarch64__` not defined) | the L508-597 `crc32_z` is dead |
| `HAVE_S390X_VX` | undefined | `crc32()` calls `crc32_z` directly (L947-949 dead) |
| `Z_SOLO` | undefined | `zcalloc`, `zcfree` exist; `compress.c`/`uncompr.c` use the default allocator through `deflateInit`/`inflateInit` |
| `HAVE_MEMCPY` | defined (`STDC`) | `zmemcpy` = `memcpy`, `zmemcmp` = `memcmp`, `zmemzero(d, n)` = `memset(d, 0, n)` (`zutil.h` L207-219); the byte-loop `zmemcpy` etc. in `zutil.c` L151-180 are dead |
| `SYS16BIT`, `MY_ZCALLOC`, `M_I86`, `__TURBOC__` | undefined | only the generic `zcalloc`/`zcfree` at `zutil.c` L295-314 is live; `sizeof(uInt) > 2` is a constant true, so `zcalloc` is `malloc(items * size)` |
| `MAXSEG_64K` | undefined | `deflateCopy` is the full version (L1342-1405) |
| `sizeof(int) <= 2` | constant false | `fill_window` L267-280 is dead code that is still compiled; translate it as dead or omit with a comment |
| `MIN_MATCH != 3` | false | `fill_window` L319-321, `deflate_fast` L1959-1961 are not compiled |
| `_MSC_VER`, `__has_feature(memory_sanitizer)` | undefined / false | `#pragma` and `no_sanitize` lines are not compiled |
| `OS_CODE` | 3 (`zutil.h` L187-189, "assume Unix") | `put_byte(s, OS_CODE)` writes 3 (`deflate.c` L1100); the `gz_header.os` path writes `s->gzhead->os & 0xff` |
| `HAVE_HIDDEN` | defined | `ZLIB_INTERNAL` is `__attribute__((visibility ("hidden")))`; no semantic effect |
| `Z_U8`, `Z_U4` | `unsigned long`, `unsigned` | see `W` |
| `z_const`, `FAR`, `ZEXPORT`, `ZEXPORTVA` | empty | no effect |

## 1. (a) All functions: lines, count, difficulty

"Tr" is the difficulty of the **translation**, "Pf" of the **proof** (safety and, where it is small, correctness).
easy = straight-line or one small loop; medium = several loops, pointer arithmetic, allocation, or one non-obvious
invariant; hard = a long state machine, an arithmetic that mixes `unsigned`, `long` and `ulg`, an overlay of buffers, or
an invariant that is a theorem of its own.

Counts: crc32.c 13 (`byte_swap` and `crc_word_big` are compiled although only the big-endian branch uses them), zutil.c 5,
deflate.c 30, trees.c 21 (`tr_static_init` is compiled with an empty body, `_tr_tally` is compiled and never called),
compress.c 6, uncompr.c 4. Total **79 functions** compiled in the default build (the dead ones listed under each table are not
counted). The header macros of section 5 are not functions but need a `def` each.

### crc32.c (983 lines; `crc32.h` 9,446 lines of data)

| Function | Lines | Count | Tr | Pf | Why |
| --- | --- | --- | --- | --- | --- |
| `byte_swap` | L121-139 | 19 (10 live) | easy | easy | only used by the big-endian branch (L811, L911); pure bit mask and shift on `unsigned long` |
| `multmodp` | L163-178 | 16 | medium | medium | `for (;;)` with `break`; **does not terminate unless `a & 0xffffffff != 0`** (section 2, U-C1) |
| `x2nmodp` | L184-195 | 12 | easy | easy | `while (n)`, table index `k & 31`; calls `multmodp` |
| `get_crc_table` | L482-487 | 6 | easy | easy | returns a pointer to the static table |
| `crc_word` | L608-613 | 6 | easy | easy | 8-step loop over `crc_table` |
| `crc_word_big` | L615-621 | 7 | easy | easy | dead on little-endian, compiled |
| `crc32_z` | L626-941 | 316 (pp: 117) | **hard** | medium-hard | alignment by address (`(z_size_t)buf & 7`), cast `(z_word_t const *)buf`, runtime endian test through a pointer to a local, `while (--blks)`, five parallel braids, big-endian branch compiled |
| `crc32` | L946-951 | 6 | easy | easy | `uInt len` widened |
| `crc32_combine_gen64` | L954-961 | 8 | easy | easy | `len2 < 0` test, calls `x2nmodp` |
| `crc32_combine_gen` | L964-966 | 3 | easy | easy | cast |
| `crc32_combine_op` | L969-973 | 5 | easy | medium | calls `multmodp(op, crc1 & 0xffffffff)`: `op` is arbitrary; hangs for `op >= 2^32` with zero low word (**run**) |
| `crc32_combine64` | L976-978 | 3 | easy | easy | |
| `crc32_combine` | L981-983 | 3 | easy | easy | |

Dead in the default build (not counted): ARM `crc32_z` (L508-597), `make_crc_table`, `braid`, `write_table*`, `main`.

### zutil.c (316 lines)

| Function | Lines | Count | Tr | Pf | Why |
| --- | --- | --- | --- | --- | --- |
| `zlibVersion` | L27-29 | 3 | easy | easy | returns a pointer to a string literal |
| `zlibCompileFlags` | L31-121 | 91 (pp: 29) | easy | easy | four constant `switch` on `sizeof`, each with `break`; the result is the constant 169 (**run**) |
| `zError` | L139-141 | 3 | easy | easy | `ERR_MSG(err)` |
| `zcalloc` | L303-307 | 5 | easy | medium | `malloc(items * size)`: 32-bit multiply, not zeroed |
| `zcfree` | L309-312 | 4 | easy | easy | `free(ptr)` |

Dead: `z_error`, `z_verbose` (ZLIB_DEBUG), `zmemcpy`/`zmemcmp`/`zmemzero` functions (L151-180), the 16-bit `zcalloc` variants.

### deflate.c (2,221 lines)

| Function | Lines | Count | Tr | Pf | Why |
| --- | --- | --- | --- | --- | --- |
| `slide_hash` | L187-210 | 24 | easy | easy | two `do { ... } while (--n)` loops over `head` and `prev`; reads uninitialised `prev` |
| `read_buf` | L219-240 | 22 | easy | easy | `memcpy` from `next_in`, `adler32`/`crc32` callee, advances `next_in` |
| `fill_window` | L252-376 (pp: 63) | 125 | **hard** | **hard** | `do ... while` with `break`; `memcpy` with computed size; `slide_hash`; hash re-priming loop with `break`; high-water zeroing with three `ulg` quantities; many invariants |
| `deflateInit_` | L379-384 | 6 | easy | easy | one call |
| `deflateInit2_` | L387-532 | 146 | medium | medium | five `ZALLOC`, a function-pointer call, failure path with `deflateEnd`, sizes, `static const char my_version[]` |
| `deflateStateCheck` | L537-555 | 19 | easy | easy | type-confused read of `strm->state` if the state is an inflate state |
| `deflateSetDictionary` | L558-622 | 65 | medium | medium | calls `fill_window` twice, `UPDATE_HASH`, pointer into the caller's dictionary, temporary `wrap = 0` |
| `deflateGetDictionary` | L625-641 | 17 | easy | easy | `memcpy` with pointer arithmetic |
| `deflateResetKeep` | L644-690 | 47 | easy | easy | many field writes; `crc32(0L, Z_NULL, 0)`/`adler32(0L, Z_NULL, 0)` |
| `lm_init` | L695-715 | 21 | easy | easy | `CLEAR_HASH`, table lookups |
| `deflateReset` | L718-725 | 8 | easy | easy | |
| `deflateSetHeader` | L728-733 | 6 | easy | easy | stores a caller pointer |
| `deflatePending` | L736-748 | 13 | easy | easy | out-parameters through pointers |
| `deflateUsed` | L751-756 | 6 | easy | easy | |
| `deflatePrime` | L759-790 | 32 | medium | medium | byte-wise self-overlapping move in `pending_buf`, `do ... while (bits)`, signed `int` shifts |
| `deflateParams` | L793-835 | 43 | medium | medium | calls `deflate` (recursion between the API functions), function-pointer comparison, `slide_hash`/`CLEAR_HASH` |
| `deflateTune` | L838-849 | 12 | easy | easy | |
| `deflateBound_z` | L875-947 | 73 (pp: 55) | medium | medium | `switch` with `break` and a `do ... while (*str++)` string scan on caller memory, many unsigned overflow guards |
| `deflateBound` | L948-951 | 4 | easy | easy | |
| `putShortMSB` | L958-961 | 4 | easy | easy | two `put_byte` |
| `flush_pending` | L969-987 | 19 | easy | medium | `memcpy` to `next_out`, calls `_tr_flush_bits` |
| `deflate` | L1000-1309 | **310** (pp: 244) | **hard** | **hard** | state machine on `s->status`, 18 `return` statements, 3 loops with `return` inside, `strm->avail_out == 0` early exits, `HCRC_UPDATE` macro, function-pointer dispatch |
| `deflateEnd` | L1312-1329 | 18 | easy | medium | `TRY_FREE` x4, `ZFREE`, ownership |
| `deflateCopy` | L1336-1406 | 71 | **hard** | medium | whole-struct `memcpy`, then pointer fix-ups into the copy, partial `prev` copy with a data-dependent size, five allocations with unwinding |
| `longest_match` | L1418-1559 (pp: 50) | 142 | **hard** | **hard** | `do ... while` whose `continue` jumps to the condition; unrolled scan with 8 pre-increments; reads past `lookahead`; chain walk through `prev` |
| `deflate_stored` | L1700-1883 | 184 (pp: 115) | **hard** | **hard** | the hardest arithmetic: `unsigned`, `long` and `ulg` mixed; two phases; direct copy `next_in` to `next_out`; window slide; `MIN` macro on mixed types |
| `deflate_fast` | L1892-1983 | 92 (pp: 54) | medium | medium | `for (;;)` with `break` and macros that `return` |
| `deflate_slow` | L1991-2112 | 122 (pp: 72) | **hard** | **hard** | lazy matching state across iterations, macros that `return`, the `FLUSH_BLOCK_ONLY` without return |
| `deflate_rle` | L2120-2185 | 66 (pp: 53) | medium | medium | pointer scan with pre-increments, `strstart > 0` precondition for `scan = window + strstart - 1` |
| `deflate_huff` | L2191-2221 | 31 | easy | easy | |

Dead: the `FASTEST` `longest_match`, `check_match` (ZLIB_DEBUG).

### trees.c (1,119 lines; `trees.h` 128 lines of data)

| Function | Lines | Count | Tr | Pf | Why |
| --- | --- | --- | --- | --- | --- |
| `bi_reverse` | L154-161 | 8 | easy | easy | `do ... while (--len > 0)` |
| `bi_flush` | L166-176 | 11 | easy | medium | writes 0, 1 or 2 bytes to `pending_buf` without a capacity test |
| `bi_windup` | L181-193 | 13 | easy | medium | same; `bi_used = ((bi_valid - 1) & 7) + 1` |
| `gen_codes` | L203-232 | 30 | medium | medium | local array `next_code[16]` of `ush`, `continue`, post-increment as an argument |
| `tr_static_init` | L295-374 | 80 in the file, **0 live** | easy | easy | empty function in the default build |
| `init_block` | L440-451 | 12 | easy | easy | |
| `_tr_init` | L456-478 | 23 | easy | easy | sets pointers into the same struct and to static descriptors |
| `pqdownheap` | L509-528 | 20 | medium | medium | `smaller` macro, loop with `break`, indices into `heap` and `depth` |
| `gen_bitlen` | L540-613 | 74 (pp: 52) | **hard** | **hard** | length-limit repair with `while (s->bl_count[bits] == 0) bits--`, `continue` inside a `while`, `ulg` arithmetic that wraps on purpose |
| `build_tree` | L627-706 | 80 (pp: 41) | **hard** | **hard** | heap construction, `pqremove`, chained assignments, forced extra nodes |
| `scan_tree` | L712-747 | 36 | medium | medium | `continue` in `for`, writes a guard element past `max_code` |
| `send_tree` | L753-794 | 42 | medium | medium | `do ... while (--count != 0)` with macro bodies, depends on the guard from `scan_tree` |
| `build_bl_tree` | L800-826 | 27 | easy | medium | |
| `send_all_trees` | L833-855 | 23 | easy | easy | |
| `_tr_stored_block` | L860-875 | 16 | medium | medium | `memcpy` to `pending_buf + pending`, `put_short` x2 |
| `_tr_flush_bits` | L880-882 | 3 | easy | easy | |
| `_tr_align` | L888-895 | 8 | easy | easy | |
| `compress_block` | L900-951 | 52 | medium | **hard** | the overlay: reads `sym_buf` while writing `pending_buf` (same allocation) |
| `detect_data_type` | L966-991 | 26 | easy | easy | `unsigned long block_mask` shifted in the `for` increment |
| `_tr_flush_block` | L997-1089 | 93 | medium | **hard** | picks stored/fixed/dynamic by `ulg` arithmetic; the overlay proof lives here |
| `_tr_tally` | L1095-1119 | 25 | easy | easy | **dead code** in the default build (not called), but compiled |

### compress.c (99 lines), uncompr.c (101 lines)

| Function | Lines | Count | Tr | Pf | Why |
| --- | --- | --- | --- | --- | --- |
| `compress2_z` | compress.c L24-66 | 43 | medium | medium | local `z_stream` (address taken), `do ... while (err == Z_OK)` loop; chunked `uInt` limits; pointer difference `next_out - dest` |
| `compress2` | L67-74 | 8 | easy | easy | `&got` out-parameter; reads `*destLen` without a NULL test (**run**: segfault for `destLen == NULL`) |
| `compress_z` | L77-81 | 5 | easy | easy | |
| `compress` | L82-85 | 4 | easy | easy | |
| `compressBound_z` | L91-95 | 5 | easy | easy | overflow guards |
| `compressBound` | L96-99 | 4 | easy | easy | |
| `uncompress2_z` | uncompr.c L29-82 | 54 | medium | medium | local `z_stream`, `(Bytef *)&stream.reserved` as a dummy `next_out`, the same chunk loop, final arithmetic on `len`/`left` |
| `uncompress2` | L83-91 | 9 | easy | easy | two out-parameters |
| `uncompress_z` | L92-96 | 5 | easy | easy | `&used` |
| `uncompress` | L97-101 | 5 | easy | easy | |

## 2. (b) Undefined behaviour and sites that need a decision

Classes as in [inflate-side.md](inflate-side.md): **R** = a call that `zlib.h` allows reaches UB (or a non-terminating
loop, or an out-of-range read) in the C; **P** = UB only if the caller breaks a precondition; **I** = the C is correct only
because an invariant or an earlier test excludes it (the proofs discharge these); **D** = defined behaviour, but the
runtime model needs a decision. The Lean translation raises `Fault.ub` at R, P and I sites.

### 2.1 Class R

| Id | Site | What | Handled by |
| --- | --- | --- | --- |
| R-1 | `crc32.c` L163-178 `multmodp`, called from L972 `crc32_combine_op` | `multmodp(a, b)` loops until it finds a bit of `a` in positions 31..0 (`m` starts at `1 << 31`). If `a != 0` but `a & 0xffffffff == 0` then `m` reaches 0 after 32 iterations and the loop never ends (`a & m` stays 0, `a & (m - 1)` is never evaluated). `crc32_combine_op(1, 2, 1UL << 32)` hangs (**run**: killed by a timeout). `zlib.h` says `op` comes from `crc32_combine_gen`, which is `< 2^32`, so this is an API misuse, not a bug in documented use | translation: `while` with fuel (fuel exhaustion is a fault); the theorem for `crc32_combine_op` has the precondition `op >>> 32 = 0` (documented as narrower than the prototype) |
| R-2 | `compress.c` L70 `compress2`, `uncompr.c` L86 `uncompress2` | `*destLen` (and `*sourceLen`) are read **before** the `NULL` tests that `compress2_z`/`uncompress2_z` make. `compress2(d, NULL, s, 1, 6)` crashes (**run**: SIGSEGV). `zlib.h` documents `destLen` as a pointer to a length; a `NULL` `destLen` is a caller error, but the `_z` function was written to return `Z_STREAM_ERROR` for it | precondition `destLen != NULL` (P-class in practice) |

No other class R site was found in these files. In particular the `deflate`-side functions reach no UB from calls that
`zlib.h` allows (the sanitizer run of section 0 agrees, as evidence). The two `gz*` R sites are in gz-side.md.

### 2.2 Class P: caller preconditions that the C does not check

| Id | Site | Precondition |
| --- | --- | --- |
| P-1 | `deflate.c` L1137, L1164, L1186, L1207 (`s->gzhead->extra`, `->name`, `->comment`, `->hcrc`) | `gzhead != NULL` whenever `status` is `EXTRA_STATE`, `NAME_STATE`, `COMMENT_STATE` or `HCRC_STATE`. `deflateSetHeader(strm, NULL)` after the header has begun would break it. `zlib.h`: `deflateSetHeader` is called "before the first call of deflate". The invariant must tie `status` to `gzhead` |
| P-2 | `deflate.c` L1139-1143 | `gzhead->extra_len & 0xffff` and the `extra` buffer must not change between calls (`left = (extra_len & 0xffff) - gzindex` wraps if `extra_len` shrinks, then `zmemcpy` reads far beyond `extra`) |
| P-3 | `deflate.c` L1177, L1199, L920, L925 | `gzhead->name` and `->comment` are NUL-terminated within their block and do not change |
| P-4 | `deflate.c` L227 (`read_buf`, also called with `buf = next_out` at L1781), L1377 | `memcpy` with overlapping ranges is UB: the caller's `next_in` and `next_out` ranges must not overlap each other (in the heap model: two different blocks, or disjoint ranges); `deflateCopy` needs `dest != source` (L1377 `zmemcpy(dest, source, sizeof(z_stream))`) |
| P-5 | `deflate.c` L1004-1014 | `strm` was initialised by `deflateInit*`; `strm->state` is a deflate state, not an inflate state (the state check reads `s->strm` and `s->status` through the wrong struct type otherwise; the schema makes a wrong-kind cast a fault) |
| P-6 | `deflate.c` L394 | `version` is a NUL-terminated string (reads `version[0]`) |
| P-7 | `uncompr.c` L43 | none: `dest = (Bytef *)&stream.reserved` is never dereferenced because `avail_out == 0` (D-5) |

### 2.3 Class I: sites excluded by an invariant (obligations for the proofs)

| Id | Site | What must hold |
| --- | --- | --- |
| I-1 | every `put_byte`/`put_short`/`send_bits` (macros: `deflate.h` L293, `trees.c` L144-147, L274-286) | `pending < pending_buf_size` (or `pending + 2 <=`) before the store: **no capacity test anywhere**. This is the overlay lemma (trees.md section 7). Sites in `deflate()` (header, trailer, `putShortMSB`) hold because `pending == 0` or a flush just happened |
| I-2 | `deflate.h` L368-375 `_tr_tally_dist`: `dist--` on a `ush` | `dist >= 1`: with `dist == 0` the decrement wraps to 65535 and `d_code(65535)` indexes `_dist_code[767]` (the table has 512 entries). Holds: `strstart - match_start >= 1` because `match_start < strstart` (chain entries are older positions); `deflate_rle` passes 1 |
| I-3 | `deflate.h` L368-370, L357-363 (`sym_buf[sym_next++]`) | `sym_next + 3 <= 3 * lit_bufsize` before a tally. Holds because `sym_end = (lit_bufsize - 1) * 3` and every tally is followed by a test of `sym_next == sym_end` that flushes (`deflate_slow` L2101 tallies the pending literal without a test, but a flush follows at once) |
| I-4 | `trees.c` L585 `while (s->bl_count[bits] == 0) bits--;` | an index below `max_length` with a non-zero count exists when `overflow > 0` (Kraft); otherwise the loop reads `bl_count[-1]` and below |
| I-5 | `trees.c` L603 `m = s->heap[--h];` | `h > s->heap_max` inside the repair loop; `h` starts at `HEAP_SIZE` and the number of repaired items equals the number of leaves |
| I-6 | `trees.c` L563 `tree[tree[n].Dad].Len` | `Dad` was set for every `n` in `heap[heap_max+1 .. HEAP_SIZE-1]` by `build_tree` L684 |
| I-7 | `trees.c` L722 guard `tree[max_code + 1].Len = 0xffff`, L725 and L766 `tree[n + 1].Len` | `max_code + 1 <` the array length: `dyn_ltree` has 573 entries (`max_code <= 285`), `dyn_dtree` 61 (`max_code <= 29`). `send_tree` reads the guard that `scan_tree` wrote (same `max_code`) |
| I-8 | `trees.c` L729-736 `s->bl_tree[curlen].Freq`, L770-783 | `curlen` in `0..15` for real lengths; the guard value 0xffff is only ever `nextlen`, never `curlen` |
| I-9 | `deflate.c` L1511-1514, L1529-1533, L2143-2150 (reads up to index `strstart + 258` inclusive) | `strstart <= window_size - MIN_LOOKAHEAD` (`fill_window` post-condition, L374) so the reads are in the block; they may read bytes beyond `strstart + lookahead`: those are zero (L347-371) or stale; the result is clipped to `lookahead` (L1557-1558, L2152) |
| I-10 | `deflate.c` L1769 `s->window + s->block_start`, L1874 | `block_start >= 0` whenever `level == 0` (the model must fault otherwise, `long` offset negative). After `deflateParams` switches to level 0 the previous block was flushed (L810-818) so `block_start == strstart` |
| I-11 | `deflate.c` L1384-1385 `(slid \|\| strstart - insert > w_size ? w_size : strstart - insert) * sizeof(Pos)` | `insert <= strstart` (else the unsigned difference wraps and the `memcpy` size is huge). Maintained by L291-292, L1812-1813, L1845-1846 |
| I-12 | `deflate.c` L287 `zmemcpy(s->window, s->window + wsize, (unsigned)wsize - more)` | `more <= wsize` and the two ranges do not overlap (`wsize - more = strstart + lookahead - wsize <= wsize`). Holds because `strstart >= wsize + MAX_DIST` at that test |
| I-13 | `deflate.c` L1806-1809 `zmemcpy(window, window + w_size, strstart)` after `strstart -= w_size` | `strstart <= w_size` afterwards (the test is `window_size - strstart <= used < w_size`), so no overlap |
| I-14 | `deflate.c` L1801 `strm->next_in - s->w_size` | at least `w_size` bytes of `next_in` were consumed (`used >= w_size`), so the pointer stays in the caller's block |
| I-15 | `deflate.c` L2049 `max_insert = strstart + lookahead - MIN_MATCH` | no wrap: when `prev_length >= MIN_MATCH` the previous step had `lookahead >= prev_length` |
| I-16 | `deflate.c` L1817, L1853 `s->w_size - s->insert` | `insert <= w_size` |
| I-18 | `deflate.c` L1557-1558 and `deflate_slow` L2020-2029 | `longest_match` result is `<= lookahead`, so `lookahead -= prev_length - 1` (L2063) does not wrap |
| I-19 | `deflate.c` L291 `s->block_start -= (long)wsize` | signed `long`; cannot overflow (a block spans fewer than `sym_end` symbols of at most 258 bytes, so fewer than ~260 slides; **to confirm**) |
| I-20 | `deflate.c` L1140-1154 | `pending <= pending_buf_size` so `pending_buf_size - pending` does not wrap |
| I-21 | `crc32.c` L710, L832 `while (--blks)` | `blks >= 1`: before the alignment loop `len >= 47`; the loop removes at most 7; `blks = len / 40 >= 1`. With `blks == 0` the pre-decrement would wrap to `2^64 - 1` |
| I-22 | `crc32.c` L772-788 `words[0..N-1]` | the last block exists: `blks >= 1` full blocks of 40 bytes are in `[buf, buf + len)` |
| I-23 | `crc32.c` L190, L960 `x2n_table[k & 31]` | the mask keeps the index in range for every `k` |
| I-24 | `trees.c` L918-937 `compress_block` | the symbol buffer holds valid symbols: `lc <= 255`, `1 <= dist <= 32768`, so `_length_code[lc]`, `extra_lbits[code]`, `base_length[code]`, `d_code(dist)` (index `<= 511`), `base_dist[code]` are in range |
| I-25 | `trees.c` L1050-1056 | stored block: `stored_len + 4 <= opt_lenb` and `pending + stored_len + 4 <= pending_buf_size` (bounded because `opt_lenb` is a compressed size, **to confirm**; trees.md 7.5) |

### 2.4 The earlier repository's patches, per function

| Patch | Where | Needed by this document? |
| --- | --- | --- |
| `0001` (`deflateBound_z`, upstream PR 1360): `wraplen += 2 + (z_size_t)(s->gzhead->extra_len & 0xffff)` | `deflate.c` L915 | **No for safety.** In the live code `2 + s->gzhead->extra_len` is computed in `unsigned` (int `2` and `uInt`), so it wraps for `extra_len >= 0xFFFFFFFE`; the result is converted to `z_size_t` and added. No UB; the bound is simply too small by about 4 GiB. **Yes for a correctness theorem** "output size <= deflateBound_z" for gzip streams with a header whose `extra_len` is that large. `deflate()` itself writes only `extra_len & 0xffff` bytes (L1126-1127, L1139) |
| `0002` (`gz_fetch`), `0004` (`gzseek64`), `ub.patch` `gz_reset` | `gz*.c` | not in this file set (see gz-side.md) |
| `ub.patch` `inflateCopy` | `inflate.c` | not in this file set |
| `0003` (`adler32`) | `adler32.c` | present in the workspace. Relevant here because `read_buf` (L229) and `deflateResetKeep` (L671) call `adler32`: with the patch `adler32(0L, Z_NULL, 0)` and `adler32(a, Z_NULL, 1)` both return 1 |

No patch for `crc32.c`, `trees.c`, `compress.c`, `uncompr.c`, `zutil.c` exists or is needed.

### 2.5 Class D: defined behaviour that needs a model decision

| Id | Site | Decision |
| --- | --- | --- |
| D-1 | `crc32.c` L647, L649 `((z_size_t)buf & (W - 1)) != 0` | the value of a pointer as an integer: architecture says alignment per block (ghost alignment `a`, address mod 8 = `(a + offset) mod 8`). The result of `crc32_z` must not depend on `a`: state the theorem for all `a` |
| D-2 | `crc32.c` L655 `words = (z_word_t const *)buf` and L917 `buf = (unsigned char const *)words` | a read of 8 bytes as `unsigned long` from a `Bytef` block; strict aliasing is not respected by the C (an `unsigned char` array is read through `unsigned long`) but gcc compiles it as a plain load. Model: `ldU64LE` (8 bytes, little-endian) at an offset that is a multiple of 8 relative to the address, fault if out of range. Alignment is guaranteed by the preceding loop |
| D-3 | `crc32.c` L661-662 `unsigned endian = 1; if (*(unsigned char *)&endian)` | address-taken local of type `unsigned`, read as a byte. Little-endian x86: the byte is 1. Model: `endian := 1`, first byte `1`. Keep the big-endian branch (L790-912) and prove it unreachable, or omit it with a comment; the decision is the translators' (recommended: keep, 120 lines) |
| D-4 | `compress.c` L63 `stream.next_out - dest` | `NULL - NULL` when `dest == NULL` (then `deflate` returns `Z_STREAM_ERROR` and `next_out` is still `NULL`): allowed by the model |
| D-5 | `uncompr.c` L43 `(Bytef *)&stream.reserved` | a pointer to a field of a local struct, cast from `uLong *` to `Bytef *`. Model: any non-null pointer to an at least 1-byte block that is never dereferenced because `avail_out == 0` (`inflate` returns `Z_BUF_ERROR` before writing). Recommended: allocate a one-byte scratch block |
| D-6 | `deflate.c` L1239 `(*(configuration_table[s->level].func))(s, flush)` and L810 `func != configuration_table[level].func` | function pointers to local functions: model as an enum `{stored, fast, slow}` in `config`; equality of enums; `s->level` in `0..9` is an invariant (the table has 10 entries) |
| D-7 | `deflate.c` L401-413, L440-442, L457-459, L504, L1325 `ZALLOC`/`ZFREE` | call through `strm->zalloc`/`zfree`. Default: `zcalloc`/`zcfree` installed by `deflateInit2_` (L405, L413). A user allocator: `ub "custom allocator not modelled"` for now |
| D-8 | `deflate.c` L1788-1809, L1801 pointer arithmetic on `strm->next_in` | pointer minus `w_size` is inside the caller's block (I-14) |
| D-9 | `deflate.c` L1388 `ds->pending_out = ds->pending_buf + (ss->pending_out - ss->pending_buf)` | a pointer difference inside one block (`ss->pending_out` is in `ss->pending_buf`); model offsets |
| D-10 | `deflate.c` L1383-1386, L1360 `zmemcpy` of uninitialised bytes | copying indeterminate bytes is allowed and copies the "uninitialised" flags (architecture.md section 4); `prev` is partly uninitialised |
| D-11 | `deflate.c` L783, L786 `value >>= put` for a negative `value` | right shift of a negative `int` is implementation-defined (arithmetic shift in gcc), not UB. Model: arithmetic shift |
| D-12 | `trees.c` L158 `code >>= 1, res <<= 1` | comma operator, unsigned, defined |
| D-13 | `deflate.c` L1504, L1535, L2155 | `Assert` is compiled out (no `ZLIB_DEBUG`); do not translate asserts |

## 3. (c) Static tables and constants

Every table is read-only; a store through a pointer to one is a fault.

| Name | File and lines | Type and size | Where the content comes from |
| --- | --- | --- | --- |
| `static_ltree` | `trees.h` L3-62 (included at `trees.c` L114) | `const ct_data[288]` (`L_CODES+2`), 4 bytes each = 1,152 bytes. `fc` = code, `dl` = length: 0..143 -> 8 bits, 144..255 -> 9, 256..279 -> 7, 280..287 -> 8; codes are bit-reversed canonical codes | generated: `tr_static_init` (trees.c L295-374) under `-DGEN_TREES_H` writes `trees.h` through `gen_trees_header` (L388-434) (**run**: identical). Can be recomputed in Lean by `gen_codes` on the length list; entries 286 and 287 exist only to make the code canonical |
| `static_dtree` | `trees.h` L64-71 | `const ct_data[30]`; `Len = 5`, `Code = bi_reverse(n, 5)` | same |
| `_dist_code` | `trees.h` L73-100 (`deflate.h` L334-335 extern) | `const uch[512]`: entries 0..255 map distance-1 `< 256` to a code; entries 256..511 map `(distance-1) >> 7` ; **entries 256 and 257 are 0 and are never used** (`deflate.h` L324-325) | same |
| `_length_code` | `trees.h` L102-116 | `const uch[256]` (`MAX_MATCH-MIN_MATCH+1`); entry 255 is 28 (the overwrite at trees.c L330) | same |
| `base_length` | `trees.h` L118-121 | `const int[29]`: `0,1,..,8,10,12,14,16,20,...,224,0` | same |
| `base_dist` | `trees.h` L123-127 | `const int[30]`: `0,1,2,3,4,6,8,12,...,24576` | same |
| `extra_lbits` | `trees.c` L62-63 | `const int[29]`: `0 x8, 1 x4, 2 x4, 3 x4, 4 x4, 5 x4, 0` | literal in the source |
| `extra_dbits` | `trees.c` L65-66 | `const int[30]`: `0 x4, 1 x2, ... 13 x2` | literal |
| `extra_blbits` | `trees.c` L68-69 | `const int[19]`: `0 x16, 2, 3, 7` | literal |
| `bl_order` | `trees.c` L71-72 | `const uch[19]`: `16,17,18,0,8,7,9,6,10,5,11,4,12,3,13,2,14,1,15` | literal |
| `static_l_desc` | `trees.c` L131-132 | `static_tree_desc` {`static_ltree`, `extra_lbits`, 257, 286, 15} | literal; the struct `struct static_tree_desc_s` is defined at trees.c L117-123 (five fields: pointer to `ct_data`, pointer to `int`, `int` x3) |
| `static_d_desc` | L134-135 | {`static_dtree`, `extra_dbits`, 0, 30, 15} | literal |
| `static_bl_desc` | L137-138 | {`NULL`, `extra_blbits`, 0, 19, 7} | literal |
| `configuration_table` | `deflate.c` L112-124 | `const config[10]`, `config` = {`ush good_length, max_lazy, nice_length, max_chain; compress_func func`} (16 bytes). Rows: 0 {0,0,0,0,stored}, 1 {4,4,8,4,fast}, 2 {4,5,16,8,fast}, 3 {4,6,32,32,fast}, 4 {4,4,16,16,slow}, 5 {8,16,32,32,slow}, 6 {8,16,128,128,slow}, 7 {8,32,128,256,slow}, 8 {32,128,258,1024,slow}, 9 {32,258,258,4096,slow} | literal |
| `z_errmsg` | `zutil.c` L13-24 | `const char *const[10]`: "need dictionary", "stream end", "", "file error", "stream error", "data error", "insufficient memory", "buffer error", "incompatible version", "" | literal; index `2 - err` for `err` in -6..2, else 9 (`zutil.h` L65) |
| `crc_table` | `crc32.h` L5-57 | `const z_crc_t[256]` (`unsigned`), 1,024 bytes. `crc_table[n]` = CRC of the byte `n` for polynomial `0xedb88320` | generated by `make_crc_table` (crc32.c L243-402) compiled with `-DMAKECRCH` (**run**: identical) |
| `crc_big_table` | `crc32.h` L63-149 (the `W == 8` copy; the `W == 4` copy at L153-205 is dead) | `const z_word_t[256]`, 2,048 bytes; `crc_table[n]` byte-swapped. **Used only by `crc_word_big`** | generated |
| `crc_braid_table` | `crc32.h` L6365-6781 (`N == 5`, `W == 8`; the other 11 variants for `N = 1..6`, `W = 4, 8` are dead) | `const z_crc_t[8][256]` (`W` rows), 8,192 bytes. Row `k`: `multmodp(i << 24, x^((5*8+3-k)*8) mod p)` (`braid`, L461-473 with `n = 5`, `w = 8`) | generated |
| `crc_braid_big_table` | `crc32.h` L6783-7471 | `const z_word_t[8][256]`, 16,384 bytes; used only by the big-endian branch | generated |
| `x2n_table` | `crc32.h` L9439-9446 | `const z_crc_t[32]`: `x^(2^n) mod p`; first entries 0x40000000, 0x20000000, 0x08000000, 0x00800000, 0x00008000, 0xedb88320 | generated |
| `my_version` | `deflate.c` L392 (function-local `static const char[]`) | `"1.3.2.1-motley"` (15 bytes with the NUL); only `version[0]` is compared | literal from `zlib.h` L44 |
| `deflate_copyright` | `deflate.c` L54-55 | `const char[]`, never read | |
| string literals for `ERR_MSG` | see `z_errmsg` | `strm->msg` points to one of them | |
| `block_mask` | `trees.c` L971 | local `unsigned long` constant `0xf3ffc07f` | literal |

Sizes of the structs that `ZALLOC` needs (**run**, `sizeof` on x86_64): `z_stream` 112, `gz_header` 80, `deflate_state` 5,968,
`ct_data` 4 (align 2), `tree_desc` 24, `gzFile_s` 24. Offsets in `deflate_state` (for the difftest of the schema):
`pending_buf` 16, `dyn_ltree` 212 (2,292 bytes), `dyn_dtree` 2,504 (244), `bl_tree` 2,748 (156), `l_desc` 2,904 (24 each),
`bl_count` 2,976 (32), `heap` 3,008 (2,292), `depth` 5,308 (573), `bi_used` 5,944, `sym_buf` 5,888, `slid` 5,960.
Allocation sizes (`ZALLOC(strm, items, size)`, all far below 2^32): state 1 x 5,968; `window` `w_size` x 2 (max 65,536);
`prev` `w_size` x 2; `head` `hash_size` x 2 (max 131,072 for `memLevel` 9); `pending_buf` `lit_bufsize` x 4 (max 131,072).

## 4. (d) Struct fields that the code touches

Schema check: the generated schema must contain every field below, in declaration order, with the C type. Reading is
`R`, writing `W`. "macro" means through `put_byte`, `put_short`, `send_bits`, `INSERT_STRING`, `UPDATE_HASH`,
`CLEAR_HASH`, `FLUSH_BLOCK*`, `_tr_tally_*` (section 5).

### 4.1 `z_stream` (112 bytes) in these files

| Field | C type | Used |
| --- | --- | --- |
| `next_in` | `z_const Bytef *` | R/W: `read_buf`, `deflate_stored`, `deflateSetDictionary` (saved and restored), `compress2_z`, `uncompress2_z` |
| `avail_in` | `uInt` | R/W: same |
| `total_in` | `uLong` | W in `read_buf` L237 (also during `deflateSetDictionary`!), `deflateResetKeep`; R in the gzip trailer L1292-1295 |
| `next_out` | `Bytef *` | R/W: `flush_pending`, `deflate_stored`, `deflate` (NULL test), `compress2_z`, `uncompress2_z` |
| `avail_out` | `uInt` | R/W |
| `total_out` | `uLong` | W in `flush_pending`, `deflate_stored`, `deflateResetKeep` |
| `msg` | `z_const char *` | W: `deflateInit2_`, `deflateResetKeep`, `ERR_RETURN` |
| `state` | `struct internal_state *` | R/W: `deflateInit2_`, `deflateCopy`, `deflateEnd`, `deflateStateCheck` |
| `zalloc`, `zfree` | `alloc_func`, `free_func` | R/W: `deflateInit2_` (defaults), `deflateStateCheck` (tests non-null), `ZALLOC`/`ZFREE` |
| `opaque` | `voidpf` | R/W: `deflateInit2_`; passed to the allocators |
| `data_type` | `int` | W `deflateResetKeep` (`Z_UNKNOWN`), R/W `_tr_flush_block` L1006-1007 |
| `adler` | `uLong` | R/W: `read_buf`, `deflate` (header/trailer), `deflateSetDictionary`, `deflateResetKeep`, `HCRC_UPDATE` |
| `reserved` | `uLong` | never read or written; only its address in `uncompress2_z` L43 |

### 4.2 `deflate_state` (5,968 bytes), 61 fields in P0

All fields declared in `deflate.h` L104-288 exist except the ones inside `#ifdef LIT_MEM` (`d_buf`, `l_buf`) and
`#ifdef ZLIB_DEBUG` (`compressed_len`, `bits_sent`), which are absent. `bi_used` (L274) and `slid` (L285) are present. All 57 are
touched; `method` is written once (L529) and never read.

| Field | C type | Written by | Read by (besides the writers) |
| --- | --- | --- | --- |
| `strm` | `z_streamp` | `deflateInit2_` L444, `deflateCopy` L1379 | `deflateStateCheck`, `fill_window` (`s->strm->avail_in`), `deflate_stored`, `deflate_slow` L2088, `FLUSH_BLOCK*`, `_tr_flush_block` (`data_type`) |
| `status` | `int` | `deflateInit2_`, `deflateResetKeep`, `deflate` | `deflate`, `deflateEnd`, `deflateSetDictionary`, `deflateStateCheck` |
| `pending_buf` | `Bytef *` | `deflateInit2_` L504, `deflateCopy` L1364 | `put_byte`, `deflate` (HCRC), `deflateCopy`, `deflatePrime`, `deflateEnd`, `_tr_stored_block`, `flush_pending` |
| `pending_buf_size` | `ulg` | `deflateInit2_` L505 | `deflate`, `deflatePrime`, `deflate_stored` |
| `pending_out` | `Bytef *` | `deflateResetKeep`, `deflatePrime`, `deflateCopy`, `flush_pending` | same |
| `pending` | `ulg` | `put_byte`, `deflateResetKeep`, `deflate`, `flush_pending`, `_tr_stored_block` | many |
| `wrap` | `int` | `deflateInit2_`, `deflateResetKeep` (sign flip), `deflateSetDictionary` (temp 0), `deflate` L1307 (negated) | `deflate`, `deflateBound_z`, `read_buf`, `deflateSetHeader`, `FLUSH_BLOCK` |
| `gzhead` | `gz_headerp` | `deflateResetKeep` (NULL), `deflateSetHeader` | `deflate`, `deflateBound_z`, `HCRC_UPDATE` |
| `gzindex` | `ulg` | `deflate` | `deflate` |
| `method` | `Byte` | `deflateInit2_` | never |
| `last_flush` | `int` | `deflate`, `deflateResetKeep` | `deflate`, `deflateParams` |
| `w_size`, `w_bits`, `w_mask` | `uInt` | `deflateInit2_` | `fill_window`, `deflate` (header), `deflateBound_z`, `longest_match`, `deflateSetDictionary`, `deflate_stored`, `slide_hash`, `lm_init`, `INSERT_STRING` (`w_mask`) |
| `window` | `Bytef *` | `deflateInit2_`, `deflateCopy` | all matchers, `fill_window`, `deflate_stored`, `FLUSH_BLOCK_ONLY` (address of an element), `deflateEnd` |
| `window_size` | `ulg` | `lm_init` | `fill_window`, `deflate_stored`, `longest_match`, `deflate_rle` |
| `prev`, `head` | `Posf *` (`ush *`) | `deflateInit2_`, `deflateCopy`; contents by `INSERT_STRING`, `fill_window`, `deflateSetDictionary`, `slide_hash`, `CLEAR_HASH` | `longest_match` (`prev`), `slide_hash`, `deflateCopy`, `deflateEnd` |
| `ins_h` | `uInt` | `lm_init`, `UPDATE_HASH`, `fill_window`, `deflate_fast` | same |
| `hash_size`, `hash_bits`, `hash_mask`, `hash_shift` | `uInt` | `deflateInit2_` | `CLEAR_HASH`, `slide_hash`, `UPDATE_HASH`, `deflateBound_z`, `deflateCopy` |
| `block_start` | `long` | `lm_init`, `deflateResetKeep`, `deflateSetDictionary`, `fill_window`, `deflate`, `deflate_stored`, `FLUSH_BLOCK_ONLY` | `deflateParams`, `deflate_stored`, `FLUSH_BLOCK_ONLY` |
| `match_length`, `prev_match`, `match_available`, `match_start`, `prev_length` | `uInt`, `IPos`, `int`, `uInt`, `uInt` | `lm_init`, `deflateResetKeep`, `deflateSetDictionary`, `deflate_fast/slow/rle/huff`, `longest_match` (`match_start`), `fill_window` (`match_start -= wsize`) | same |
| `strstart`, `lookahead` | `uInt` | everywhere in the matchers | everywhere |
| `max_chain_length`, `max_lazy_match`, `good_match`, `nice_match` | `uInt`, `uInt`, `uInt`, `int` | `lm_init`, `deflateParams`, `deflateTune` | `longest_match`, `deflate_fast` (`max_insert_length` is a macro for `max_lazy_match`, deflate.h L186), `deflate_slow` |
| `level`, `strategy` | `int` | `deflateInit2_`, `deflateParams` | `deflate`, `deflateParams`, `deflate_slow`, `_tr_flush_block`, `deflateBound_z` |
| `dyn_ltree` | `struct ct_data_s[573]` | `init_block`, `_tr_tally`/macro, `build_tree`, `gen_bitlen`, `gen_codes`, `scan_tree` (guard) | `compress_block`, `detect_data_type`, `send_tree` |
| `dyn_dtree` | `struct ct_data_s[61]` | same | same |
| `bl_tree` | `struct ct_data_s[39]` | same | same |
| `l_desc`, `d_desc`, `bl_desc` | `struct tree_desc_s` (`dyn_tree` pointer into the arrays above, `max_code`, `stat_desc` pointer to a static descriptor) | `_tr_init` (pointers), `build_tree` (`max_code`), `deflateCopy` L1400-1402 (`dyn_tree` re-pointed) | `build_tree`, `gen_bitlen`, `_tr_flush_block`, `build_bl_tree` |
| `bl_count` | `ush[16]` | `gen_bitlen` | `gen_codes` |
| `heap` | `int[573]` | `build_tree`, `pqdownheap`, `pqremove` | same, `gen_bitlen` |
| `heap_len`, `heap_max` | `int` | `build_tree`, `pqremove` (`heap_len--`) | `pqdownheap`, `gen_bitlen` |
| `depth` | `uch[573]` | `build_tree` | `pqdownheap` via `smaller` |
| `sym_buf` | `uchf *` | `deflateInit2_` L519, `deflateCopy` L1396 | `_tr_tally_*`, `compress_block`, `deflateCopy` |
| `lit_bufsize` | `uInt` | `deflateInit2_` | `deflateCopy` |
| `sym_next`, `sym_end` | `uInt` | `deflateInit2_` (`sym_end`), `init_block` (`sym_next = 0`), `_tr_tally_*` | `deflate_*` (`if (s->sym_next)`), `compress_block`, `_tr_tally_*` |
| `opt_len`, `static_len` | `ulg` | `init_block`, `gen_bitlen`, `build_tree`, `build_bl_tree` | `_tr_flush_block` |
| `matches` | `uInt` | `init_block` (0), `lm_init`, `deflateResetKeep`, `deflateParams`, `deflate_stored` | `deflateParams`, `deflateResetKeep`, `deflate_stored` |
| `insert` | `uInt` | `lm_init`, `fill_window`, `deflateSetDictionary`, `deflate`, `deflate_*` | `fill_window`, `deflate_stored`, `deflateCopy` |
| `bi_buf` | `ush` | `_tr_init`, `send_bits`, `bi_flush`, `bi_windup`, `deflatePrime` | same |
| `bi_valid` | `int` | same | same, `deflatePending`, `deflate_stored` |
| `bi_used` | `int` | `_tr_init`, `bi_windup`, `deflate_stored` L1826 and L1881 | `deflateUsed` |
| `high_water` | `ulg` | `deflateInit2_`, `fill_window`, `deflate_stored` | `deflateCopy`, `fill_window`, `deflate_stored` |
| `slid` | `int` | `CLEAR_HASH` (0), `slide_hash` (1) | `deflateCopy` |

Static union `ct_data`: `{ union { ush freq; ush code; } fc; union { ush dad; ush len; } dl; }`. `Freq`, `Code` are the macros
`fc.freq`, `fc.code`; `Dad`, `Len` are `dl.dad`, `dl.len` (`deflate.h` L83-86). Both members of each union have the same
type, so the schema has two `UInt16` fields `fc`, `dl`; `Freq` and `Code` are the same cell, `Dad` and `Len` the same cell.
Code that writes `Dad` and later reads `Len` (`gen_bitlen` L563-565: "We overwrite tree[n].Dad which is no longer needed")
and code that writes `Freq` then `Code` relies on this.

`tree_desc`: `{ ct_data *dyn_tree; int max_code; const static_tree_desc *stat_desc; }` (24 bytes). `static_tree_desc`
(trees.c L117-123): `{ const ct_data *static_tree; const intf *extra_bits; int extra_base; int elems; int max_length; }`.
`config` (deflate.c L98-104): `{ ush good_length, max_lazy, nice_length, max_chain; compress_func func; }`.

### 4.3 `gz_header` (80 bytes), read only, through `s->gzhead`

`text` (R L1111), `time` (R L1117-1120), `os` (R L1124), `extra` (R L914, L1113, L1125, L1137, L1143, L1156),
`extra_len` (R L915, L1126-1127, L1139), `name` (R L916, L1114, L1164, L1177), `comment` (R L921, L1115, L1186, L1199),
`hcrc` (R L926, L1112, `HCRC_UPDATE`, L1129, L1207). Not read in these files: `xflags`, `extra_max`, `name_max`, `comm_max`, `done`.

## 5. Macros: exact expansion, reads and writes

Macros that contain `return`, `goto` or `break` are marked **control**. There is no `goto` in any of these files.
`s` and `strm` below are the names in scope at the use; several macros capture them from the caller (`HCRC_UPDATE`).

| Macro | Definition (file, lines) | Reads | Writes | Notes |
| --- | --- | --- | --- | --- |
| `put_byte(s, c)` | `{s->pending_buf[s->pending++] = (Bytef)(c);}` (`deflate.h` L293) | `pending_buf`, `pending`, `c` | `pending_buf[pending]`, `pending` | block statement; no capacity test (I-1) |
| `put_short(s, w)` | `{ put_byte(s, (uch)((w) & 0xff)); put_byte(s, (uch)((ush)(w) >> 8)); }` (`trees.c` L144-147) | | | `w` is evaluated twice (always `s->bi_buf` or a pure cast) |
| `send_bits(s, value, length)` | `{ int len = length; if (s->bi_valid > (int)Buf_size - len) { int val = (int)value; s->bi_buf \|= (ush)val << s->bi_valid; put_short(s, s->bi_buf); s->bi_buf = (ush)val >> (Buf_size - s->bi_valid); s->bi_valid += len - Buf_size; } else { s->bi_buf \|= (ush)(value) << s->bi_valid; s->bi_valid += len; } }` (`trees.c` L274-286; `Buf_size` = 16) | `bi_valid`, `bi_buf`, `value`, `length` | `bi_buf`, `bi_valid`, `pending_buf`, `pending` | declares locals `len` and `val`: an argument that mentions a variable of that name would be captured. **No call in the library does** (checked: every call site in `trees.c`, listed by `grep`). `(ush)val << bi_valid`: `ush` promotes to `int`; the shift count is `0..16`; with count 16 the value is below `2^15` (length `<= 15`) so no signed overflow; **run**: not reported by UBSan `shift`. `bi_buf \|= int` converts back to `ush` (truncating) |
| `send_code(s, c, tree)` | `send_bits(s, tree[c].Code, tree[c].Len)` (`trees.c` L239) | `tree[c].fc`, `tree[c].dl` | as `send_bits` | `tree` is a macro parameter: `send_code(s, curlen, s->bl_tree)` becomes `s->bl_tree[curlen].fc.code` |
| `UPDATE_HASH(s, h, c)` | `(h = (((h) << s->hash_shift) ^ (c)) & s->hash_mask)` (`deflate.c` L141) | `h`, `hash_shift`, `hash_mask`, `c` | `h` | `h` is `s->ins_h` or a local; shift count `hash_shift <= 6`, `ins_h < 2^16`, so no wrap |
| `INSERT_STRING(s, str, match_head)` | `(UPDATE_HASH(s, s->ins_h, s->window[(str) + (MIN_MATCH-1)]), match_head = s->prev[(str) & s->w_mask] = s->head[s->ins_h], s->head[s->ins_h] = (Pos)(str))` (L160-163) | `ins_h`, `hash_shift`, `hash_mask`, `window[str+2]`, `w_mask`, `head[ins_h]` | `ins_h`, `prev[str & w_mask]`, `head[ins_h]`, `match_head` | a comma expression; `str` is evaluated up to 4 times and is `s->strstart`, which is not changed inside; the chained assignment stores the `ush` read from `head` into `prev` and then assigns the `ush` value to `match_head` (type `IPos`, so zero-extended); `(Pos)(str)` truncates to 16 bits (`strstart < 65536`) |
| `CLEAR_HASH(s)` | `do { s->head[s->hash_size - 1] = NIL; zmemzero(s->head, (unsigned)(s->hash_size - 1)*sizeof(*s->head)); s->slid = 0; } while (0)` (L170-175) | `head`, `hash_size` | `head[0..hash_size-1]`, `slid` | the `memset` covers `hash_size - 1` entries (the cast is to `unsigned`, then multiplied by `size_t 2`) |
| `RANK(f)` | `(((f) * 2) - ((f) > 4 ? 9 : 0))` (L133) | | | `f` in -2..5: no overflow |
| `MIN(a, b)` | `((a) > (b) ? (b) : (a))` (L1683) | | | arguments are evaluated twice; types follow the usual conversions (L1705: `ulg` and `uInt`; L1817: `uInt` and `uInt`; L1865: `ulg` and `int` -> `ulg`) |
| `HCRC_UPDATE(beg)` | `do { if (s->gzhead->hcrc && s->pending > (beg)) strm->adler = crc32_z(strm->adler, s->pending_buf + (beg), s->pending - (beg)); } while (0)` (L992-997) | `s`, `strm` (**captured from the caller**), `gzhead->hcrc`, `pending`, `pending_buf`, `strm->adler` | `strm->adler` | used at L1145, L1158, L1169, L1180, L1191, L1202; `beg` is a `ulg` local |
| `FLUSH_BLOCK_ONLY(s, last)` | `{ _tr_flush_block(s, (s->block_start >= 0L ? (charf *)&s->window[(unsigned)s->block_start] : (charf *)Z_NULL), (ulg)((long)s->strstart - s->block_start), (last)); s->block_start = s->strstart; flush_pending(s->strm); Tracev((stderr,"[FLUSH]")); }` (L1659-1668) | `block_start`, `window`, `strstart`, `strm` | `block_start` (and everything `_tr_flush_block` and `flush_pending` write) | `Tracev` expands to nothing, leaving an empty statement; `&s->window[(unsigned)s->block_start]` is the address of an element |
| `FLUSH_BLOCK(s, last)` | `{ FLUSH_BLOCK_ONLY(s, last); if (s->strm->avail_out == 0) { if (!(last)) return need_more; if (s->pending != 0 \|\| s->wrap != 0) return finish_started; } }` (L1671-1677) | `strm->avail_out`, `pending`, `wrap` | | **control**: `return` from the enclosing function. For `last = 1` and `avail_out == 0` with `pending == 0 && wrap == 0` it falls through to the code after the macro (`return finish_done`) |
| `_tr_tally_lit(s, c, flush)` | `{ uch cc = (c); s->sym_buf[s->sym_next++] = 0; s->sym_buf[s->sym_next++] = 0; s->sym_buf[s->sym_next++] = cc; s->dyn_ltree[cc].Freq++; flush = (s->sym_next == s->sym_end); }` (`deflate.h` L357-364) | `sym_next`, `sym_end`, `c` | `sym_buf[..]`, `sym_next`, `dyn_ltree[cc].fc`, `flush` | `c` is evaluated once, before the stores; `.Freq++` on `ush` wraps modulo 65536 (unreachable: at most 32,767 symbols) |
| `_tr_tally_dist(s, distance, length, flush)` | `{ uch len = (uch)(length); ush dist = (ush)(distance); s->sym_buf[s->sym_next++] = (uch)dist; s->sym_buf[s->sym_next++] = (uch)(dist >> 8); s->sym_buf[s->sym_next++] = len; dist--; s->dyn_ltree[_length_code[len]+LITERALS+1].Freq++; s->dyn_dtree[d_code(dist)].Freq++; flush = (s->sym_next == s->sym_end); }` (L365-375) | `sym_next`, `sym_end`, `_length_code`, `_dist_code`, `distance`, `length` | `sym_buf[..]`, `sym_next`, `dyn_ltree[..].fc`, `dyn_dtree[..].fc`, `flush` | declares locals `len` and `dist`: no argument uses those names (the arguments are `s->strstart - s->match_start`, `s->match_length - MIN_MATCH`, `s->strstart - 1 - s->prev_match`, `s->prev_length - MIN_MATCH`, `1`, `s->match_length - MIN_MATCH`). `dist--` on a `ush`: `dist == 0` gives 65535 (I-2). `(uch)dist` and `(uch)(dist >> 8)` are the low and high byte |
| `d_code(dist)` | `((dist) < 256 ? _dist_code[dist] : _dist_code[256+((dist)>>7)])` (`deflate.h` L320-321) | `_dist_code` | | `dist` must have no side effect; the index is `<= 511` for `dist <= 32767` |
| `pqremove(s, tree, top)` | `{ top = s->heap[SMALLEST]; s->heap[SMALLEST] = s->heap[s->heap_len--]; pqdownheap(s, tree, SMALLEST); }` (`trees.c` L488-493; `SMALLEST` = 1) | `heap[1]`, `heap[heap_len]`, `heap_len` | `top`, `heap[1]`, `heap_len` | **evaluation order**: the read `s->heap[s->heap_len--]` uses the old `heap_len` and then decrements; the call to `pqdownheap` sees the new `heap_len` |
| `smaller(tree, n, m, depth)` | `(tree[n].Freq < tree[m].Freq \|\| (tree[n].Freq == tree[m].Freq && depth[n] <= depth[m]))` (L499-501) | | | `n` and `m` are `s->heap[j+1]`, `s->heap[j]`, `v` (pure expressions evaluated several times) |
| `ERR_MSG(err)` | `z_errmsg[(err) < -6 \|\| (err) > 2 ? 9 : 2 - (err)]` (`zutil.h` L65) | | | |
| `ERR_RETURN(strm, err)` | `return (strm->msg = ERR_MSG(err), (err))` (L67-68) | | `strm->msg` | **control**: `return`. Used in `deflate` at L1012, L1014, L1039, L1044 (with `Z_STREAM_ERROR` or `Z_BUF_ERROR`) |
| `ZALLOC(strm, items, size)` | `(*((strm)->zalloc))((strm)->opaque, (items), (size))` (`zutil.h` L252-253) | `zalloc`, `opaque` | | call through a function pointer; `size_t` argument converted to `unsigned` |
| `ZFREE(strm, addr)` | `(*((strm)->zfree))((strm)->opaque, (voidpf)(addr))` | | | |
| `TRY_FREE(s, p)` | `{if (p) ZFREE(s, p);}` | | | block statement |
| `zmemcpy(d, s, n)`, `zmemzero(d, n)`, `zmemcmp` | `memcpy`, `memset(d, 0, n)`, `memcmp` (`zutil.h` L216-218) | | | `n` of type `unsigned` or `size_t` |
| `Assert`, `Trace*`, `check_match` | empty | | | no statement |
| `NIL` | 0; `MAX_STORED` 65535; `WIN_INIT` = `MAX_MATCH` = 258; `MIN_LOOKAHEAD` = 262; `MAX_DIST(s)` = `s->w_size - 262`; `MAX_WBITS` 15; `MAX_MEM_LEVEL` 9; `DEF_MEM_LEVEL` 8; `Z_NULL` 0; `PRESET_DICT` 0x20; `OS_CODE` 3; `LITERALS` 256; `LENGTH_CODES` 29; `L_CODES` 286; `D_CODES` 30; `BL_CODES` 19; `HEAP_SIZE` 573; `MAX_BITS` 15; `MAX_BL_BITS` 7; `END_BLOCK` 256; `REP_3_6` 16; `REPZ_3_10` 17; `REPZ_11_138` 18; `STORED_BLOCK` 0; `STATIC_TREES` 1; `DYN_TREES` 2; `Buf_size` 16; status codes `INIT_STATE` 42, `GZIP_STATE` 57, `EXTRA_STATE` 69, `NAME_STATE` 73, `COMMENT_STATE` 91, `HCRC_STATE` 103, `BUSY_STATE` 113, `FINISH_STATE` 666 | | | constants (`Headers/` equivalents) |
| `max_insert_length` | `#define max_insert_length max_lazy_match` (`deflate.h` L186) | | | an alias of a struct field name |
| `Freq`, `Code`, `Dad`, `Len` | `fc.freq`, `fc.code`, `dl.dad`, `dl.len` (`deflate.h` L83-86) | | | field aliases (see 4.2) |
| `ZSWAP32`, `GT_OFF`, `Z_ONCE` | not used in this file set | | | |

## 6. Cross-cutting decisions for the translators

1. **Early return from inside a loop.** `deflate()` has three loops with `return` inside (L1140-1154, L1167-1179,
   L1189-1201); `FLUSH_BLOCK` returns from inside the `for (;;)` of the five `deflate_*` functions; `fill_window`,
   `longest_match`, `deflate_stored` have `break`. Follow the guide: a control tag in the loop state, e.g.
   `inductive Ctl (α) | next | brk | ret (v : α)`. Straight-line early returns (the 18 returns of `deflate()` outside loops)
   can use the monad's `return`. A macro that returns is a `def` that yields `Option BlockState` (`none` = fall through).
2. **`do { } while (cond)` with `continue`** (`longest_match` L1463-1555): `continue` jumps to the condition, which
   performs `cur_match = prev[cur_match & wmask]` and `--chain_length`. The body therefore returns one of three tags:
   `skip` (run the condition), `stop` (`break`), `go` (run the condition). Translate the condition once, after the body.
3. **Pointers into the same struct.** `l_desc.dyn_tree` etc. point into `dyn_ltree`/`dyn_dtree`/`bl_tree`; `build_tree`
   gets `tree_desc *desc = &s->l_desc`. Use the pointer constructors of the schema (`inState ref idx`); `tree` in
   `gen_codes`, `scan_tree`, `send_tree` is a pointer to the start of one of the three arrays (offset 0).
4. **`pending_buf` and `sym_buf` are one allocation** (`sym_buf = pending_buf + lit_bufsize`, L519). The model must keep
   them in the same byte block and compute `sym_buf` as a pointer with offset `lit_bufsize`. The overlay lemma
   (docs/proof/trees.md section 7) is about this.
5. **Whole-struct copy** (`deflateCopy` L1360): a value copy of the record, followed by the pointer fix-ups of L1361-1402.
   `ds->strm`, `ds->gzhead`, `ds->l_desc.stat_desc`, `ds->d_desc.stat_desc`, `ds->bl_desc.stat_desc` stay as copied.
6. **Out-parameters.** `deflatePending(strm, unsigned *pending, int *bits)`, `deflateGetDictionary(.., uInt *dictLength)`,
   `compress2_z(.., z_size_t *destLen ..)`, `uncompress2_z(.., z_size_t *destLen, z_size_t *sourceLen)`, `compress2`
   (`&got`), `uncompress2` (`&got`, `&used`), `uncompress_z` (`&used`), `uncompress` (`&used`). Pass a pointer to a heap cell
   that the caller allocated (the callers in the tests will do), or return the new value and let the wrapper write it.
   Mixed: `deflatePending` writes `*pending` **twice** (L741, L743) when it overflows: keep both writes.
7. **Integer promotions that matter.** `ush` operands become `int` (`tree[n].Freq < tree[m].Freq`, `s->bl_tree[curlen].Freq +=
   (ush)count`, `(ush)val << s->bi_valid`); `uch` become `int`; `Byte scan_end = scan[best_len]` is `UInt8`;
   comparisons between `uInt` and `ulg` happen in `ulg`; `long` and `uInt` mix in `long` (`(long)s->strstart - s->block_start`,
   `s->block_start -= s->w_size`); `int` and `uInt` mix in `uInt` (`s->bi_valid + 42` is cast first at L1720, L1863).
8. **`Tracev`/`Assert` statements** are empty in the default build; a `;` left behind is an empty statement.

## 7. Function by function

Each section has the six items: (1) signature and size, (2) callees, (3) control flow that needs a decision,
(4) memory behaviour, (5) integer rules, (6) proposed translation. "Lib" = functions of the library, "libc" = C library.
Skeletons are Lean-shaped sketches, not code to paste; `M` is the runtime monad, `Fault.ub` the fault.
Names of runtime operations (`ldB`, `stB`, `padd`, `memcpyB`, `allocB`, `whileF`) are placeholders for those of `ZlibF/Runtime/`.

### 7.1 `crc32.c`

Live configuration: `W = 8`, `N = 5`, little-endian, no ARM. The tables are section 3.

#### `byte_swap` (L121-139; live lines L122-131; 19 lines)
1. `local z_word_t byte_swap(z_word_t word)`. The `W == 4` branch (L132-137) is dead.
2. Lib: none. libc: none.
3. Straight line: one `return` of an `|` of eight masked shifts.
4. None.
5. `(word & 0xff00000000000000) >> 56 | ... | (word & 0xff) << 56` all in `unsigned long`; the left shifts discard bits on purpose; counts 8..56 are in range.
6. Pure `def byteSwap64 (w : UInt64) : UInt64`; called only from the big-endian branch (L811, L911).

#### `multmodp` (L163-178; 16 lines)
1. `local uLong multmodp(uLong a, uLong b)`.
2. Lib: none.
3. `for (;;)` with one `break` (L172) inside an `if` inside an `if`. Order inside one iteration: (i) if `a & m`: `p ^= b`, and if `(a & (m - 1)) == 0` break (the shift of `m` and the update of `b` are then skipped); (ii) `m >>= 1`; (iii) `b = b & 1 ? (b >> 1) ^ POLY : b >> 1`.
4. None (pure on `uLong`). `POLY` is `0xedb88320`.
5. All `unsigned long`; `m` starts at `(uLong)1 << 31` (a shift by 31 of a 64-bit value). `m - 1` when `m == 0` would be `2^64 - 1` but is only evaluated when `a & m != 0`, so `m != 0`. **Non-termination (R-1)** when `a & 0xffffffff == 0`.
6. Loop with fuel (fault on exhaustion, as the loop rule requires):
   ```lean
   def multmodp (a b : UInt64) : M UInt64 :=
     whileF (m := (1:UInt64) <<< 31, b, p := 0) fun (m, b, p) =>
       if a &&& m != 0 then
         let p := p ^^^ b
         if a &&& (m - 1) == 0 then return .brk p
         else return .next (m >>> 1, step b, p)
       else return .next (m >>> 1, step b, p)
   ```
   Keep `m - 1` inside the `then` branch; do not hoist it.

#### `x2nmodp` (L184-195; 12 lines)
1. `local uLong x2nmodp(z_off64_t n, unsigned k)`.
2. Lib: `multmodp`. Data: `x2n_table` (32 entries, section 3).
3. `while (n)`; no `break`.
4. Reads `x2n_table[k & 31]`.
5. `n & 1` and `n >>= 1` on a **signed** `long` that the caller guarantees non-negative (L955 for `crc32_combine_gen64`; **P**: `n >= 0`); `k++` is `unsigned` and wraps in principle (`k <= 3 + 63`); `p` starts at `(uLong)1 << 31`.
6. Loop state `(n, k, p)`. A negative `n` would make `n >>= 1` converge to -1 and never reach 0: the fuel catches it; the caller test makes it unreachable. The result of `multmodp(x2n_table[k & 31], p)` is `uLong`.

#### `get_crc_table` (L482-487; 6 lines)
1. `const z_crc_t FAR * ZEXPORT get_crc_table(void)`.
2. None (the `z_once` call is under `DYNAMIC_CRC_TABLE`).
3. None.
4. Returns a pointer to the static `crc_table` (read-only).
5. None.
6. Return the constructor for the static table (`st_crc_table`, index 0).

#### `crc_word` (L608-613; 6 lines) and `crc_word_big` (L615-621; 7 lines)
1. `local z_crc_t crc_word(z_word_t data)`; `local z_word_t crc_word_big(z_word_t data)`.
2. Lib: none. Data: `crc_table` (`crc_word`), `crc_big_table` (`crc_word_big`).
3. `for (k = 0; k < W; k++)` with `k` an `int`, 8 iterations.
4. Reads the static tables with an index `data & 0xff` (`crc_word`) or `(data >> ((W-1) << 3)) & 0xff` = `data >> 56 & 0xff` (`crc_word_big`).
5. `data >> 8`, `data << 8` on `unsigned long`; `(z_crc_t)data` truncates to 32 bits. After 8 steps of `(data >> 8) ^ T[..]` the result is below `2^32`, so the cast loses nothing (**to confirm**).
6. Two pure loops over `Fin 8`; the table index is `(data &&& 0xff).toNat` and the table lookup is total because the table has 256 entries.

#### `crc32_z` (L626-941; 316 lines; pp: 117 lines)
1. `uLong ZEXPORT crc32_z(uLong crc, const unsigned char FAR *buf, z_size_t len)`.
2. Lib: `crc_word` (L772-780), `crc_word_big` (L894-904, dead), `byte_swap` (L811, L911, dead). Data: `crc_table`, `crc_braid_table`, `crc_braid_big_table`. libc: none.
3. No `goto`, no `switch`. Order of the body:
   (a) `if (buf == Z_NULL) return 0;` (L628) early return.
   (b) `crc = (~crc) & 0xffffffff;` (L635).
   (c) `if (len >= N * W + W - 1)` (L640; 47): the braided part.
       - `while (len && ((z_size_t)buf & (W - 1)) != 0)` (L647-650): byte loop until aligned; per step `len--; crc = (crc >> 8) ^ crc_table[(crc ^ *buf++) & 0xff];`.
       - `blks = len / (N * W); len -= blks * N * W; words = (z_word_t const *)buf;` (L653-655).
       - `endian = 1; if (*(unsigned char *)&endian) { little } else { big }` (L661-662, L790).
       - little endian (L662-789): declare `crc0..crc4`, `word0..word4`; `crc0 = (z_crc_t)crc; crc1..crc4 = 0;` then `while (--blks) { ... }` (L710-766) whose body loads `wordI = crcI ^ words[I]` (I = 0..4), `words += N;` then `crcI = crc_braid_table[0][wordI & 0xff]` for all I, then `for (k = 1; k < W; k++) crcI ^= crc_braid_table[k][(wordI >> (k << 3)) & 0xff]` for all I; after the loop the last block: `crc = crc_word(crc0 ^ words[0]); crc = crc_word(crc1 ^ words[1] ^ crc); ... crc = crc_word(crc4 ^ words[4] ^ crc); words += N;` (L772-788).
       - big endian (L790-912): same shape with `crc_braid_big_table`, `byte_swap`, `crc_word_big`, `comb`; compiled but never run on x86.
       - `buf = (unsigned char const *)words;` (L917).
   (d) `while (len >= 8) { len -= 8; 8 x crc = (crc >> 8) ^ crc_table[(crc ^ *buf++) & 0xff]; }` (L923-933).
   (e) `while (len) { len--; crc = ... }` (L934-937).
   (f) `return crc ^ 0xffffffff;` (L940).
   `while (--blks)`: **pre-decrement**; with `blks == 1` the body does not run (I-21).
4. Reads: bytes of `[buf, buf + len)`, as bytes (L649, L925-936) and as 8-byte words `words[0..4]` per block (L712-720, L772-780); static tables. Writes: none. `endian` is an address-taken local (D-3). Pointers: `buf` byte pointer, `words` word pointer (cast, D-2), `(z_size_t)buf` as an integer (D-1: ghost alignment).
5. `crc` is `uLong` but always `< 2^32` after L635. `crc0..crc4` are `z_crc_t` (`unsigned`, 32 bits); `wordI` are `z_word_t` (64 bits): `wordI = crcI ^ words[I]` promotes `crcI` to 64 bits; `crcI = table[..]` assigns a 32-bit value; `crcI ^= table[..]` stays 32-bit. `(word0 >> (k << 3))`: counts 8..56. `crc = crc_word(crc1 ^ words[1] ^ crc)`: `crc1` is promoted, `crc` is `uLong`. `blks * N * W`: `z_size_t` times `int`, no wrap since `blks <= len/40`. `N * W + W - 1` is the `int` 47 compared with `z_size_t` `len`.
6. Structure:
   ```lean
   def crc32_z (crc : UInt64) (buf : BPtr) (len : UInt64) : M UInt64 := do
     if buf.isNull then return 0
     let crc := (~~~crc) &&& 0xffffffff
     let mut s : (UInt64 × BPtr × UInt64) := (crc, buf, len)
     if len ≥ 47 then
       s ← alignLoop s        -- L647: state (crc, buf, len), cond len ≠ 0 ∧ addr buf % 8 ≠ 0
       let (crc, buf, len) := s
       let blks := len / 40; let len := len - blks * 40
       let endian : UInt32 := 1                        -- L661
       if (endian &&& 0xff) ≠ 0 then                   -- L662 *(unsigned char*)&endian
         let st ← braidLoop (blks) (crc.toUInt32) buf  -- while (--blks): returns (words, crc0..crc4)
         let crc ← lastBlock st                        -- L772-788
         s := (crc, st.words, len)
       else
         ... big endian ...
     tailLoops s; return crc ^^^ 0xffffffff
   ```
   Make `braidLoop` a recursion on `(blks, words, c0, c1, c2, c3, c4)`; one iteration is a pure function `braidStep : (c0..c4) → (w0..w4) → (c0'..c4')`, which is where the 5x8 table lookups live; load `w0..w4` with a single `ldU64LE` each at `words + 8*I`, faulting if outside the block. Proofs want `braidStep` as one lemma. The 8-times unrolled tail loop is `Nat.repeat 8` of one byte step.
   The alignment predicate needs the ghost alignment of the block (D-1); the theorem is for every alignment.

#### `crc32` (L946-951; 6 lines)
1. `uLong ZEXPORT crc32(uLong crc, const unsigned char FAR *buf, uInt len)`.
2. Lib: `crc32_z`.
3. Straight line (the `HAVE_S390X_VX` return is dead).
4. None. 5. `len` is `uInt`, widened to `z_size_t`. 6. One call.

#### `crc32_combine_gen64` (L954-961; 8 lines)
1. `uLong ZEXPORT crc32_combine_gen64(z_off64_t len2)`.
2. Lib: `x2nmodp(len2, 3)`.
3. `if (len2 < 0) return 0;` (L955), then `return x2nmodp(len2, 3);` (the `DYNAMIC_CRC_TABLE` block is dead).
4. None (`x2n_table` through `x2nmodp`).
5. `len2` is a signed `long`; the test makes the argument of `x2nmodp` non-negative; the result is `< 2^32`.
6. Direct.

#### `crc32_combine_gen` (L964-966; 3 lines)
1. `uLong ZEXPORT crc32_combine_gen(z_off_t len2)`. 2. Lib: `crc32_combine_gen64`. 3. None. 4. None. 5. `(z_off64_t)len2`: `z_off_t` is `off_t` = `long`, the cast is the identity. 6. Direct.

#### `crc32_combine_op` (L969-973; 5 lines)
1. `uLong ZEXPORT crc32_combine_op(uLong crc1, uLong crc2, uLong op)`.
2. Lib: `multmodp`.
3. `if (op == 0) return 0;` (L970); then `return multmodp(op, crc1 & 0xffffffff) ^ (crc2 & 0xffffffff);`.
4. None.
5. All `unsigned long`. `multmodp(op, ...)` does not terminate for `op != 0` with `op & 0xffffffff == 0` (R-1); `op` is documented as the result of `crc32_combine_gen`.
6. Direct. Theorem precondition: `op < 2^32` (narrower than the prototype, to be listed in the deviations).

#### `crc32_combine64` (L976-978; 3 lines), `crc32_combine` (L981-983; 3 lines)
1. `uLong ZEXPORT crc32_combine64(uLong crc1, uLong crc2, z_off64_t len2)`; `uLong ZEXPORT crc32_combine(uLong crc1, uLong crc2, z_off_t len2)`.
2. Lib: `crc32_combine_op(crc1, crc2, crc32_combine_gen64(len2))`; `crc32_combine64(crc1, crc2, (z_off64_t)len2)`.
3. None. 4. None. 5. As above: the operator is always `< 2^32`, so `multmodp` terminates. 6. Direct.

### 7.2 `zutil.c`

#### `zlibVersion` (L27-29; 3 lines)
1. `const char * ZEXPORT zlibVersion(void)`. 2. None. 3. None. 4. Returns a pointer to the string literal `"1.3.2.1-motley"` (`zlib.h` L44): a static read-only block of 15 bytes with the NUL. 5. None. 6. Constant pointer `st_version`.

#### `zError` (L139-141; 3 lines)
1. `const char * ZEXPORT zError(int err)`. 2. None (macro `ERR_MSG`). 3. None. 4. Returns `z_errmsg[idx]`, a pointer to one of ten literals (static, read-only). 5. `idx = err < -6 || err > 2 ? 9 : 2 - err`: the comparison comes first, so `2 - err` is computed only for `-6 <= err <= 2`; there is no overflow for any `int` (including `INT_MIN`). 6. `def zError (e : Int32) : M BPtr := pure (st_errmsg (if e < -6 ∨ e > 2 then 9 else (2 - e).toNat))`.

#### `zlibCompileFlags` (L31-121; 91 lines; pp: 29)
1. `uLong ZEXPORT zlibCompileFlags(void)`. 2. None.
3. Four `switch ((int)(sizeof(T)))` with `case 2`, `case 4`, `case 8`, `default`, every case ending in `break` except `default` (last); the discriminants are constants 4, 8, 8, 8, so only one case runs each. Then a series of `#ifdef` blocks, none defined (section 0.1), and a block `#if defined(STDC) || defined(Z_HAVE_STDARG_H)` that is live and adds nothing (`NO_vsnprintf` and `HAS_vsnprintf_void` undefined).
4. None. 5. `flags += 1`, `+= 2 << 2`, `+= 2 << 4`, `+= 2 << 6`: constants; the sum is 1 + 8 + 32 + 128 = 169 (**run**).
6. Translate the four `switch`es on the constants (keep the `match`), or a single constant `169` with a comment; a difftest compares with the real C.

#### `zcalloc` (L303-307; 5 lines)
1. `voidpf ZLIB_INTERNAL zcalloc(voidpf opaque, unsigned items, unsigned size)`.
2. libc: `malloc`.
3. `(void)opaque;` then `return sizeof(uInt) > 2 ? (voidpf)malloc(items * size) : (voidpf)calloc(items, size);`; the condition is the constant true.
4. A fresh block of `items * size` bytes, **not zeroed**, or NULL (allocation oracle). The callers `ZALLOC(strm, 1, sizeof(deflate_state))` receive a struct, which the schema models as a record in a table; a typed helper per use (`zallocState`, `zallocBytes`, `zallocWords`) sharing the heap's allocation counter and oracle is recommended.
5. `items * size` is computed in 32-bit `unsigned` and wraps; no call site reaches 2^32 (section 3), so the model reports a fault at a wrap (architecture.md section 4).
6. Direct.

#### `zcfree` (L309-312; 4 lines)
1. `void ZLIB_INTERNAL zcfree(voidpf opaque, voidpf ptr)`. 2. libc: `free`. 3. `(void)opaque; free(ptr);`. 4. Frees a block (fault if `ptr` is not a block start or is already freed; `free(NULL)` is a no-op). 5. None. 6. Direct.

### 7.3 `deflate.c`

#### `slide_hash` (L187-210; 24 lines)
1. `local void slide_hash(deflate_state *s)`. The `__attribute__((no_sanitize("memory")))` is not compiled.
2. Lib: none. libc: none.
3. Two `do { ... } while (--n)` loops (L194-197, L201-207) with no `break`. Each runs `n >= 1` times (`hash_size >= 128`, `wsize >= 256`).
4. Reads and writes `head[0..hash_size-1]` and `prev[0..w_size-1]`, walking backwards through a pointer `p = &s->head[n]` (one past the end) with `*--p`. Contents arbitrary (D-10): `prev` is partly uninitialised.
5. `m` is `unsigned`; `*--p` is a `ush` promoted; `m >= wsize ? m - wsize : NIL` then `(Pos)` cast. `--n` on `unsigned` ends at 0. Writes `s->slid = 1`.
6. Loop on an index counting down (state `n`); the pointer `p` is `head + n` before the decrement. Prove by induction with the array generalised (the pilot's `slide_hash_ok`).

#### `read_buf` (L219-240; 22 lines)
1. `local unsigned read_buf(z_streamp strm, Bytef *buf, unsigned size)`.
2. Lib: `adler32` (L229), `crc32` (L233); libc: `memcpy` (as `zmemcpy`, L227).
3. Early `return 0` at L223 (`len == 0`); `if (wrap == 1) ... else if (wrap == 2)` (L228-235, the `else if` is under `GZIP`).
4. Reads `strm->avail_in`, `strm->state->wrap`, `next_in`; writes `avail_in`, `adler`, `next_in`, `total_in`; copies `len` bytes from `next_in` to `buf` (ranges must not overlap, P-4); `adler32`/`crc32` read `buf[0..len)`. Note the checksum is computed over `buf` (the copy), not over `next_in`.
5. `len = min(avail_in, size)` in `unsigned`; `strm->total_in += len` (`uLong += unsigned`). `strm->avail_in -= len` happens **before** the copy (L225).
6. Straight line. Order the statements exactly as in C.

#### `fill_window` (L252-376; 125 lines; pp: 63)
1. `local void fill_window(deflate_state *s)`. `Assert` at L257, L309, L374 are empty.
2. Lib: `slide_hash`, `read_buf`. libc: `zmemcpy` (L287), `zmemzero` (L358, L369).
3. `do { ... } while (s->lookahead < MIN_LOOKAHEAD && s->strm->avail_in != 0);` (L259-338), with a `break` at L296 (`if (s->strm->avail_in == 0) break;`) and a `break` inside a nested `while (s->insert)` at L330-331. The `if (sizeof(int) <= 2)` block (L267-280) is dead. Inside the loop: slide test (L285-295), read (L311-312), re-prime hash when `lookahead + insert >= MIN_MATCH` (L315-333). After the loop the high-water zeroing (L347-372): `if (high_water < window_size) { curr = ...; if (high_water < curr) {...} else if (high_water < curr + WIN_INIT) {...} }`.
4. Reads/writes: `window` (bytes), `head`, `prev` (through `INSERT_STRING`-like statements written out at L317-329), `ins_h`, `insert`, `lookahead`, `strstart`, `match_start`, `block_start`, `high_water`. `zmemcpy(s->window, s->window + wsize, (unsigned)wsize - more)` copies within one block; ranges adjoin but must not overlap (I-12). `read_buf(strm, window + strstart + lookahead, more)` writes into the window at the end of the current data. `zmemzero(window + curr, (unsigned)init)` and `(window + high_water, init)` write zeros. Pointer arithmetic: `window + wsize`, `window + strstart + lookahead`: all inside the `window_size`-byte block.
5. `more = (unsigned)(s->window_size - (ulg)s->lookahead - (ulg)s->strstart)`: `ulg` arithmetic then truncation to `unsigned` (intended; the value fits). `s->match_start -= wsize` (unsigned, may wrap when `match_start < wsize`: it is garbage then, by design). `s->block_start -= (long)wsize` (signed `long`). `s->strstart -= wsize`. `more += wsize` (`unsigned`). `curr = s->strstart + (ulg)(s->lookahead)`: `uInt + ulg`. `init = s->window_size - curr`, `init = (ulg)curr + WIN_INIT - s->high_water`, `s->window_size - s->high_water` all `ulg`, no wrap by the invariants (`high_water <= window_size`, `strstart + lookahead <= window_size`). `(unsigned)init` truncation: `init <= 258`.
6. Loop state: nothing carried except the heap (`s` fields); the carried locals are `n`, `more` (recomputed at the top). Use a `doWhile` combinator with a tag `{ cont, brk }` for the body; the inner `while (s->insert)` is a second loop with its own tag. The post-loop block is straight-line `if`s. Proof obligations: I-11..I-14 and the post-condition `strstart <= window_size - MIN_LOOKAHEAD`.

#### `deflateInit_` (L379-384; 6 lines)
1. `int ZEXPORT deflateInit_(z_streamp strm, int level, const char *version, int stream_size)`.
2. Lib: `deflateInit2_` with `Z_DEFLATED`, `MAX_WBITS` (15), `DEF_MEM_LEVEL` (8), `Z_DEFAULT_STRATEGY` (0). 3. None. 4. None. 5. None. 6. One call.

#### `deflateInit2_` (L387-532; 146 lines)
1. `int ZEXPORT deflateInit2_(z_streamp strm, int level, int method, int windowBits, int memLevel, int strategy, const char *version, int stream_size)`.
2. Lib: `deflateInit2_` -> `deflateReset` (L531) -> `deflateResetKeep`, `lm_init`; on failure `deflateEnd` (L511). libc: none directly (`zcalloc`/`zcfree` through the function pointers, `zmemzero`).
3. Early returns L396, L398, L425, L437, L441, L512; the `#ifdef FASTEST` block is dead; `#ifdef Z_SOLO` dead; `else if (windowBits > 15)` (L429, GZIP) live. No loop.
4. Reads `version[0]` and `my_version[0]`; writes `strm->msg`, `zalloc`, `opaque`, `zfree`, `state`; `ZALLOC(strm, 1, sizeof(deflate_state))` (a record), `zmemzero(s, sizeof(deflate_state))` (all fields zero, pointers NULL); allocates `window` (`w_size` x 2 bytes), `prev` (`w_size` x 2), `head` (`hash_size` x 2), `pending_buf` (`lit_bufsize` x 4 = `LIT_BUFS`) with `ZALLOC` through `strm->zalloc` (D-7). Then sets `sym_buf = pending_buf + lit_bufsize` (L519), `pending_buf_size = lit_bufsize * 4`. On a failed allocation (L507-513): `status = FINISH_STATE`, `msg`, `deflateEnd(strm)` frees whatever was allocated, returns `Z_MEM_ERROR`; no leak. Allocation order: state, window, prev, head, pending_buf.
5. `stream_size != sizeof(z_stream)` compares an `int` with a `size_t`; a negative `stream_size` converts to a huge value (not equal). `s->w_size = 1 << s->w_bits` (`int` shift, `w_bits <= 15`), `1 << s->hash_bits` (`hash_bits <= 16`), `lit_bufsize = 1 << (memLevel + 6)` (`<= 2^15`). `s->hash_shift = (hash_bits + MIN_MATCH-1) / MIN_MATCH`. `windowBits == 8` is changed to 9 (L439). `windowBits < -15` return (L424). `(uInt)` and `(Byte)` casts at L448, L529. `sizeof(deflate_state)` as `size_t` narrowed to `unsigned` in `ZALLOC`.
6. One `def` with early `return`s. Failure path: a helper `failInit` that sets `status`, `msg`, calls `deflateEnd`, returns -4. The version test reads `version[0]` from a NUL-terminated block (P-6); `my_version[0]` is `'1'`. 

#### `deflateStateCheck` (L537-555; 19 lines)
1. `local int deflateStateCheck(z_streamp strm)`.
2. None. 3. Early returns of 1; nested `||`/`&&` chain. 4. Reads `strm`, `zalloc`, `zfree`, `state`, `s->strm`, `s->status`. The `state` pointer may be an inflate state (P-5): the schema makes that a fault at the cast. 5. Compares `status` with seven constants (the `GZIP_STATE` test is live). 6. Direct; return `1` or `0` as `Int32`.

#### `deflateSetDictionary` (L558-622; 65 lines)
1. `int ZEXPORT deflateSetDictionary(z_streamp strm, const Bytef *dictionary, uInt dictLength)`.
2. Lib: `deflateStateCheck`, `adler32` (L576), `fill_window` (L596, L610); `CLEAR_HASH`, `UPDATE_HASH`. libc: `memset` in `CLEAR_HASH`.
3. Early returns L567, L572; `while (s->lookahead >= MIN_MATCH)` (L597-611) containing a `do { ... } while (--n)` (L600-607); no `break`.
4. Reads the caller's dictionary through `strm->next_in` after `strm->next_in = dictionary` (L595) (pointer arithmetic `dictionary += dictLength - s->w_size`, L587); `fill_window` reads from it with `read_buf` (so `total_in` grows by the dictionary length, **run**: the earlier repository reproduced it). Writes `prev`, `head`, `ins_h`, `strstart`, `block_start`, `insert`, `lookahead`, `match_length`, `prev_length`, `match_available`, and restores `next_in`, `avail_in`, `wrap`. The temporary `s->wrap = 0` (L577) must be restored on the single exit path (L620).
5. `(long)s->strstart != s->block_start` (L571); `dictLength - s->w_size` `uInt`; `n = s->lookahead - (MIN_MATCH-1)` `uInt`, `n >= 1` inside the loop; `(Pos)str` truncation; `s->strstart += s->lookahead` (L612).
6. One `def`. The inner `do ... while (--n)` is a loop on `(str, n)`; the outer `while` on the heap state. The call to `fill_window` at L596 happens with `avail_in = dictLength` (so `fill_window` may slide). State the **narrower** precondition if the proof needs `next_in` non-overlapping.

#### `deflateGetDictionary` (L625-641; 17 lines)
1. `int ZEXPORT deflateGetDictionary(z_streamp strm, Bytef *dictionary, uInt *dictLength)`.
2. Lib: `deflateStateCheck`. libc: `memcpy`.
3. Early return L631; two `if (... != Z_NULL)` guards. 4. Copies `len` bytes from `window + strstart + lookahead - len` to `dictionary`; writes `*dictLength`. 5. `len = strstart + lookahead` `uInt` (cannot wrap: `<= window_size`), clipped to `w_size`; the pointer expression is `((window + strstart) + lookahead) - len`. 6. Direct; the out-parameter is a pointer to a `UInt32` cell.

#### `deflateResetKeep` (L644-690; 47 lines)
1. `int ZEXPORT deflateResetKeep(z_streamp strm)`.
2. Lib: `deflateStateCheck`, `crc32(0L, Z_NULL, 0)` (L669), `adler32(0L, Z_NULL, 0)` (L671), `_tr_init` (L679).
3. Early return L648. Straight line. A block `{ uInt matches = s->level == 0 ? s->matches : 0; _tr_init(s); s->matches = matches; }` (L676-681): `_tr_init` clears `matches` (through `init_block`), so the value is saved and restored (it carries the number of pending hash slides of level 0, see `deflate_stored`). The `s->status = s->wrap == 2 ? GZIP_STATE : INIT_STATE` (L662-666) and `strm->adler = s->wrap == 2 ? crc32(0L, Z_NULL, 0) : adler32(0L, Z_NULL, 0)` (L667-671) are conditional expressions around `#ifdef GZIP` lines (both live).
4. Writes `total_in`, `total_out`, `msg`, `data_type`, `pending`, `pending_out`, `wrap` (sign flip), `status`, `adler`, `last_flush` (-2), `gzhead` (NULL), `block_start`, `lookahead`, `match_length`, `prev_length`, `match_available`; `_tr_init` writes the tree fields.
5. `s->wrap = -s->wrap` when negative (`wrap` in -2..2, no overflow); `(long)s->strstart`; `crc32(0L, Z_NULL, 0)` is 0, `adler32(0L, Z_NULL, 0)` is 1 (with `0003`).
6. Direct; keep the `matches` save and restore.

#### `lm_init` (L695-715; 21 lines)
1. `local void lm_init(deflate_state *s)`.
2. Macro `CLEAR_HASH`. Reads `configuration_table[s->level]` (`level` in 0..9, D-6).
3. Straight line. 4. Writes `window_size`, `head[0..hash_size-1]`, `slid`, `matches`, `max_lazy_match`, `good_match`, `nice_match`, `max_chain_length`, `strstart`, `block_start`, `lookahead`, `insert`, `match_length`, `prev_length`, `match_available`, `ins_h`. 5. `window_size = (ulg)2L*s->w_size`; the table fields are `ush` widened. 6. Direct; `CLEAR_HASH` as a helper `clearHash s`.

#### `deflateReset` (L718-725; 8 lines)
1. `int ZEXPORT deflateReset(z_streamp strm)`. 2. Lib: `deflateResetKeep`, `lm_init(strm->state)`. 3. `if (ret == Z_OK) lm_init(...)`. 4. None directly. 5. None. 6. Direct.

#### `deflateSetHeader` (L728-733; 6 lines)
1. `int ZEXPORT deflateSetHeader(z_streamp strm, gz_headerp head)`. 2. Lib: `deflateStateCheck`. 3. Early return when `deflateStateCheck(strm) || strm->state->wrap != 2`. 4. Stores the caller's `gz_header` pointer in `gzhead` (a reference to a caller-owned record; zlib never frees it). 5. None. 6. Direct. No test on `status` or on `head == NULL` (section 10, item 7).

#### `deflatePending` (L736-748; 13 lines)
1. `int ZEXPORT deflatePending(z_streamp strm, unsigned *pending, int *bits)`. 2. Lib: `deflateStateCheck`. 3. Early return L737; `if (bits != Z_NULL) *bits = ...;` `if (pending != Z_NULL) { *pending = ...; if (*pending != strm->state->pending) { *pending = (unsigned)-1; return Z_BUF_ERROR; } }`. 4. Out-parameters (two cells; `*pending` is written **twice** on overflow). 5. `(unsigned)strm->state->pending` truncates a `ulg`; the comparison `unsigned != ulg` is in `ulg`; `(unsigned)-1`. 6. Direct, with heap cells for the two out-parameters.

#### `deflateUsed` (L751-756; 6 lines)
1. `int ZEXPORT deflateUsed(z_streamp strm, int *bits)`. 2. Lib: `deflateStateCheck`. 3. Early return; `if (bits != Z_NULL)`. 4. Writes `*bits = bi_used`. 5. None. 6. Direct.

#### `deflateTune` (L838-849; 12 lines)
1. `int ZEXPORT deflateTune(z_streamp strm, int good_length, int max_lazy, int nice_length, int max_chain)`. 2. Lib: `deflateStateCheck`. 3. Early return L842. 4. Writes `good_match`, `max_lazy_match`, `nice_match`, `max_chain_length`. 5. `(uInt)good_length` etc.: a negative `int` becomes a large `uInt` (stored, no fault, no check); `nice_match = nice_length` stays `int`. 6. Direct. With `max_chain == 0` the test `--chain_length != 0` in `longest_match` wraps the `unsigned` counter to `2^32 - 1`; the walk then ends only through `cur_match <= limit` (chain entries strictly decrease, so it still terminates; **to confirm**). The theorems of `deflate` should either assume the values installed by `lm_init`/`deflateParams` or state the range accepted from `deflateTune`.

#### `deflateBound` (L948-951; 4 lines)
1. `uLong ZEXPORT deflateBound(z_streamp strm, uLong sourceLen)`. 2. Lib: `deflateBound_z`. 3. None. 4. None. 5. `(uLong)bound != bound` is false on LP64 (both 64 bits). 6. Direct.

#### `putShortMSB` (L958-961; 4 lines)
1. `local void putShortMSB(deflate_state *s, uInt b)`. 2. Macro `put_byte` x2. 3. None. 4. Writes two bytes at `pending_buf[pending]` (I-1) and advances `pending` by 2. 5. `(Byte)(b >> 8)`, `(Byte)(b & 0xff)`. 6. Direct.

#### `deflatePrime` (L759-790; 32 lines)
1. `int ZEXPORT deflatePrime(z_streamp strm, int bits, int value)`.
2. Lib: `deflateStateCheck`, `_tr_flush_bits`.
3. Early returns L764, L767, L778; `while (n--) *to++ = *from++;` (L772-773) moves `pending` bytes from `pending_out` to `pending_buf` (the ranges overlap only if `pending_out` is within the buffer: forward copy, `to < from`; do **not** use `memmove` semantics blindly: a byte-wise forward loop gives the same result as `memmove` here, but translate the loop); `do { ... } while (bits)` (L779-788) which runs at least once.
4. Writes `pending_buf`, `pending_out`, `bi_buf`, `bi_valid`. Reads `pending_buf_size`, `pending`.
5. `need = (s->bi_valid + bits) >> 3` (`int`, `bits <= 16`); `s->pending_buf_size - s->pending < (ulg)need`; `put = Buf_size - s->bi_valid` (can be 0 when `bi_valid == 16`); `(1 << put) - 1` (`put <= 16`); `(value & mask) << s->bi_valid` is below `2^16` so no signed overflow; `value >>= put` for negative `value` is implementation-defined (D-11); `s->bi_buf |= (ush)(...)`.
6. One `def`, the two loops as recursions; loop 1 on `(to, from, n)`, loop 2 on `(value, bits)`. If `put == 0` and `bits > 0` loop 2 still terminates because `_tr_flush_bits` (via `bi_flush`) empties a full buffer.

#### `deflateParams` (L793-835; 43 lines)
1. `int ZEXPORT deflateParams(z_streamp strm, int level, int strategy)`.
2. Lib: `deflateStateCheck`, `deflate` (L813), `slide_hash` (L822), `CLEAR_HASH` (L824).
3. Early returns L797, L806, L815, L817; nested `if`. `deflate` returns `Z_STREAM_ERROR` for a state error and the function returns it (L813-815).
4. Writes `max_lazy_match`, `good_match`, `nice_match`, `max_chain_length`, `level`, `strategy`, `matches`; `deflate(strm, Z_BLOCK)` may write anything through `strm`.
5. `(s->strstart - s->block_start) + s->lookahead`: `uInt` converted to `long`, `long` difference, then `+ uInt` as `long`; non-zero test. `func != configuration_table[level].func` (D-6).
6. One `def`; the `deflate` call makes this function recursive with `deflate` only in the call graph sense (`deflate` does not call `deflateParams`): define `deflateParams` after `deflate`. A proof of `deflateParams` uses the theorem of `deflate`.

#### `deflateBound_z` (L875-947; 73 lines; pp: 55)
1. `z_size_t ZEXPORT deflateBound_z(z_streamp strm, z_size_t sourceLen)`.
2. Lib: `deflateStateCheck`.
3. `switch (s->wrap < 0 ? -s->wrap : s->wrap)` (L902-933) with `case 0`, `case 1`, `case 2` (GZIP) and `default`, each ending in `break` (no fall-through; the `default` is last and needs none). Inside `case 2`: two `do { wraplen++; } while (*str++);` loops (L918-920, L923-925) that scan a caller string until its NUL. Early returns L897, L939, L946.
4. Reads `s->wrap`, `strstart`, `gzhead` and through it `extra`, `extra_len`, `name`, `comment`, `hcrc`; `w_bits`, `hash_bits`, `level`. The scan reads every byte up to and including the NUL (P-3).
5. `fixedlen = sourceLen + (sourceLen >> 3) + (sourceLen >> 8) + (sourceLen >> 9) + 4` with the unsigned-wrap guard `fixedlen < sourceLen`; same for `storelen`; `bound + 18 < bound`; `bound + wraplen < bound`; `bound < sourceLen`. All `z_size_t`, wrap on purpose. **L915 `wraplen += 2 + s->gzhead->extra_len`**: `2 + extra_len` is `unsigned` (32-bit) and wraps for `extra_len >= 0xFFFFFFFE`; patch `0001` replaces it by `2 + (z_size_t)(extra_len & 0xffff)`. Precedence at L937: `(w_bits <= hash_bits && level) ? fixedlen : storelen`.
6. One `def` with the `switch` as a `match` on `Int32`; the two string scans as loops over a pointer; the state may have negative `wrap` after `Z_FINISH`, hence the absolute value.

#### `flush_pending` (L969-987; 19 lines)
1. `local void flush_pending(z_streamp strm)`.
2. Lib: `_tr_flush_bits`. libc: `memcpy`.
3. Early `return` at L976 (`len == 0`).
4. Copies `len` bytes from `pending_out` to `next_out` (different blocks, P-4); writes `next_out`, `pending_out`, `total_out`, `avail_out`, `pending`; resets `pending_out = pending_buf` when `pending == 0`.
5. `len = s->pending > strm->avail_out ? strm->avail_out : (unsigned)s->pending` (comparison in `ulg`); `strm->total_out += len`; `avail_out -= len`; `pending -= len` (`ulg`).
6. Direct; the pilot already proved this function (`flush_pending`) on the object heap.

#### `deflate` (L1000-1309; 310 lines; pp: 244)
1. `int ZEXPORT deflate(z_streamp strm, int flush)`.
2. Lib: `deflateStateCheck`, `flush_pending`, `putShortMSB`, `adler32(0L, Z_NULL, 0)` (L1074), `crc32(0L, Z_NULL, 0)` (L1087, L1217), `crc32_z` (L1130, via `HCRC_UPDATE`), `deflate_stored`, `deflate_huff`, `deflate_rle`, `(*configuration_table[level].func)` = `deflate_fast`/`deflate_slow`, `_tr_align`, `_tr_stored_block`, `CLEAR_HASH`. libc: `memcpy` (L1142, L1155).
3. **No goto, no switch.** Stateful flow on `s->status`: sequential `if (s->status == X)` blocks, not an `else if` chain, so one call can pass through several: `INIT_STATE` (L1050-1083) -> `BUSY`; `GZIP_STATE` (L1085-1135) -> `BUSY` or `EXTRA_STATE`; `EXTRA_STATE` (L1136-1162) -> `NAME_STATE`; `NAME_STATE` (L1163-1184) -> `COMMENT_STATE`; `COMMENT_STATE` (L1185-1205) -> `HCRC_STATE`; `HCRC_STATE` (L1206-1227) -> `BUSY_STATE`; then the block compression (L1232-1280), then the trailer (L1282-1308). **Return points: 18** (L1005, L1012 via `ERR_RETURN`, L1014 via `ERR_RETURN`, L1030, L1039 via `ERR_RETURN`, L1044 via `ERR_RETURN`, L1081, L1107, L1150, L1173, L1195, L1212, L1225, L1248, L1277, L1282, L1283, L1308). Three loops contain a `return`: `while (s->pending + left > s->pending_buf_size)` (L1140-1154, returns at L1150), `do { ... } while (val != 0)` for the name (L1167-1179, return at L1173) and for the comment (L1189-1201, return at L1195). Each uses the pattern `flush_pending(strm); if (s->pending != 0) { s->last_flush = -1; return Z_OK; }`. Macros: `ERR_RETURN` (returns), `HCRC_UPDATE` (captures `s`, `strm`), `put_byte`.
   The function-pointer call at L1236-1239 is a conditional chain: `level == 0 ? deflate_stored : strategy == Z_HUFFMAN_ONLY ? deflate_huff : strategy == Z_RLE ? deflate_rle : table[level].func`.
4. Reads/writes: see section 4.1 and 4.2. Header: `put_byte` into `pending_buf` at index `pending` (I-1; `pending == 0` at L1047 because either `pending` was 0 or `flush_pending` emptied it with `avail_out != 0`). Header bytes read `s->gzhead->time`, `os`, `extra_len`, `text`, `hcrc` and the caller's `extra`, `name`, `comment` buffers (`zmemcpy(pending_buf + pending, extra + gzindex, copy)`, L1142, L1155). `strm->adler` is overwritten at several places: L1074 (after the zlib header, to the Adler-32 initial value 1), L1087, L1217 (CRC-32 initial 0).
5. `flush > Z_BLOCK || flush < 0` (L1004); `RANK(flush) <= RANK(old_flush)` with `old_flush` in -2..5 (`int`, no overflow); `header = (Z_DEFLATED + ((s->w_bits - 8) << 4)) << 8` in `uInt` (`w_bits >= 9`, so the subtraction does not wrap); `level_flags << 6`; `header += 31 - (header % 31)`; `(uInt)(strm->adler >> 16)`, `strm->adler & 0xffff`; `(Byte)(... & 0xff)` casts; `s->gzhead->extra_len & 0xff`, `(extra_len >> 8) & 0xff` as `int` expressions; `ulg left = (extra_len & 0xffff) - s->gzindex` (P-2); `s->pending + left > s->pending_buf_size` in `ulg`; `s->pending + 2 > s->pending_buf_size`; `val = s->gzhead->name[s->gzindex++]` (an `int` from a `Bytef`); `(Byte)(strm->total_in & 0xff)` etc. for the trailer; `s->wrap = -s->wrap` (L1307).
6. Structure: one `def deflate`, a straight `do` block with `return` for the straight-line early exits and **loop-with-tag** helpers for the three loops:
   ```lean
   def deflate (strm : StrmRef) (flush : Int32) : M Int32 := do
     if (← deflateStateCheck strm) ≠ 0 ∨ flush > 5 ∨ flush < 0 then return -2
     let s ← stateOf strm
     if next_out = null ∨ (avail_in ≠ 0 ∧ next_in = null) ∨ (s.status = 666 ∧ flush ≠ 4) then
       return ← errReturn strm (-2)                       -- ERR_RETURN
     if avail_out = 0 then return ← errReturn strm (-5)
     let old_flush := s.last_flush; setLastFlush flush
     if s.pending ≠ 0 then
       flushPending strm
       if avail_out = 0 then setLastFlush (-1); return 0
     else if avail_in = 0 ∧ rank flush ≤ rank old_flush ∧ flush ≠ 4 then return ← errReturn strm (-5)
     if status = 666 ∧ avail_in ≠ 0 then return ← errReturn strm (-5)
     -- header phases: each phase is `if status = X then ...`, in this order
     ...
     -- phase EXTRA (loop with a return): 
     --   match ← extraLoop strm s beg left with | .ret r => return r | .done => pure ()
   ```
   The loop helpers (`extraLoop`, `nameLoop`, `commentLoop`) return `Ctl Int32`; their body is exactly `HCRC_UPDATE; gzindex += copy; flush_pending; if pending ≠ 0 then ret 0`. A first step before translating: write the tag type and the `errReturn`/`flushOrReturn` helpers once. Differential tests must cover small `avail_out` (1 byte) to reach every `last_flush = -1` return; the existing difftest approach drives `deflate` with output sizes 1, 2, 3, ... for this reason.

#### `deflateEnd` (L1312-1329; 18 lines)
1. `int ZEXPORT deflateEnd(z_streamp strm)`.
2. Lib: `deflateStateCheck`; `ZFREE` through `strm->zfree` (the default `zcfree`).
3. Early return L1315; four `TRY_FREE` blocks in the order `pending_buf`, `head`, `prev`, `window` (comment: "reverse order of allocations"), then `ZFREE(strm, strm->state)`, `strm->state = Z_NULL`.
4. Frees the four buffers (each only if non-NULL) and the state record. `status` is read **before** the free (L1317).
5. `status == BUSY_STATE ? Z_DATA_ERROR : Z_OK`. 6. Direct. This function is the leak-freedom anchor: after it the heap holds none of the five blocks.

#### `deflateCopy` (L1336-1406; 71 lines)
1. `int ZEXPORT deflateCopy(z_streamp dest, z_streamp source)`.
2. Lib: `deflateStateCheck`; `ZALLOC`/`ZFREE` through `source->zalloc/zfree`. libc: `memcpy` x6.
3. Early returns L1347, L1350, L1358, L1373; one failure branch with four `TRY_FREE` and `ZFREE(source, ds)`. Straight line after that. `#ifdef MAXSEG_64K` dead.
4. `zmemcpy(ds, ss, sizeof(deflate_state))` (a value copy of the record, D: whole-struct copy); allocate `window`, `prev`, `head`, `pending_buf` for `ds`; `zmemcpy(dest, source, sizeof(z_stream))` (value copy of the stream; `dest != source`, P-4), `dest->state = ds`, `ds->strm = dest`; `zmemcpy(ds->window, ss->window, ss->high_water)`; `zmemcpy(ds->prev, ss->prev, (...) * sizeof(Pos))` (I-11); `zmemcpy(ds->head, ss->head, ds->hash_size * sizeof(Pos))`; `ds->pending_out = ds->pending_buf + (ss->pending_out - ss->pending_buf)` (D-9); `zmemcpy(ds->pending_out, ss->pending_out, ss->pending)`; `ds->sym_buf = ds->pending_buf + ds->lit_bufsize; zmemcpy(ds->sym_buf, ss->sym_buf, ss->sym_next)`; `ds->l_desc.dyn_tree = ds->dyn_ltree` (and `d_desc`, `bl_desc`). The `memcpy` of `prev` and `window` copies uninitialised bytes (D-10).
5. `ss->strstart - ss->insert > ds->w_size ? ds->w_size : ss->strstart - ss->insert` is `uInt`; times `sizeof(Pos)` (`size_t`); `ds->hash_size * sizeof(Pos)`; `ss->pending` (`ulg`) as a size.
6. One `def`. The `strm` back-pointers: after `zmemcpy(dest, source)` the copied `dest->state` is overwritten at L1378. Note that the C copies `dest` from `source` **after** allocating `ds` with `source`'s allocator; if the model copies the record `source` into `dest`, keep that order.

#### `longest_match` (L1418-1559; 142 lines; pp: 50)
1. `local uInt longest_match(deflate_state *s, IPos cur_match)`.
2. Lib: none. libc: none. (The `UNALIGNED_OK` branches and `Assert`s are dead.)
3. `do { ... } while ((cur_match = prev[cur_match & wmask]) > limit && --chain_length != 0);` (L1463-1555) with a **`continue`** at L1514 (`if (match[best_len] != scan_end || ... ) continue;`) and a `break` at L1546 (`if (len >= nice_match) break;`). `continue` in a `do ... while` jumps to the condition (L1554), which performs the chain step. Inside: an inner `do { } while (*++scan == *++match && ... && scan < strend)` (L1528-1533) with an **empty body** and eight pre-increment comparisons. Final `return` L1557-1558.
4. Reads `window[...]` at `strstart`, `strstart + best_len - 1 .. best_len`, `cur_match + best_len`, up to index `strstart + 258` (I-9), `prev[cur_match & wmask]`; writes `match_start`. Pointers `scan`, `match`, `strend` (`strend = window + strstart + MAX_MATCH`, L1441) into the window; comparison `scan < strend` is inside one block. The pointer `scan` is reset to `strend - MAX_MATCH` (L1539) so it stays equal to `window + strstart`; `scan_end1 = scan[best_len - 1]; scan_end = scan[best_len]` are `Byte` locals (L1442-1443, L1550-1551) updated when `len > best_len`.
5. `chain_length >>= 2` (`unsigned`); `(uInt)nice_match > s->lookahead` then `nice_match = (int)lookahead` (L1458); `limit = s->strstart > (IPos)MAX_DIST(s) ? s->strstart - (IPos)MAX_DIST(s) : NIL`; `len = MAX_MATCH - (int)(strend - scan)` (pointer difference cast to `int`); `best_len` `int`; `(uInt)best_len <= s->lookahead` (L1557). `cur_match` is `IPos` (`unsigned`) assigned from a `ush`.
6. Loop state `(cur_match, chain_length, best_len, scan_end1, scan_end)` plus `match_start` in the heap. Body returns `Tag := skip | brk | cont`:
   ```lean
   -- body: returns (st', tag) ; `continue` = skip, `break` = brk
   -- cond: (cur_match := prev[cur_match &&& wmask]) > limit && (chain_length := chain_length - 1) ≠ 0
   ```
   Write the inner comparison loop as a function `scanEq (scan match : Nat) : M Nat` that advances by 8 and stops on the first mismatch or `scan ≥ strend`, with the pre-increment semantics (compare after incrementing both pointers). Do not simplify to a `memcmp`: the 8-step granularity decides how far beyond a mismatch the loop reads (never beyond `strend`).
   ```lean
   structure LM where (cur : UInt32) (chain : UInt32) (best : Int32) (scanEnd1 scanEnd : UInt8)
   inductive Step | skip | brk | go          -- `continue`, `break`, fall through to the condition
   def longest_match (s : DRef) (cur0 : UInt32) : M UInt32 := do
     -- L1419-1458: chain := max_chain_length (>>> 2 if prev_length ≥ good_match), best := prev_length,
     --             limit, nice := min(nice_match, lookahead), scanEnd1/scanEnd := scan[best-1], scan[best]
     let st ← doWhile ⟨cur0, chain, best, e1, e0⟩ fun st => do
       let m := window + st.cur
       if ← mismatch4 s st m then return (st, .skip)      -- L1511-1514 `continue`
       let len ← scanEq s (scan := 2) (match := 2)         -- L1522-1538, eight compares per round
       if len > st.best then
         setMatchStart st.cur
         if len ≥ nice then return ({st with best := len}, .brk)   -- L1546
         return ({st with best := len, scanEnd1 := .., scanEnd := ..}, .go)
       return (st, .go)
     cond: fun st => do                                    -- L1554: the update happens here, once
       let c ← ldW (prev + (st.cur &&& wmask))
       let chain := st.chain - 1
       return (c > limit && chain ≠ 0, {st with cur := c, chain := chain})
     -- L1557: return min best lookahead
   ```
   `.skip` and `.go` both run `cond`; only `.brk` leaves without it. The `cond` must not run after a `break`.

#### `deflate_stored` (L1700-1883; 184 lines; pp: 115)
1. `local block_state deflate_stored(deflate_state *s, int flush)`.
2. Lib: `_tr_stored_block` (L1748, L1874), `flush_pending` (L1757, L1876), `read_buf` (L1781, L1851). libc: `memcpy` (L1769, L1801, L1809, L1815, L1841).
3. `do { ... } while (last == 0);` (L1714-1786) with **two `break`s** (L1722, L1742) and no `continue`; after the loop three straight-line phases with early `return`s at L1827 (`last`), L1833 (`block_done`) and L1882. Macro `MIN`.
4. Window and output: Phase A copies directly into `next_out`: `_tr_stored_block(s, (char *)0, 0L, last)` writes a dummy stored-block header into `pending_buf` (it contains `buf == NULL`, `stored_len == 0`, so no `memcpy`), L1751-1754 overwrite the length bytes at `pending - 4 .. pending - 1` (`pending >= 4` after the header), `flush_pending` emits the header, `zmemcpy(strm->next_out, window + block_start, left)` copies window bytes (needs `block_start >= 0`, I-10), `read_buf(strm, next_out, len)` copies input bytes straight to the output (the destination is the caller's `next_out`; the checksum is computed on it). Phase B updates the window: `zmemcpy(s->window, s->strm->next_in - s->w_size, s->w_size)` (I-14), or slides (`zmemcpy(window, window + w_size, strstart)`, I-13) and appends `used` bytes taken from `next_in - used`. Phase C reads more input into the window with `read_buf`. Phase D emits a stored block into `pending_buf` via `_tr_stored_block(s, (charf *)s->window + s->block_start, len, last)`.
5. This is the place where `unsigned`, `long` and `ulg` mix:
   * L1705 `min_block = (unsigned)(MIN(s->pending_buf_size - 5, s->w_size))`: `MIN(ulg, uInt)` evaluates in `ulg`; `pending_buf_size >= 512`.
   * L1720 `have = ((unsigned)s->bi_valid + 42) >> 3` (the cast first: no negative). L1724 `have = avail_out - have` after the test at L1721.
   * L1725 `left = (unsigned)(s->strstart - s->block_start)`: `uInt` converted to `long`, subtracted, truncated.
   * L1726 `left < len && avail_in < len - left`, L1727 `len = left + avail_in` (no wrap: `< 65535`). L1732 `all = len >= left && len - left == avail_in`.
   * L1739-1741 condition on `min_block`, `flush`, `all`. L1747 `last = flush == Z_FINISH && all ? 1 : 0`.
   * L1751-1754 `(Bytef)len`, `(Bytef)(len >> 8)`, `(Bytef)~len`, `(Bytef)(~len >> 8)`: `~len` is `unsigned`, truncated.
   * L1773 `s->block_start += left` (`long += unsigned`). L1774 `len -= left`.
   * L1794 `used -= avail_in` (`unsigned`). L1806 `s->window_size - s->strstart <= used` (`ulg - uInt` compared with `unsigned`, converted to `ulg`). L1808 `strstart -= w_size`. L1817 `s->insert += MIN(used, s->w_size - s->insert)`.
   * L1832 `(long)s->strstart == s->block_start`. L1836 `have = (unsigned)(window_size - strstart)`. L1837 `avail_in > have && block_start >= (long)w_size`. L1839 `block_start -= w_size` (`long -= uInt`). L1844 `have += w_size`.
   * L1865 `(unsigned)MIN(s->pending_buf_size - have, MAX_STORED)`: `ulg` against `int 65535` converted to `ulg`. L1866 `min_block = MIN(have, s->w_size)`.
   * L1868-1870 `left >= min_block || ((left || flush == Z_FINISH) && flush != Z_NO_FLUSH && avail_in == 0 && left <= have)`.
   * L1874 `(charf *)s->window + s->block_start`: the cast binds before the `+`; a `char *` plus a `long`.
6. Translate as four phases in one `def`. Phase A as `doWhile` with state `(last, all, len, left, have)` and tags `brk`/`cont`; after it `used` is derived from `avail_in`. Carry **every unsigned local as `UInt32`** and convert explicitly where the C converts (`toInt64` for `strstart - block_start`, `toUInt32` for the cast back). The three early `return`s of phases B-D use the monad's `return`. Skeleton of phase A:
   ```lean
   structure SL where (last : Bool) (all : Bool) (len left have_ : UInt32)
   -- do { ... } while (last == 0): `break` at L1722 and L1742 are `.brk`; falling off the end is `.go`
   let st ← doWhile (init := ⟨false, false, 0, 0, 0⟩) fun st => do
     let have0 := ((← s.bi_valid).toUInt32 + 42) >>> 3                      -- L1720
     if (← strm.avail_out) < have0 then return (st, .brk)                   -- L1721-1722
     let have_ := (← strm.avail_out) - have0                                -- L1724
     let left := ((← s.strstart).toUInt64.toInt64 - (← s.block_start)).toUInt32  -- L1725, long arithmetic
     let len := if left < 65535 ∧ (← strm.avail_in) < 65535 - left then left + (← strm.avail_in) else 65535
     let len := if len > have_ then have_ else len                          -- L1728
     let all := len ≥ left ∧ len - left == (← strm.avail_in)                -- L1732
     if len < min_block ∧ ((len == 0 ∧ flush ≠ 4) ∨ flush == 0 ∨ ¬all) then return (st, .brk)
     let last := flush == 4 ∧ all                                           -- L1747
     trStoredBlock s null 0 last; patchLen s len; flushPending strm         -- L1748-1757
     ... copy `left` window bytes, then `len` input bytes (L1766-1785) ...
     return ({st with last, all, len, left, have_}, if last then .brk else .go)   -- while (last == 0)
   ```
   Because the `ulg`/`unsigned`/`long` mixture is exactly where a wrong `UInt`/`Int` choice would still typecheck, add a difftest with `memLevel` 1 (`pending_buf_size = 512`, `min_block = 507`), small `avail_out`, input larger than `w_size`, and `deflateParams` switching the level to 0 (the `matches` counter) and back.

#### `deflate_fast` (L1892-1983; 92 lines; pp: 54)
1. `local block_state deflate_fast(deflate_state *s, int flush)`. Used for levels 1 to 3.
2. Lib: `fill_window` (L1903), `longest_match` (L1926), `flush_pending` and `_tr_flush_block` (inside `FLUSH_BLOCK`). Macros: `INSERT_STRING` (L1915, L1946), `UPDATE_HASH` (L1958), `_tr_tally_dist` (L1932), `_tr_tally_lit` (L1969), `FLUSH_BLOCK` (L1973, L1977, L1981). `check_match` and `Tracevv` are empty.
3. `for (;;)` (L1896-1974) with one `break` (L1907) and one early `return need_more` (L1905). `if (bflush) FLUSH_BLOCK(s, 0);` (L1973) can return `need_more` or `finish_started`. The match branch (L1929-1965) is `if (match_length >= MIN_MATCH) { tally; lookahead -= match_length; if (match_length <= max_insert_length && lookahead >= MIN_MATCH) { match_length--; do { strstart++; INSERT_STRING } while (--match_length != 0); strstart++; } else { strstart += match_length; match_length = 0; ins_h = window[strstart]; UPDATE_HASH } } else { tally_lit; lookahead--; strstart++ }`; the `else` at L1952 sits between `#ifndef FASTEST` and `#endif`; both are live in the default build. After the loop (L1975-1982): `insert = ...; if (flush == Z_FINISH) { FLUSH_BLOCK(s, 1); return finish_done; } if (s->sym_next) FLUSH_BLOCK(s, 0); return block_done;`.
4. Window reads at `strstart`, `strstart + 1`, `strstart + 2` (via `INSERT_STRING`); writes `head[ins_h]`, `prev[strstart & w_mask]`; `sym_buf` through the tally macros (I-3); `dyn_ltree`, `dyn_dtree` frequencies. `longest_match` writes `match_start`.
5. `hash_head` is `IPos` (`unsigned`), assigned from the `ush` head slot; `s->strstart - hash_head <= MAX_DIST(s)` is `unsigned`; the tally arguments `s->strstart - s->match_start` (cast to `ush`, intended: `<= MAX_DIST < 2^16`) and `s->match_length - MIN_MATCH` (cast to `uch`, `<= 255` by the bound of `longest_match`); `lookahead -= match_length` (no wrap, `longest_match` returns `<= lookahead`); `--s->match_length != 0` pre-decrement in the `while`; `s->insert = s->strstart < MIN_MATCH-1 ? s->strstart : MIN_MATCH-1`. The stale `match_length` persists across iterations (L1919 comment: it is `< MIN_MATCH` at the top of the loop).
6. One `def` with a `for (;;)` loop whose carried state is the heap plus the locals `hash_head` and `bflush`. Tag `Ctl BlockState := next | brk | ret bs`. Write `flushBlock s last : M (Option BlockState)` once (section 5) and use `if let some r ← flushBlock s 0 then return .ret r`. Do not factor `INSERT_STRING` into `fill_window`'s inlined copy of the same statements (L317-329).

#### `deflate_slow` (L1991-2112; 122 lines; pp: 72)
1. `local block_state deflate_slow(deflate_state *s, int flush)`. Levels 4 to 9 (lazy matching).
2. Lib: `fill_window` (L2003), `longest_match` (L2029), `flush_pending`, `_tr_flush_block`. Macros: `INSERT_STRING` (L2015, L2067), `_tr_tally_dist` (L2055), `_tr_tally_lit` (L2082, L2101), `FLUSH_BLOCK` (L2074, L2106, L2110), `FLUSH_BLOCK_ONLY` (L2084), `MAX_DIST`.
3. `for (;;)` (L1996-2097), `break` at L2007, `return need_more` at L2005 and L2088. A three-way `if (prev_length >= MIN_MATCH && match_length <= prev_length) {...} else if (match_available) {...} else {...}` (L2048-2096). In the first branch: `FLUSH_BLOCK(s, 0)` inside `if (bflush)` (L2074; may return). In the second: `if (bflush) { FLUSH_BLOCK_ONLY(s, 0); }` (no return) **then** `strstart++; lookahead--;` **then** `if (s->strm->avail_out == 0) return need_more;` (L2084-2088). A `do { if (++s->strstart <= max_insert) { INSERT_STRING(...); } } while (--s->prev_length != 0);` loop (L2065-2069). After the loop: `if (s->match_available) { tally_lit; match_available = 0; }`, then the same ending as `deflate_fast` (L2104-2111).
4. Reads/writes as `deflate_fast`, plus `prev_length`, `prev_match`, `match_available`, `strategy`. The TOO_FAR test (L2032-2037) reads `match_start`, which may be stale (`match_start` is zeroed by the `zmemzero` of `deflateInit2_`, so it is an ordinary value, never uninitialised).
5. `s->prev_length = s->match_length, s->prev_match = s->match_start;` is a comma expression (L2020). `s->strstart - hash_head <= MAX_DIST(s)`; `s->match_length <= 5 && (s->strategy == Z_FILTERED || (s->match_length == MIN_MATCH && s->strstart - s->match_start > TOO_FAR))` (`TOO_FAR` = 4096, `unsigned` compare). `max_insert = strstart + lookahead - MIN_MATCH` (`uInt`, I-15). `lookahead -= prev_length - 1` (L2063), `prev_length -= 2` (L2064): `prev_length >= 3` is known, so `>= 1` afterwards and the `do/while (--prev_length != 0)` runs `prev_length - 2` times. `++s->strstart <= max_insert`: pre-increment in the condition.
6. One `def`; the carried locals are `hash_head` and `bflush` only; the lazy state lives in the heap (`prev_length`, `prev_match`, `match_available`, `match_length`). Translate the three-way branch exactly; the extra `return need_more` of the second branch is easy to lose.

#### `deflate_rle` (L2120-2185; 66 lines; pp: 53)
1. `local block_state deflate_rle(deflate_state *s, int flush)`. Used when `strategy == Z_RLE`.
2. Lib: `fill_window` (L2131), `flush_pending`, `_tr_flush_block`. Macros: `_tr_tally_dist` (L2163), `_tr_tally_lit` (L2171), `FLUSH_BLOCK` (L2175, L2179, L2183). `check_match` is empty.
3. `for (;;)` (L2125-2176) with one `break` (L2135) and `return need_more` (L2133). Note the test is `s->lookahead <= MAX_MATCH` (L2130, `<=` not `<`). The run scan: `scan = window + strstart - 1; prev = *scan; if (prev == *++scan && prev == *++scan && prev == *++scan) { strend = window + strstart + MAX_MATCH; do { } while (prev == *++scan && ... eight times ... && scan < strend); match_length = MAX_MATCH - (uInt)(strend - scan); if (match_length > lookahead) match_length = lookahead; }` (L2140-2154).
4. Reads `window[strstart - 1 .. strstart + 258]` (requires `strstart > 0`, tested at L2140; I-9). Does not touch `head`/`prev`. Pointers `scan`, `strend` are in the window block; `scan < strend` is a same-object comparison.
5. `prev` is a `uInt` holding a byte; `*++scan` is a `Byte` promoted to `int` and compared with `prev` converted to `int`; `MAX_MATCH - (uInt)(strend - scan)` (pointer difference cast to `uInt`); `s->lookahead -= s->match_length`. `_tr_tally_dist(s, 1, s->match_length - MIN_MATCH, bflush)`.
6. Same loop shape as `deflate_fast`; the scan as a helper `runLength : M UInt32` returning the final `scan` offset.

#### `deflate_huff` (L2191-2221; 31 lines)
1. `local block_state deflate_huff(deflate_state *s, int flush)`. Used when `strategy == Z_HUFFMAN_ONLY`.
2. Lib: `fill_window` (L2197), `flush_pending`, `_tr_flush_block`. Macros: `_tr_tally_lit` (L2208), `FLUSH_BLOCK` (L2211, L2215, L2219).
3. `for (;;)` (L2194-2212): `if (s->lookahead == 0) { fill_window(s); if (s->lookahead == 0) { if (flush == Z_NO_FLUSH) return need_more; break; } }` then one literal per iteration; `if (bflush) FLUSH_BLOCK(s, 0);`. After the loop `s->insert = 0;` and the same ending.
4. Reads `window[strstart]`; writes `sym_buf`, `dyn_ltree`, `match_length = 0`.
5. Plain `uInt` decrements and increments.
6. Same shape as `deflate_fast` without the match code.

### 7.4 `trees.c`

#### `bi_reverse` (L154-161; 8 lines)
1. `local unsigned bi_reverse(unsigned code, int len)`.
2. None. 3. `do { res |= code & 1; code >>= 1, res <<= 1; } while (--len > 0);` then `return res >> 1;`. The body runs at least once (`len >= 1`); `code >>= 1, res <<= 1` is a comma expression of two statements. 4. None. 5. `unsigned` shifts by 1; `--len > 0` on `int`. 6. Recursion on `(code, res, len)`; pure.

#### `bi_flush` (L166-176; 11 lines)
1. `local void bi_flush(deflate_state *s)`. 2. Macros `put_short`, `put_byte`. 3. `if (s->bi_valid == 16) {...} else if (s->bi_valid >= 8) {...}` (two branches, a third path does nothing). 4. Writes 2 bytes (`bi_valid == 16`) or 1 byte (`>= 8`) to `pending_buf[pending..]` without a capacity test (I-1), clears or shifts `bi_buf`, adjusts `bi_valid`. 5. `put_byte(s, (Byte)s->bi_buf)`; `s->bi_buf >>= 8` on a `ush`; `s->bi_valid -= 8`. 6. Direct.

#### `bi_windup` (L181-193; 13 lines)
1. `local void bi_windup(deflate_state *s)`. 2. Macros `put_short`, `put_byte`. 3. `if (bi_valid > 8) put_short else if (bi_valid > 0) put_byte` then three assignments. 4. Writes 0, 1 or 2 bytes to `pending_buf`, then `bi_used`, `bi_buf = 0`, `bi_valid = 0`. 5. `s->bi_used = ((s->bi_valid - 1) & 7) + 1`: for `bi_valid == 0` the expression is `((-1) & 7) + 1 = 8`, defined. 6. Direct.

#### `gen_codes` (L203-232; 30 lines)
1. `local void gen_codes(ct_data *tree, int max_code, ushf *bl_count)`.
2. Lib: `bi_reverse`.
3. Two loops: `for (bits = 1; bits <= MAX_BITS; bits++)` and `for (n = 0; n <= max_code; n++)` with `if (len == 0) continue;` (L225).
4. Local array `next_code[MAX_BITS+1]` of `ush` (a stack array; index `bits` 1..15; `next_code[0]` is never read). Reads `bl_count[bits - 1]` (`bits = 1` reads `bl_count[0]`), `tree[n].Len`; writes `tree[n].Code`. `tree` points to `dyn_ltree`, `dyn_dtree` or `bl_tree` of the state (offset 0); `bl_count` points to `s->bl_count`.
5. `code = (code + bl_count[bits - 1]) << 1` (`unsigned`); `next_code[bits] = (ush)code` truncates; `bi_reverse(next_code[len]++, len)`: the post-increment is an argument (the value passed is the old one; the stored value wraps at 65536 which is unreachable); `(ush)bi_reverse(...)` truncation.
6. Two loops: the first accumulates `(code, next_code array)`, the second walks the tree. Use a local `Array UInt16` (size 16) threaded through the second loop.

#### `tr_static_init` (L295-374; empty in the default build)
1. `local void tr_static_init(void)`. 2. None. 3. The whole body is inside `#if defined(GEN_TREES_H) || !defined(STDC)`, which is false: the function is `{ }` (**pp:** `static void tr_static_init(void) { }`). 4. None. 5. None. 6. `pure ()`. The values the dead code would compute are the tables of section 3 (they can be recomputed in Lean as a check, not as part of the translation).

#### `init_block` (L440-451; 12 lines)
1. `local void init_block(deflate_state *s)`. 2. None. 3. Three `for` loops (L444-446) over `n < L_CODES` (286), `D_CODES` (30), `BL_CODES` (19). 4. Writes the `fc` field (`Freq`) of `dyn_ltree[0..285]`, `dyn_dtree[0..29]`, `bl_tree[0..18]` to 0, then `dyn_ltree[END_BLOCK].fc = 1`, `opt_len = static_len = 0`, `sym_next = matches = 0`. The `dl` field (`Len`/`Dad`) keeps its old value. 5. Chained assignments `s->opt_len = s->static_len = 0L;`, `s->sym_next = s->matches = 0;` (types `ulg`, `uInt`). 6. Direct; three loops as recursions or `Fin` maps.

#### `_tr_init` (L456-478; 23 lines)
1. `void ZLIB_INTERNAL _tr_init(deflate_state *s)`. 2. Lib: `tr_static_init`, `init_block`. 3. Straight line. 4. Sets `l_desc.dyn_tree = s->dyn_ltree` (a pointer to the array inside the same state), `l_desc.stat_desc = &static_l_desc` (pointer to a static descriptor), the same for `d_desc` and `bl_desc`, and `bi_buf = 0`, `bi_valid = 0`, `bi_used = 0`. 5. None. 6. Direct, with the pointer constructors of the schema.

#### `pqdownheap` (L509-528; 20 lines)
1. `local void pqdownheap(deflate_state *s, ct_data *tree, int k)`.
2. Macro `smaller`.
3. `while (j <= s->heap_len)` with one `break` (L519). The inner `if (j < s->heap_len && smaller(tree, s->heap[j + 1], s->heap[j], s->depth)) j++;`.
4. Reads `heap[k]`, `heap[j]`, `heap[j+1]`, `tree[..].Freq`, `depth[..]`; writes `heap[k]` repeatedly and `heap[k] = v` at the end. Indices: `j <= heap_len <= 572`, `j + 1 <= heap_len`.
5. `int` arithmetic: `j = k << 1`, `j <<= 1`; all indices below 573. `smaller` compares `ush` values promoted to `int` and `uch` values.
6. Loop state `(k, j)`, `v` fixed; the `break` is the exit tag. Prove the standard heap invariants separately (trees.md section 2).

#### `gen_bitlen` (L540-613; 74 lines; pp: 52)
1. `local void gen_bitlen(deflate_state *s, tree_desc *desc)`.
2. Lib: none.
3. `for (bits = 0; bits <= MAX_BITS; bits++) bl_count[bits] = 0;` (L554); `for (h = s->heap_max + 1; h < HEAP_SIZE; h++)` with `continue` (L568); `if (overflow == 0) return;` (L577); `do { bits = max_length - 1; while (s->bl_count[bits] == 0) bits--; ... overflow -= 2; } while (overflow > 0);` (L583-593); `for (bits = max_length; bits != 0; bits--) { n = s->bl_count[bits]; while (n != 0) { m = s->heap[--h]; if (m > max_code) continue; if (...) {...} n--; } }` (L600-612): the `continue` is inside the `while (n != 0)` and does **not** decrement `n`.
4. Reads `desc->dyn_tree`, `max_code`, `stat_desc->{static_tree, extra_bits, extra_base, max_length}`; `heap`, `heap_max`, `tree[..].Dad/Freq/Len`, `static_tree[n].Len`, `extra[n - base]`; writes `bl_count`, `tree[..].Len`, `opt_len`, `static_len`. `stree` is `NULL` for the bit length tree (L575 tests the pointer).
5. `bits = tree[tree[n].Dad].Len + 1` (`int`); `tree[n].Len = (ush)bits`; `s->opt_len += (ulg)f * (unsigned)(bits + xbits)`; `s->static_len += (ulg)f * (unsigned)(stree[n].Len + xbits)`; **L607 `s->opt_len += ((ulg)bits - tree[m].Len) * tree[m].Freq`** wraps modulo `2^64` on purpose when the length shrinks (the product of the wrapped difference and `Freq` added to `opt_len` gives the signed change). `n >= base` selects `xbits = extra[n - base]`.
6. Four loops, each a recursion on explicit state: `(h)` for the first, `(bits)` for the search, `(overflow)` for the repair, `(bits, n, h)` for the last. The `while (s->bl_count[bits] == 0) bits--;` is the I-4 obligation: translate with fuel and make the index an `Int` (so that `-1` is a detectable fault, not a `UInt` wrap). Keep the "`continue` without `n--`" shape.

#### `build_tree` (L627-706; 80 lines; pp: 41)
1. `local void build_tree(deflate_state *s, tree_desc *desc)`.
2. Lib: `pqdownheap` (also via macro `pqremove`), `gen_bitlen`, `gen_codes`.
3. `for (n = 0; n < elems; n++)` (L641-648); `while (s->heap_len < 2)` (L655-661); `for (n = s->heap_len/2; n >= 1; n--)` (L667); `do { pqremove(...); ... } while (s->heap_len >= 2);` (L673-695); a final statement (L697). No `break`.
4. Reads `desc->dyn_tree`, `stat_desc->static_tree`, `elems`; writes `heap[]`, `heap_len`, `heap_max`, `depth[]`, `tree[n].Freq` (L657, L681), `tree[n].Dad`/`Len`, `desc->max_code`, `opt_len`, `static_len`. Internal nodes live at indices `elems .. 2*elems - 1` of the same arrays (`dyn_ltree` has 573 entries, `dyn_dtree` 61, `bl_tree` 39): the node index is bounded by `2*elems - 1`.
5. `s->heap[++(s->heap_len)] = max_code = n;` (chain, pre-increment); `node = s->heap[++(s->heap_len)] = (max_code < 2 ? ++max_code : 0);` (L656); `s->opt_len--` (wraps below 0 on purpose, `ulg`) and `s->static_len -= stree[node].Len` (L659); `tree[node].Freq = tree[n].Freq + tree[m].Freq` (`ush + ush` computed in `int`, stored to `ush`, truncating); `s->depth[node] = (uch)((s->depth[n] >= s->depth[m] ? s->depth[n] : s->depth[m]) + 1)`; `tree[n].Dad = tree[m].Dad = (ush)node;`; `s->heap[SMALLEST] = node++;`; `s->heap[--(s->heap_max)] = n;` (two decrements).
6. One `def`; the four loops as recursions, the macro `pqremove` as a local `def pqremove` that returns `top`. Preserve the exact sequence `top = heap[1]; heap[1] = heap[heap_len]; heap_len -= 1; pqdownheap`. The theorem needs `heap_len <= 572` and `heap_max >= heap_len + 1` style invariants (trees.md section 2).

#### `scan_tree` (L712-747; 36 lines)
1. `local void scan_tree(deflate_state *s, ct_data *tree, int max_code)`. 2. None.
3. `for (n = 0; n <= max_code; n++)` with `if (++count < max_count && curlen == nextlen) { continue; } else if (count < min_count) {...} else if (curlen != 0) {...} else if (count <= 10) {...} else {...}` then the resets `count = 0; prevlen = curlen;` and a three-way update of `max_count`, `min_count`. The `continue` skips the resets.
4. Reads `tree[0].Len` and `tree[n+1].Len`; writes the guard `tree[max_code + 1].Len = (ush)0xffff` (I-7) and `s->bl_tree[x].Freq` for `x` in `curlen`, 16, 17, 18.
5. `int` locals; `tree[n+1].Len` is a `ush` promoted to `int`; `s->bl_tree[curlen].Freq += (ush)count;` narrows to `ush`; `Freq++`. 6. Loop state `(n, prevlen, nextlen, count, max_count, min_count)` with a `Ctl` tag for `continue`.

#### `send_tree` (L753-794; 42 lines)
1. `local void send_tree(deflate_state *s, ct_data *tree, int max_code)`. 2. Macros `send_code`, `send_bits`.
3. Same loop skeleton as `scan_tree`. In the `count < min_count` branch: `do { send_code(s, curlen, s->bl_tree); } while (--count != 0);` (L770; the body is a macro block statement). In the `curlen != 0` branch: `if (curlen != prevlen) { send_code(...); count--; }` then `send_code(s, REP_3_6, s->bl_tree); send_bits(s, count - 3, 2);`. The guard line is a comment (L762).
4. Reads `tree[n+1].Len` (including the guard written by `scan_tree`), writes through `send_bits` (`bi_buf`, `bi_valid`, `pending_buf`, `pending`).
5. `send_bits(s, count - 3, 2)`, `count - 3` and `count - 11` in `int`. 6. As `scan_tree`, plus the inner `do ... while` as a loop on `count`. The call-order dependency (the guard) must be recorded as a precondition of `send_tree`.

#### `build_bl_tree` (L800-826; 27 lines)
1. `local int build_bl_tree(deflate_state *s)`. 2. Lib: `scan_tree` x2, `build_tree` (on `&s->bl_desc`). 3. `for (max_blindex = BL_CODES-1; max_blindex >= 3; max_blindex--) { if (s->bl_tree[bl_order[max_blindex]].Len != 0) break; }` (L817-819), then `return max_blindex`. 4. Reads `l_desc.max_code`, `d_desc.max_code`, `bl_tree[..].Len`, `bl_order`; writes `opt_len`. 5. `s->opt_len += 3*((ulg)max_blindex + 1) + 5 + 5 + 4`. 6. Direct; the `break` is the exit tag of the loop (a counting-down loop).

#### `send_all_trees` (L833-855; 23 lines)
1. `local void send_all_trees(deflate_state *s, int lcodes, int dcodes, int blcodes)`. 2. Lib: `send_tree` x2; macro `send_bits`. 3. `for (rank = 0; rank < blcodes; rank++)`. 4. Reads `bl_tree[bl_order[rank]].Len`; writes via `send_bits`. 5. `send_bits(s, lcodes - 257, 5)`, `dcodes - 1`, `blcodes - 4` in `int`; `Assert`s on the ranges are compiled out. 6. Direct. The caller (L1067) passes `l_desc.max_code + 1` etc. (>= 257, >= 1, >= 4 since `END_BLOCK` has frequency 1).

#### `_tr_stored_block` (L860-875; 16 lines)
1. `void ZLIB_INTERNAL _tr_stored_block(deflate_state *s, charf *buf, ulg stored_len, int last)`. 2. Lib: `bi_windup`; macros `send_bits`, `put_short`; libc `memcpy` (`zmemcpy`). 3. Straight line; `if (stored_len) zmemcpy(...)`. 4. Writes the 3-bit block header, the pad, 4 length bytes and `stored_len` bytes at `pending_buf + pending` from `buf` (`buf` may be NULL only when `stored_len == 0`; I-25), then `pending += stored_len`. 5. `(STORED_BLOCK<<1) + last`; `(ush)stored_len`; `(ush)~stored_len`: the complement in `ulg`, then truncation. 6. Direct.

#### `_tr_flush_bits` (L880-882; 3 lines)
1. `void ZLIB_INTERNAL _tr_flush_bits(deflate_state *s)`. 2. Lib: `bi_flush`. 3-5. None. 6. One call.

#### `_tr_align` (L888-895; 8 lines)
1. `void ZLIB_INTERNAL _tr_align(deflate_state *s)`. 2. Lib: `bi_flush`; macros `send_bits`, `send_code` (with `static_ltree` and `END_BLOCK`). 3. Straight line. 4. Reads `static_ltree[256]` (a static table; `Code` 0, `Len` 7); writes through `send_bits`. 5. `STATIC_TREES<<1`. 6. Direct.

#### `compress_block` (L900-951; 52 lines)
1. `local void compress_block(deflate_state *s, const ct_data *ltree, const ct_data *dtree)`.
2. Macros `send_code`, `send_bits`, `d_code`.
3. `if (s->sym_next != 0) do { ... } while (sx < s->sym_next);` (L908-948), then `send_code(s, END_BLOCK, ltree)` (L950). An `if (dist == 0) {...} else {...}` in the body. No `break`/`continue`.
4. Reads `sym_buf[sx..sx+2]` three bytes per symbol (`dist` low, high, then `lc`) and tables `_length_code`, `extra_lbits`, `base_length`, `_dist_code`, `extra_dbits`, `base_dist`; `ltree`/`dtree` point to the static trees or to the dynamic ones. **Writes `pending_buf` (the same allocation as `sym_buf`)**: no write may reach `sym_buf[sx..]` (the overlay lemma).
5. `dist = s->sym_buf[sx++] & 0xff; dist += (unsigned)(s->sym_buf[sx++] & 0xff) << 8;` (`unsigned`); `lc = s->sym_buf[sx++]` (`int`); `code = _length_code[lc]` (`unsigned`); `send_code(s, code + LITERALS + 1, ltree)`; `lc -= base_length[code]`; `dist--` (now `>= 0` since `dist >= 1`; I-24); `dist -= (unsigned)base_dist[code]`; `send_bits(s, (int)dist, extra)`.
6. Loop state `sx` and the heap; the loop is `doWhile`. Index into `sym_buf` through the shared block: `sym_buf` is `pending_buf` with offset `lit_bufsize`.

#### `detect_data_type` (L966-991)
1. `local int detect_data_type(deflate_state *s)`.
2. None. 3. `for (n = 0; n <= 31; n++, block_mask >>= 1) if ((block_mask & 1) && (s->dyn_ltree[n].Freq != 0)) return Z_BINARY;` (L975-977) then `if (...) return Z_TEXT;` and `for (n = 32; n < LITERALS; n++) if (...) return Z_TEXT;`, final `return Z_BINARY`. The `for` increment has a comma expression `n++, block_mask >>= 1`.
4. Reads `dyn_ltree[n].fc` for `n` 0..255. 5. `unsigned long block_mask = 0xf3ffc07fUL`. 6. Loops with early returns (`Ctl`).

#### `_tr_flush_block` (L997-1089; 93 lines)
1. `void ZLIB_INTERNAL _tr_flush_block(deflate_state *s, charf *buf, ulg stored_len, int last)`.
2. Lib: `detect_data_type`, `build_tree` x2 (through `&s->l_desc`, `&s->d_desc`), `build_bl_tree`, `_tr_stored_block`, `send_bits`, `compress_block`, `send_all_trees`, `init_block`, `bi_windup`.
3. `if (s->level > 0) {...} else {...}` (L1003-1042); then a three-way choice: `if (stored_len + 4 <= opt_lenb && buf != 0) { stored } else if (static_lenb == opt_lenb) { static } else { dynamic }` (L1047-1074); `init_block`; `if (last) bi_windup`. `#ifndef FORCE_STATIC` makes L1035 `if (static_lenb <= opt_lenb || s->strategy == Z_FIXED) opt_lenb = static_lenb;`. `opt_lenb` and `static_lenb` are assigned on both branches (L1027-1028, L1037, L1041), so neither is read uninitialised.
4. Reads/writes `strm->data_type` (L1006-1007), `opt_len`, `static_len`, `l_desc`, `d_desc`, the dyn trees; calls that write `pending_buf`. `buf` points into the window or is NULL; `charf *` is `char *` (cast to `Bytef *` inside `_tr_stored_block`).
5. `opt_lenb = (s->opt_len + 3 + 7) >> 3` (`ulg`); `stored_len + 4 <= opt_lenb`; `(STATIC_TREES<<1) + last`, `(DYN_TREES<<1) + last` (`int`); `max_blindex + 1`, `l_desc.max_code + 1`; `opt_lenb = static_lenb = stored_len + 5` for level 0.
6. Straight line with the three-way `if`. This function is where the overlay proof lives: before `compress_block` the translation must state "the bytes of `sym_buf[0 .. sym_next)` are still those written by the tallies" and after each `send_*` the pending counter bound.

#### `_tr_tally` (L1095-1119; 25 lines; **never called**)
1. `int ZLIB_INTERNAL _tr_tally(deflate_state *s, unsigned dist, unsigned lc)`.
2. None. 3. `if (dist == 0) ... else ...`. 4. Same writes as the inline macros. 5. `s->sym_buf[s->sym_next++] = (uch)dist; ... = (uch)(dist >> 8); ... = (uch)lc;` `dist--`; `d_code(dist)` on an `unsigned`; returns `s->sym_next == s->sym_end`. 6. Translate it (it is compiled and exported) but no proof depends on it; a difftest can call it directly.

### 7.5 `compress.c`, `uncompr.c`

#### `compress2_z` (L24-66; 43 lines)
1. `int ZEXPORT compress2_z(Bytef *dest, z_size_t *destLen, const Bytef *source, z_size_t sourceLen, int level)`.
2. Lib: `deflateInit_` (through the macro `deflateInit(&stream, level)`, `zlib.h` L1942-1943: `deflateInit_((strm), (level), ZLIB_VERSION, (int)sizeof(z_stream))`), `deflate`, `deflateEnd`.
3. `do { ... } while (err == Z_OK);` (L50-61), no `break`; early returns L33, L43, `return err == Z_STREAM_END ? Z_OK : err` at the end.
4. Local `z_stream stream;` **uninitialised** except `zalloc`, `zfree`, `opaque` (L38-40); its address is passed to the library; `deflateInit2_` writes `msg`, `state`, ... Fields not written before first use: `next_in`, `avail_in`, `next_out`, `avail_out` are set at L45-48 before `deflate` is called; `total_in`, `total_out`, `adler`, `data_type` are written by `deflateResetKeep`; `reserved` never. Allocate `stream` as a record in the `streams` table at the declaration and free it before every return (guide: address-taken local). Reads `*destLen` (L32, L35), writes `*destLen = 0` (L36) and `*destLen = next_out - dest` (L63) (D-4).
5. `const uInt max = (uInt)-1;` `left > (z_size_t)max ? max : (uInt)left`; `left -= stream.avail_out`; `sourceLen > (z_size_t)max ? max : (uInt)sourceLen`; `sourceLen -= avail_in`; the `deflate` flush argument is `sourceLen ? Z_NO_FLUSH : Z_FINISH`. `(z_size_t)(stream.next_out - dest)` is a pointer difference converted to unsigned.
6. One `def`; the loop is a recursion on `(err, left, sourceLen)` with the stream in the heap. Termination: when `left == 0` the call has `avail_out == 0` and `deflate` returns `Z_BUF_ERROR` (`Z_STREAM_ERROR`/`Z_BUF_ERROR` leave the loop); when `avail_out > 0` progress is made. State the theorem with `destLen` and `sourceLen` as in `zlib.h`.

#### `compress2` (L67-74; 8 lines)
1. `int ZEXPORT compress2(Bytef *dest, uLongf *destLen, const Bytef *source, uLong sourceLen, int level)`.
2. Lib: `compress2_z`. 3. None. 4. Local `z_size_t got = *destLen;` (L70) with `&got` passed on; `*destLen = (uLong)got;`. **The dereference of `destLen` precedes any NULL test** (R-2). 5. `uLongf` and `z_size_t` are both 64-bit unsigned. 6. A heap cell for `got`; read `*destLen` as a memory read that faults on NULL.

#### `compress_z` (L77-81; 5 lines)
1. `int ZEXPORT compress_z(Bytef *dest, z_size_t *destLen, const Bytef *source, z_size_t sourceLen)`. 2. Lib: `compress2_z(.., Z_DEFAULT_COMPRESSION)` (-1). 3-5. None. 6. One call.

#### `compress` (L82-85; 4 lines)
1. `int ZEXPORT compress(Bytef *dest, uLongf *destLen, const Bytef *source, uLong sourceLen)`. 2. Lib: `compress2(.., Z_DEFAULT_COMPRESSION)`. 3-5. None. 6. One call.

#### `compressBound_z` (L91-95; 5 lines)
1. `z_size_t ZEXPORT compressBound_z(z_size_t sourceLen)`. 2. None. 3. Conditional expression `bound < sourceLen ? (z_size_t)-1 : bound`. 4. None. 5. `sourceLen + (sourceLen >> 12) + (sourceLen >> 14) + (sourceLen >> 25) + 13` in `z_size_t`, wraps on purpose; the test detects the wrap. 6. Pure `def`.

#### `compressBound` (L96-99; 4 lines)
1. `uLong ZEXPORT compressBound(uLong sourceLen)`. 2. Lib: `compressBound_z`. 3. Conditional on `(uLong)bound != bound` (always false on LP64). 4. None. 5. None. 6. Direct.

#### `uncompress2_z` (uncompr.c L29-82; 54 lines)
1. `int ZEXPORT uncompress2_z(Bytef *dest, z_size_t *destLen, const Bytef *source, z_size_t *sourceLen)`.
2. Lib: `inflateInit_` (macro `inflateInit(&stream)`, `zlib.h` L1944-1945), `inflate`, `inflateEnd`.
3. `do { ... } while (err == Z_OK);` (L57-67), no `break`; early returns L38, L52; final `return` with a three-way conditional expression (L78-81).
4. Local `z_stream stream` (uninitialised except `next_in`, `avail_in`, `zalloc`, `zfree`, `opaque`, `next_out`, `avail_out`); `if (left == 0 && dest == Z_NULL) dest = (Bytef *)&stream.reserved;` (D-5). Reads `*sourceLen`, `*destLen`, writes both at L74-75 (`*sourceLen -= len; *destLen -= left;`).
5. `max = (uInt)-1` chunks as in `compress2_z`; `len += stream.avail_in`, `left += stream.avail_out`; `err == Z_BUF_ERROR && len == 0 ? Z_DATA_ERROR : err`.
6. Same shape as `compress2_z`; remember `inflateEnd(&stream)` precedes the return (L77) and its result is ignored.

#### `uncompress2` (L83-91; 9 lines)
1. `int ZEXPORT uncompress2(Bytef *dest, uLongf *destLen, const Bytef *source, uLong *sourceLen)`. 2. Lib: `uncompress2_z`. 3. None. 4. Locals `got` and `used` (L86: `z_size_t got = *destLen, used = *sourceLen;`) with addresses taken; both dereferences precede any NULL test (R-2); writes `*sourceLen = (uLong)used; *destLen = (uLong)got;`. 5. 64-bit unsigned throughout. 6. Two heap cells.

#### `uncompress_z` (L92-96; 5 lines)
1. `int ZEXPORT uncompress_z(Bytef *dest, z_size_t *destLen, const Bytef *source, z_size_t sourceLen)`. 2. Lib: `uncompress2_z(dest, destLen, source, &used)`. 3. None. 4. Local `used` with its address taken. 5. None. 6. A heap cell for `used`.

#### `uncompress` (L97-101; 5 lines)
1. `int ZEXPORT uncompress(Bytef *dest, uLongf *destLen, const Bytef *source, uLong sourceLen)`. 2. Lib: `uncompress2(dest, destLen, source, &used)`. 3. None. 4. Local `uLong used`, address taken. 5. None. 6. A heap cell.

## 8. Headers

* `deflate.h`: constants and the state struct (section 4.2); the status macros; `put_byte`, `d_code`, `_tr_tally_lit`, `_tr_tally_dist` (section 5); the externs `_length_code`, `_dist_code` are `const uch[]` (L334-335) in the default build because `STDC` is defined and `GEN_TREES_H` is not.
* `trees.h`: data only (section 3).
* `zutil.h`: `ERR_MSG`, `ERR_RETURN`, `ZALLOC`, `ZFREE`, `TRY_FREE`, the `zmem*` macros, `MIN_MATCH` 3, `MAX_MATCH` 258, `PRESET_DICT`, `OS_CODE`, `DEF_MEM_LEVEL`, `Assert`/`Trace*` (empty), `ZSWAP32` (used by inflate only), the `z_once` machinery (not compiled). `uch`, `ush`, `ulg`, `uchf`, `ushf` typedefs (L43-47).
* `zlib.h`: `z_stream` (L90-110), `gz_header` (L118-133), the constants (L172-216), the macros `deflateInit` etc. (L1942-1951), `struct gzFile_s` (L1966-1970), the `gzgetc` macro (L1977-1978; used by applications, not by the library). `ZLIB_VERSION`, `MAX_WBITS`, `MAX_MEM_LEVEL` (`zconf.h`: 15 and 9). `z_off_t`/`z_off64_t` are `off_t`/`off64_t` = `long`.

## 9. The five hardest functions

1. **`deflate_stored`**: mixed `unsigned`/`long`/`ulg` arithmetic with many wrap and truncation points, a direct-copy path that bypasses the window, a window slide with `memcpy` whose ranges must be shown disjoint, and an interaction with `deflateParams` through `matches` (level 0 keeps the number of pending hash slides). The translation must pick the right integer type at about 25 places; the proof needs `insert <= strstart`, `block_start >= 0` and the pending-buffer capacity.
2. **`deflate`**: 310 lines, 18 returns, a state machine whose state (`status`, `gzindex`, `pending`, `last_flush`) lives in the heap and must survive a return in the middle of the gzip header; three loops with returns; the overall safety and functional theorem needs invariants over every status.
3. **`_tr_flush_block` with `compress_block` (the overlay)**: `compress_block` reads `sym_buf` while `send_bits` writes `pending_buf`, which is the same allocation shifted by `lit_bufsize`. Nothing in the C checks the margin; it follows from the choice of block type (a dynamic block is chosen only if smaller than the fixed one) and from properties of `build_tree`. The earlier repository's `docs/DEFLATE_OVERLAY.md` records the long analysis (exact accounting of the margin, a kernel-checked case analysis for `memLevel` 4 to 9, and an LP relaxation for `memLevel` 1 to 3).
4. **`gen_bitlen` (with `build_tree`)**: the bit-length repair loop (L583-612) indexes `bl_count` downwards without a lower bound and `heap` downwards through `--h`; their safety is a Huffman-tree theorem; `ulg` arithmetic wraps on purpose; the union aliasing `Dad`/`Len` (overwritten in the same pass).
5. **`longest_match` together with `fill_window`**: unrolled pointer scans that read bytes beyond the valid data (bounded by the zeroed `WIN_INIT` margin), a `continue` into a loop condition with a side effect, and the hash-chain invariant (a chain is built only from inserted positions; the `prev` slots read were written for those positions) which `fill_window`'s slide must preserve.

Runner-up: `crc32_z` (alignment by address, pointer cast to words, `while (--blks)`) is the hardest function for *fidelity* but its proof is a finite case analysis; `deflateCopy` (whole-struct copy with pointer fix-ups and a data-dependent `memcpy` size).

## 10. Surprising or possibly buggy

1. `multmodp` loops forever when `a != 0` but `a & 0xffffffff == 0` (`crc32.c` L163-178, reached from `crc32_combine_op` L972): `crc32_combine_op(1, 2, 1UL << 32)` never returns (**run**). `zlib.h` says `op` comes from `crc32_combine_gen`, so this is a robustness issue of an undocumented misuse.
2. `compress2` (L70) and `uncompress2` (L86) read `*destLen` (and `*sourceLen`) before the `_z` function can test it for `NULL`: `compress2(d, NULL, s, 1, 6)` segfaults (**run**) although `compress2_z` returns `Z_STREAM_ERROR` for a `NULL` `destLen`.
3. `deflateSetDictionary` leaves `strm->total_in` increased by the dictionary length (L596, via `read_buf` L237); reproduced in the earlier repository (`docs/findings/deflatesetdict-total-in`). `zlib.h` calls `total_in` the "total number of input bytes read so far"; whether it counts the dictionary is not documented.
4. `_tr_tally` (`trees.c` L1095-1119) is compiled, exported (`ZLIB_INTERNAL`) and never called in the default build: the library uses the inline macros. Its logic duplicates `_tr_tally_dist` and could diverge unnoticed.
5. `trees.c` `tr_static_init` is an empty function in the default build, yet `_tr_init` still calls it; the translation of the static trees is the data of `trees.h`. A translator who follows the file top to bottom will find a lot of code (L295-434) that is not compiled.
6. `send_bits` and `_tr_tally_dist` declare local variables named `len`, `val`, `dist` (macro hygiene, section 5); no current call is affected, but a new call site could be. `_tr_tally_dist`'s `dist--` on a `ush` wraps to 65535 for `dist == 0` and then indexes `_dist_code[767]` (table of 512); callers never pass 0 (I-2).
7. `deflate.c` L1137 and neighbours dereference `s->gzhead` without a test; `deflateSetHeader(strm, NULL)` is accepted at any time (L728-733 only tests `wrap != 2`), so `deflateSetHeader(strm, NULL)` after the header began makes the next `deflate` read `NULL->extra`. `zlib.h` restricts the call to before the first `deflate`, so this is a misuse, but the invariant "status in {EXTRA, NAME, COMMENT, HCRC} implies `gzhead != NULL`" is not maintained by the code itself.
8. `crc32.c` has `crc5`/`word5` declarations in `#if N > 5` blocks that are compiled out, and ARM, big-endian and `W == 4` variants that are compiled or not depending on the build; the default build compiles the big-endian branch (L790-912) although it can never run on x86_64 (the `endian` test is a run-time test through a pointer to a local).
9. `deflate.c` L1759-1763, L2155, `trees.c` L1075 etc. contain `Assert`s that document invariants the proofs need (`pending < lit_bufsize + sx`, `scan <= window + window_size - 1`); they are compiled out. They are a useful list of what the authors believed.
