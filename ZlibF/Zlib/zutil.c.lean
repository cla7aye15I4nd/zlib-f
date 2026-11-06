import ZlibF.Runtime.Alloc

/-!
# zutil.c — faithful translation

Source: `zutil.c` of the verified source, default x86_64 Linux build (LP64, `Z_SOLO`, `ZLIB_DEBUG`, `SYS16BIT`,
`_WIN32_WCE` undefined; `STDC` and `HAVE_MEMCPY` defined, so the `#ifndef HAVE_MEMCPY` functions `zmemcpy`,
`zmemcmp`, `zmemzero` are not compiled: the macros of `zutil.h` expand to `memcpy`, `memcmp`, `memset`, which the
runtime provides). Live: `z_errmsg`, `zlibVersion`, `zlibCompileFlags`, `zError`, `zcalloc`, `zcfree`.

Decisions:

* **String literals.** A string literal is a static read-only array of bytes in C. `strLit` is `strLitRef`: the pointer
  to the literal number `i` of `strTable` (`BRef.str i`), the same pointer every time, no block allocated, nothing
  to free. The set of literals is the string literals of the library sources; a text outside it is a fault.
* `z_errmsg` (an array of 10 pointers to literals) is the Lean array of the 10 texts; `ERR_MSG` indexes it and then
  gives the literal.
* `sizeof` values of the LP64 target: `uInt` 4, `uLong` 8, `voidpf` 8, `z_off_t` 8.
-/

namespace Zlib.Zutil
open C

/-- A string literal of the C sources (see the file comment): `strLitRef s`. -/
def strLit (s : String) : M BPtr := strLitRef s

/-- `z_const char * const z_errmsg[10]`: the texts, indexed by `2 - error code`. -/
def z_errmsg : Array String :=
  #["need dictionary",      -- Z_NEED_DICT       2
    "stream end",           -- Z_STREAM_END      1
    "",                     -- Z_OK              0
    "file error",           -- Z_ERRNO         (-1)
    "stream error",         -- Z_STREAM_ERROR  (-2)
    "data error",           -- Z_DATA_ERROR    (-3)
    "insufficient memory",  -- Z_MEM_ERROR     (-4)
    "buffer error",         -- Z_BUF_ERROR     (-5)
    "incompatible version", -- Z_VERSION_ERROR (-6)
    ""]

/-- `const char * ZEXPORT zlibVersion(void)` -/
def zlibVersion : M BPtr :=
  -- return ZLIB_VERSION;
  strLit ZLIB_VERSION

/-- `uLong ZEXPORT zlibCompileFlags(void)` -/
def zlibCompileFlags : M UInt64 := do
  -- flags = 0;
  let flags : UInt64 := 0
  -- switch ((int)(sizeof(uInt))) { case 2: break; case 4: flags += 1; break; case 8: flags += 2; break; default: flags += 3; }
  let sz : Int32 := 4
  let flags := if sz == 2 then flags else if sz == 4 then flags + 1 else if sz == 8 then flags + 2 else flags + 3
  -- switch ((int)(sizeof(uLong))) { ... case 4: flags += 1 << 2; case 8: flags += 2 << 2; default: flags += 3 << 2; }
  let sz : Int32 := 8
  let flags := if sz == 2 then flags else if sz == 4 then flags + ((1 : UInt64) <<< 2) else if sz == 8 then flags + ((2 : UInt64) <<< 2)
    else flags + ((3 : UInt64) <<< 2)
  -- switch ((int)(sizeof(voidpf))) { ... << 4 }
  let sz : Int32 := 8
  let flags := if sz == 2 then flags else if sz == 4 then flags + ((1 : UInt64) <<< 4) else if sz == 8 then flags + ((2 : UInt64) <<< 4)
    else flags + ((3 : UInt64) <<< 4)
  -- switch ((int)(sizeof(z_off_t))) { ... << 6 }
  let sz : Int32 := 8
  let flags := if sz == 2 then flags else if sz == 4 then flags + ((1 : UInt64) <<< 6) else if sz == 8 then flags + ((2 : UInt64) <<< 6)
    else flags + ((3 : UInt64) <<< 6)
  -- ZLIB_DEBUG, ZLIB_WINAPI, BUILDFIXED, DYNAMIC_CRC_TABLE, NO_GZCOMPRESS, NO_GZIP, PKZIP_BUG_WORKAROUND, FASTEST,
  -- NO_vsnprintf, HAS_vsnprintf_void: all undefined in the default build (STDC is defined, so the
  -- `#else flags += 1L << 24` branch is dead).
  -- return flags;
  return flags

/-- `const char * ZEXPORT zError(int err)`  (`ERR_MSG(err)` is
`z_errmsg[(err) < -6 || (err) > 2 ? 9 : 2 - (err)]`) -/
def zError (err : Int32) : M BPtr := do
  let i : Int32 := if err < -6 || err > 2 then 9 else 2 - err
  -- the index is in 0..9 for every err, so the access is inside the array
  match z_errmsg[i.toInt.toNat]? with
  | some s => strLit s
  | none => ub "z_errmsg index outside its array"

/-- `voidpf ZLIB_INTERNAL zcalloc(voidpf opaque, unsigned items, unsigned size)` (the default allocator, `malloc` branch
since `sizeof(uInt) > 2`; the product is computed in `unsigned`). -/
def zcalloc («opaque» : BPtr) (items size : UInt32) : M BPtr := do
  -- (void)opaque;
  let _ := «opaque»
  -- return sizeof(uInt) > 2 ? (voidpf)malloc(items * size) : (voidpf)calloc(items, size);
  allocB (items * size).toNat

/-- `void ZLIB_INTERNAL zcfree(voidpf opaque, voidpf ptr)` -/
def zcfree («opaque» ptr : BPtr) : M Unit := do
  -- (void)opaque;
  let _ := «opaque»
  -- free(ptr);
  freeB ptr

end Zlib.Zutil
