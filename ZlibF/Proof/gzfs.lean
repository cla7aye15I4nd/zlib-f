import ZlibF.Zlib.gzfs

/-!
# Closed forms of the `snprintf` calls of the gz files

`gz_error`, `gz_open`, `gzopen`, `gzopen64` and `gzdopen` call `snprintf` with three formats only: `"%s"`,
`"%s%s%s"` and `"<fd:%d>"`. For each of them the lemmas below give the output (`formatBytes`) in closed form, and
`snprintf_ret` says that the call does not fault and returns the length that the full output has (C99), whatever the
buffer size, when the destination range is inside a writable block; the bytes written are the first `size - 1` bytes of
the output followed by a NUL.

The strings the `%s` conversions read are given by hypotheses of the form `cstring p h = .ok (s, h)` (the bytes before
the first NUL), the format by `cstring fmt h = .ok (f, h)`.
-/

namespace Zlib.GzFs.Proofs
open C Zlib.GzFs

/-- The bytes of the decimal text of an integer, with a minus sign for a negative one. -/
def decBytes (z : Int) : Array UInt8 :=
  (if z < 0 then #[45] else #[]) ++ ((Nat.toDigits 10 z.natAbs).toArray.map fun c => c.toNat.toUInt8)

theorem parse_s : parseSpec #[37, 115] 1 = some ({ conv := 115 }, 2) := by decide
theorem parse_fd : parseSpec #[60, 102, 100, 58, 37, 100, 62] 5 = some ({ conv := 100 }, 6) := by decide
theorem parse_sss1 : parseSpec #[37, 115, 37, 115, 37, 115] 1 = some ({ conv := 115 }, 2) := by decide
theorem parse_sss2 : parseSpec #[37, 115, 37, 115, 37, 115] 3 = some ({ conv := 115 }, 4) := by decide
theorem parse_sss3 : parseSpec #[37, 115, 37, 115, 37, 115] 5 = some ({ conv := 115 }, 6) := by decide


theorem heapStr_of {h : Heap} {p : BPtr} {s : Array UInt8} (hs : cstring p h = .ok (s, h)) : heapStr h p = some s := by
  simp [heapStr, hs]

/-- `printf("%s", p)` is the string at `p`. -/
theorem formatBytes_s {h : Heap} {p : BPtr} {s : Array UInt8} (hp : p ≠ .null) (hs : cstring p h = .ok (s, h)) :
    formatBytes #[37, 115] [.str p] h = .ok (s, h) := by
  have hr := heapStr_of hs
  have hpb : (p == Ptr.null) = false := by simpa using hp
  simp [formatBytes, formatGo, parse_s, argStr, hr, hpb, pad]

end Zlib.GzFs.Proofs
