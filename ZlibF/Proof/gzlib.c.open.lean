import ZlibF.Proof.«public-gz-offset»
import ZlibF.Spec.Public.GzOpen

/-!
# gzlib.c: open refusal and initial allocation failure

These execution lemmas cover the front of the actual open functions. They do not
prove successful mode parsing, handle construction or the complete public targets.
Null arguments are checked before allocation by `gz_open`. `gzdopen` first rejects
negative descriptors and then allocates its temporary path.
-/

namespace Zlib.Gzlib.Proofs
open C Zlib.GzFs Zlib.Gzguts Zlib.Gzlib.Spec ZlibF.Spec.Public.OffsetProof

/-- `gzFile gz_open(const void *path, int fd, const char *mode)` rejects NULL first. -/
theorem gz_open_null (h : Heap) (fs : Fs) (path : BPtr) (fd : Int32) (mode : BPtr)
    (hn : path = .null ∨ mode = .null) :
    gz_open path fd mode fs h = .ok ((none, fs), h) := by
  unfold gz_open
  offsetsimp [hn]

/-- `gzFile gzopen(const char *path, const char *mode)` rejects either NULL argument. -/
theorem gzopen_null (h : Heap) (fs : Fs) (path mode : BPtr)
    (hn : path = .null ∨ mode = .null) :
    gzopen path mode fs h = .ok ((none, fs), h) := gz_open_null h fs path (-1) mode hn

/-- `gzFile gzopen64(const char *path, const char *mode)` rejects either NULL argument. -/
theorem gzopen64_null (h : Heap) (fs : Fs) (path mode : BPtr)
    (hn : path = .null ∨ mode = .null) :
    gzopen64 path mode fs h = .ok ((none, fs), h) := gz_open_null h fs path (-1) mode hn

/-- `gzFile gz_open(const void *path, int fd, const char *mode)` returns NULL when
its first allocation fails. No path or mode byte is read; no descriptor is opened. -/
theorem gz_open_alloc_failure (h : Heap) (fs : Fs) (path : BPtr) (fd : Int32) (mode : BPtr)
    (hp : path ≠ .null) (hm : mode ≠ .null) (hf : h.allocOk h.nalloc = false) :
    gz_open path fd mode fs h = .ok ((none, fs), { h with nalloc := h.nalloc + 1 }) := by
  unfold gz_open
  offsetsimp [hp, hm, allocGzState, hf]

/-- `gzFile gzopen(const char *path, const char *mode)` has exact first-allocation failure effects. -/
theorem gzopen_alloc_failure (h : Heap) (fs : Fs) (path mode : BPtr)
    (hp : path ≠ .null) (hm : mode ≠ .null) (hf : h.allocOk h.nalloc = false) :
    gzopen path mode fs h = .ok ((none, fs), { h with nalloc := h.nalloc + 1 }) :=
  gz_open_alloc_failure h fs path (-1) mode hp hm hf

/-- `gzFile gzopen64(const char *path, const char *mode)` has the same allocation failure effects. -/
theorem gzopen64_alloc_failure (h : Heap) (fs : Fs) (path mode : BPtr)
    (hp : path ≠ .null) (hm : mode ≠ .null) (hf : h.allocOk h.nalloc = false) :
    gzopen64 path mode fs h = .ok ((none, fs), { h with nalloc := h.nalloc + 1 }) :=
  gz_open_alloc_failure h fs path (-1) mode hp hm hf

/-- `gzFile gzdopen(int fd, const char *mode)` rejects negative descriptors before allocation. -/
theorem gzdopen_negative (h : Heap) (fs : Fs) (fd : Int32) (mode : BPtr) (hf : fd < 0) :
    gzdopen fd mode fs h = .ok ((none, fs), h) := by
  unfold gzdopen
  offsetsimp [hf]

/-- `gzFile gzdopen(int fd, const char *mode)` retains the descriptor when its temporary
path allocation fails. The allocation counter advances once and no other heap field changes. -/
theorem gzdopen_alloc_failure (h : Heap) (fs : Fs) (fd : Int32) (mode : BPtr)
    (hn : ¬ fd < 0) (hf : h.allocOk h.nalloc = false) :
    gzdopen fd mode fs h = .ok ((none, fs), { h with nalloc := h.nalloc + 1 }) := by
  unfold gzdopen
  offsetsimp [hn, allocB, hf]

#print axioms gz_open_alloc_failure
#print axioms gzdopen_alloc_failure
end Zlib.Gzlib.Proofs
