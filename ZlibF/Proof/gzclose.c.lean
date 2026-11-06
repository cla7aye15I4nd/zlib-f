import ZlibF.Proof.«gzlib.c.seek»
import ZlibF.Zlib.«gzclose.c»

/-!
# gzclose.c: `gzclose`

`gzclose` dispatches on the mode of the handle: a reader goes to `gzclose_r` (`gzread.c`), every other handle to
`gzclose_w` (`gzwrite.c`). What `gzclose_r` and `gzclose_w` do (free the stream, the buffers, the path and the message,
close the descriptor, return the error) is stated and proved with those files; this module proves the dispatch and the
null-handle case, which need only the invariant of the handle.
-/

namespace Zlib.Gzclose.Proofs
open C Zlib.GzFs Zlib.Gzguts Zlib.Gzlib Zlib.Gzlib.Spec Zlib.Gzlib.Proofs

/-- `gzclose(NULL)` is `Z_STREAM_ERROR`, nothing else happens. -/
theorem gzclose_null (fs : Fs) (h : Heap) :
    Zlib.Gzclose.gzclose none fs h = .ok ((Z_STREAM_ERROR, fs), h) := rfl

/-- **gzclose, dispatch.** On a handle that satisfies the invariant, `gzclose` is `gzclose_r` for a reader and `gzclose_w`
for a writer (the state is read once, nothing else is done before the call). -/
theorem gzclose_dispatch {h : Heap} {gs : Nat} {s : GzState} (hG : GzGood h gs s) (fs : Fs) :
    Zlib.Gzclose.gzclose (hnd gs) fs h =
      if s.mode = GZ_READ then Zlib.Gzread.gzclose_r (hnd gs) fs h else Zlib.Gzwrite.gzclose_w (hnd gs) fs h := by
  have hs := hG.hs
  unfold Zlib.Gzclose.gzclose
  by_cases hm : s.mode = GZ_READ
  · ggsimp [hs, hm]
  · ggsimp [hs, hm]

end Zlib.Gzclose.Proofs
