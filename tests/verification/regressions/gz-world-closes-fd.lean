import ZlibF.Spec.Public.GzSafety

/-!
# gz: another party may close or reuse the handle's descriptor

`GzWorldStep` required that a world step between two calls keep the handle's descriptor open or closed: only the
library could close it. zlib.h states no such rule. The C runs cleanly when the application, or another handle on
the same descriptor, closes it or opens another file under its number: the next `read` or `write` returns `-1` with
`EBADF`, or reaches the other file. The rule narrowed the domain of `Goal.gz_sequence_safety` silently.

The step is now any well-formed file-system state. Below: a history continues through a world in which the
handle's descriptor was open and is closed, and through one in which it was closed and is open again, so every
conclusion of the goal applies after it.
-/

namespace GzWorldClosesFdRegression
open C Zlib.GzFs ZlibF.Spec.Public

/-- **Another party closes the handle's descriptor**: the history goes on. -/
theorem closed_by_other {h : Heap} {fs fs' : Fs} {i : Nat} {s : GzState} (hist : GzHistory h fs i)
    (hs : h.gzstates i = some s) (hfs : FileSystem fs') (_h0 : 0 ≤ s.fd.toInt)
    (_before : GzOracle.FdOpen fs s.fd.toInt.toNat) (_after : ¬ GzOracle.FdOpen fs' s.fd.toInt.toNat) :
    GzHistory h fs' i :=
  .world hist hs hfs

/-- **Another party reuses the descriptor's number**: the history goes on. -/
theorem reused_by_other {h : Heap} {fs fs' : Fs} {i : Nat} {s : GzState} (hist : GzHistory h fs i)
    (hs : h.gzstates i = some s) (hfs : FileSystem fs') (_h0 : 0 ≤ s.fd.toInt)
    (_before : ¬ GzOracle.FdOpen fs s.fd.toInt.toNat) (_after : GzOracle.FdOpen fs' s.fd.toInt.toNat) :
    GzHistory h fs' i :=
  .world hist hs hfs

end GzWorldClosesFdRegression
