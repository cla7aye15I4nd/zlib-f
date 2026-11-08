import ZlibF.Proof.«inflate.c.fast-writeback-frame»
import ZlibF.Proof.«inflate.c.misc»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- A decoded end-of-block changes only the inflate state mode. Its fast
local `broke` flag stops the fast loop without writing a caller byte. -/
theorem fast_terminal_buffer_frame
    {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState}
    (hz : r.get h = some z) (hs : h.istates zs = some s)
    (regions : List Region) :
    BufferFrame h (setI h zs { s with mode := TYPE })
      (fun b => StreamRoot r b ∨ b = zs) regions ∧
    LiveChange h (setI h zs { s with mode := TYPE })
      (fun _ => False) (fun _ => False) ∧
    (setI h zs { s with mode := TYPE }).nalloc = h.nalloc := by
  have frame := fastWriteback_heap_frame hz hs z
    { s with mode := TYPE } regions
  simpa only [ZStreamRef.put_self hz] using frame

#print axioms fast_terminal_buffer_frame

end Zlib.Inflate.Proofs
