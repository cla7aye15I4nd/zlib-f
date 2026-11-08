import ZlibF.Proof.«inflate.c.fast-view-body-break-effect»
import ZlibF.Proof.«inflate.c.fast-view-terminal-frame»
import ZlibF.Proof.«inflate.c.fast-memory-shape-primitives»
import ZlibF.Proof.«inflate.c.fast-view-output-effect»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- Every actual fast body exit, including BAD and TYPE, preserves the
original caller output interval outside its writable bytes. -/
theorem fast_break_effect_buffer_frame
    {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {slow : IL}
    {l result : Zlib.Inffast.L}
    (effect :
      (result.broke = l.broke ∧
        BufferFrame h after (fun b => StreamRoot r b ∨ b = zs)
          [⟨slow.put, slow.left.toNat⟩]) ∨
      (∃ i, result.broke = true ∧
        after = badHeap h r zs z s i) ∨
      after = setI h zs { s with mode := TYPE })
    (hz : r.get h = some z)
    (hs : h.istates zs = some s) :
    BufferFrame h after (fun b => StreamRoot r b ∨ b = zs)
      [⟨slow.put, slow.left.toNat⟩] := by
  rcases effect with ⟨_, frame⟩ | ⟨i, _, heapEq⟩ | heapEq
  · exact frame
  · rw [heapEq]
    exact (badHeap_buffer_frame hz hs i
      [⟨slow.put, slow.left.toNat⟩]).1
  · rw [heapEq]
    exact (fast_terminal_buffer_frame hz hs
      [⟨slow.put, slow.left.toNat⟩]).1

#print axioms fast_break_effect_buffer_frame

/-- The source effects of an actual fast body preserve object shape. -/
theorem FastOutputEffect.shape
    {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {slow : IL}
    {dest : BRef} {output : Array UInt8}
    (effect : FastOutputEffect h after r zs z s slow dest)
    (hz : r.get h = some z)
    (hs : h.istates zs = some s)
    (outputGet : Space.get h dest = some output)
    (outputWrite : Space.ro h dest = false) :
    Shape h after := by
  rcases effect with ⟨array, heapEq, _⟩ | ⟨i, heapEq⟩ | heapEq
  · rw [heapEq]
    exact fast_byte_view_put_shape outputGet outputWrite
  · rw [heapEq]
    exact (shape_put hz _).trans
      (shape_setI (by simpa using hs) _)
  · rw [heapEq]
    exact shape_setI hs _

#print axioms FastOutputEffect.shape

end Zlib.Inflate.Proofs
