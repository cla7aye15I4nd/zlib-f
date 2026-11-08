import ZlibF.Proof.«inflate.c.fast-view-body-break-effect»
import ZlibF.Proof.«inflate.c.fast-view-terminal-frame»

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

end Zlib.Inflate.Proofs
