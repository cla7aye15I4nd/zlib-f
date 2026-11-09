import ZlibF.Proof.«inflate.c.local-fast-copy-exact-output-window»
import ZlibF.Proof.«inflate.c.local-fast-exact-output-interface»
import ZlibF.Proof.«inflate.c.local-fast-copy-match-invariant»
import ZlibF.Proof.«inflate.c.slow-output-exact-frame»
import ZlibF.Proof.«inflate.c.fast-view-bad-data-frame»

/-! Exact caller-byte effects of the actual fast match branches.
The interval comes from actual copy arrays and their outside-cell equations.
A remaining-capacity frame is never used to infer the written interval. -/
namespace Zlib.Inflate.Local
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

theorem FastInputPacket.copyMatch_valid_exact_output_frame
    {cutoff : Nat}
    {h : Heap} {slow : IL} {bs : List UInt8}
    {l : Zlib.Inffast.L} {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow bs l)
    (invariant : LocalStateJ h cutoff r zs z s)
    (buffers : DispatchBuffers h r slow bs)
    (left : slow.left ≠ 0)
    (length : 3 ≤ l.len.toNat)
    (whaveBound : c.whave.toNat ≤ c.wsize.toNat)
    (wnextBound : c.wnext.toNat ≤ c.wsize.toNat)
    (wsizeBound : c.wsize.toNat ≤ 32768)
    {dest : BRef} {output : Array UInt8} {oo j : Nat}
    (outPtr : l.out = .ref dest j)
    (outputPtr : slow.put = .ref dest oo)
    (outputGet : Space.get h dest = some output)
    (outputWrite : Space.ro h dest = false)
    (outputSize : oo + slow.left.toNat ≤ output.size)
    (outputRoom : oo ≤ j ∧
      j + l.len.toNat ≤ oo + slow.left.toNat)
    (produced : l.op.toNat ≤ j)
    (distanceValid : l.dist > l.op →
      ¬ l.dist - l.op > c.whave)
    (windowData : l.dist > l.op →
      ¬ l.dist - l.op > c.whave →
      ∃ (window : BRef) (saved : Array UInt8) (woff : Nat),
        window ≠ dest ∧
        c.window = .ref window woff ∧
        Space.get h window = some saved ∧
        woff + c.wsize.toNat ≤ saved.size)
    {result : Zlib.Inffast.L} {after : Heap}
    (observed : C.run (Zlib.Inffast.copyMatch c l) h = .ok (result, after)) :
    result.out = .ref dest (j + l.len.toNat) ∧
    BufferFrame h after (fun _ => False) [⟨.ref dest j, l.len.toNat⟩] := by
  by_cases windowBranch : l.dist > l.op
  · obtain ⟨window, saved, woff, different, windowPtr, windowGet, windowSize⟩ :=
      windowData windowBranch (distanceValid windowBranch)
    obtain ⟨value, finalHeap, array, run, _, _, _, _, out, _, _, _, _, size, _, heapEq, _, segment⟩ :=
      Zlib.Inflate.Local.FastInputPacket.copyMatch_window_valid_exact_output_segment packet
        invariant buffers left windowBranch (distanceValid windowBranch)
        whaveBound wnextBound wsizeBound different windowPtr windowGet windowSize
        outPtr outputPtr outputGet outputWrite outputSize outputRoom produced
    have same := Prod.mk.inj (Except.ok.inj (run.symm.trans observed))
    rcases same with ⟨rfl, rfl⟩
    refine ⟨out, ?_⟩
    rw [heapEq]
    exact byte_view_segment_buffer_frame outputGet outputWrite size segment
  · have distance : l.dist.toNat ≤ j := by
      have notLess : ¬ l.op.toNat < l.dist.toNat := by
        intro contrary
        exact windowBranch (UInt32.lt_iff_toNat_lt.mpr contrary)
      omega
    obtain ⟨value, finalHeap, run, _, _, _, _, resultEq, _, _, heapEq, _⟩ :=
      Zlib.Inflate.Local.FastInputPacket.copyMatch_direct_local_state packet invariant buffers
        left windowBranch distance length outPtr outputPtr outputGet outputWrite outputSize outputRoom
    have same := Prod.mk.inj (Except.ok.inj (run.symm.trans observed))
    rcases same with ⟨rfl, rfl⟩
    refine ⟨by rw [resultEq], ?_⟩
    rw [heapEq]
    exact byte_view_segment_buffer_frame outputGet outputWrite
      (Zlib.Inffast.Proofs.cpyN_size _ _ _ _)
      (ArraySegmentFrame.cpy l.len.toNat (j - l.dist.toNat) j output)

theorem FastInputPacket.copyMatch_exact_output
    {cutoff : Nat}
    {h : Heap} {slow : IL} {bs : List UInt8}
    {l : Zlib.Inffast.L} {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow bs l)
    (invariant : LocalStateJ h cutoff r zs z s)
    (buffers : DispatchBuffers h r slow bs)
    (streamPtr : c.strm = some r)
    (statePtr : c.state = some (.tab zs))
    (left : slow.left ≠ 0)
    (length : 3 ≤ l.len.toNat)
    (whaveBound : c.whave.toNat ≤ c.wsize.toNat)
    (wnextBound : c.wnext.toNat ≤ c.wsize.toNat)
    (wsizeBound : c.wsize.toNat ≤ 32768)
    {dest : BRef} {output : Array UInt8} {oo j : Nat}
    (outPtr : l.out = .ref dest j)
    (outputPtr : slow.put = .ref dest oo)
    (outputGet : Space.get h dest = some output)
    (outputWrite : Space.ro h dest = false)
    (outputSize : oo + slow.left.toNat ≤ output.size)
    (outputRoom : oo ≤ j ∧
      j + l.len.toNat ≤ oo + slow.left.toNat)
    (produced : l.op.toNat ≤ j)
    (windowData : l.dist > l.op →
      ¬ l.dist - l.op > c.whave →
      ∃ (window : BRef) (saved : Array UInt8) (woff : Nat),
        window ≠ dest ∧
        c.window = .ref window woff ∧
        Space.get h window = some saved ∧
        woff + c.wsize.toNat ≤ saved.size)
    {result : Zlib.Inffast.L} {after : Heap}
    (observed : C.run (Zlib.Inffast.copyMatch c l) h = .ok (result, after)) :
    FastExactOutput h after r zs dest j result := by
  have validFrame (valid : l.dist > l.op → ¬ l.dist - l.op > c.whave) :
      FastExactOutput h after r zs dest j result := by
    obtain ⟨out, frame⟩ :=
      Zlib.Inflate.Local.FastInputPacket.copyMatch_valid_exact_output_frame packet invariant buffers
        left length whaveBound wnextBound wsizeBound outPtr outputPtr outputGet outputWrite
        outputSize outputRoom produced valid windowData observed
    refine ⟨j + l.len.toNat, out, by omega, ?_⟩
    have permitted := bufferFrame_weaken (wider := fun b => StreamRoot r b ∨ b = zs)
      (fun _ impossible => False.elim impossible) frame
    simpa only [Nat.add_sub_cancel_left] using permitted
  by_cases windowBranch : l.dist > l.op
  · by_cases invalidBack : l.dist - l.op > c.whave
    · obtain ⟨i, finalHeap, run, heapEq, _, _, _, _, _, _⟩ :=
        Zlib.Inflate.Local.FastInputPacket.copyMatch_invalid_local_state packet invariant buffers
          streamPtr statePtr windowBranch invalidBack outputGet outputWrite
      have same := Prod.mk.inj (Except.ok.inj (run.symm.trans observed))
      rcases same with ⟨rfl, rfl⟩
      refine ⟨j, outPtr, Nat.le_refl _, ?_⟩
      rw [Nat.sub_self, heapEq]
      exact (badHeap_buffer_frame invariant.good.live.hz invariant.good.live.hs i
        [⟨.ref dest j, 0⟩]).1
    · exact validFrame (fun _ => invalidBack)
  · exact validFrame (fun selected => False.elim (windowBranch selected))

#print axioms FastInputPacket.copyMatch_valid_exact_output_frame
#print axioms FastInputPacket.copyMatch_exact_output
end Zlib.Inflate.Local
