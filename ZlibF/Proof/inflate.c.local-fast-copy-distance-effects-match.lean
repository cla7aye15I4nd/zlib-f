import ZlibF.Proof.«inflate.c.local-fast-copy-distance-effects-common»
import ZlibF.Proof.«inflate.c.local-fast-copy-match-invariant»
namespace Zlib.Inflate.Local
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

theorem FastInputPacket.copyMatch_effect
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
    (length : 3 ≤ l.len.toNat ∧ l.len.toNat ≤ 258)
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
    FastExecEffect h after r zs z s slow dest j l result 0 258 := by
  have validEffect
      (valid : l.dist > l.op → ¬ l.dist - l.op > c.whave) :
      FastExecEffect h after r zs z s slow dest j l result 0 258 := by
    obtain ⟨value, finalHeap, array, run, resultPacket,
      _, _, _, out, broke, _, _, _, _, _, heapEq, frame⟩ :=
      Zlib.Inflate.Local.FastInputPacket.copyMatch_valid_local_state packet invariant buffers
        left length.1 whaveBound wnextBound wsizeBound outPtr outputPtr
        outputGet outputWrite outputSize outputRoom produced valid windowData
    have equality := Prod.mk.inj (Except.ok.inj (run.symm.trans observed))
    rcases equality with ⟨rfl, rfl⟩
    have cursor : value.in_ = l.in_ := resultPacket.cursor.trans packet.cursor.symm
    have bits : value.bits = l.bits := resultPacket.bits.trans packet.bits.symm
    refine ⟨Or.inl ⟨array, heapEq, frame, broke⟩,
      ⟨j + l.len.toNat, out, by omega, by omega⟩, ?_,
      ⟨0, by omega, by simpa only [inputAdvance_zero] using cursor, by rw [bits]; omega⟩, ?_⟩
    · intro _
      exact ⟨j + l.len.toNat, out, by omega⟩
    · intro _
      rw [bits]
      exact Nat.le_max_left _ _
  by_cases windowBranch : l.dist > l.op
  · by_cases invalidBack : l.dist - l.op > c.whave
    · obtain ⟨i, finalHeap, run, heapEq, _, _, _, _, _, _⟩ :=
        Zlib.Inflate.Local.FastInputPacket.copyMatch_invalid_local_state packet invariant buffers
          streamPtr statePtr windowBranch invalidBack outputGet outputWrite
      have equality := Prod.mk.inj (Except.ok.inj (run.symm.trans observed))
      rcases equality with ⟨rfl, rfl⟩
      refine ⟨Or.inr (Or.inl ⟨i, rfl, heapEq⟩),
        ⟨j, outPtr, by omega, by omega⟩, ?_,
        ⟨0, by omega, ?_, by simp⟩, ?_⟩
      · intro impossible
        contradiction
      · simp only [inputAdvance_zero]
      · intro impossible
        contradiction
    · exact validEffect (fun _ => invalidBack)
  · exact validEffect (fun selected => False.elim (windowBranch selected))

#print axioms FastInputPacket.copyMatch_effect
end Zlib.Inflate.Local
