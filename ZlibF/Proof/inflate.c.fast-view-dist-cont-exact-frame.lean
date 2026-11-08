import ZlibF.Proof.«inflate.c.fast-view-diff-exact-frame»
import ZlibF.Proof.«inflate.c.fast-view-dist-cont-invariant»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The translated distance extra-bit suffix writes only through its
returned output cursor; extra-bit arithmetic itself changes no byte view. -/
theorem FastInputPacket.distCont_exact_frame
    {h : Heap} {slow : IL} {bs : List UInt8}
    {l : Zlib.Inffast.L} {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow bs l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow bs)
    (streamPtr : c.strm = some r)
    (statePtr : c.state = some (.tab zs))
    (whaveEq : c.whave = s.whave)
    (wsizeEq : c.wsize = s.wsize)
    (wnextEq : c.wnext = s.wnext)
    (windowEq : c.window = s.window)
    (extraBits : l.op.toNat ≤ slow.bits.toNat)
    (extraSmall : l.op.toNat < 32)
    (left : slow.left ≠ 0)
    (avail : 258 ≤ slow.left.toNat)
    (length : 3 ≤ l.len.toNat ∧ l.len.toNat ≤ 258)
    {dest : BRef} {output : Array UInt8} {oo bg j : Nat}
    (outPtr : l.out = .ref dest j)
    (outputPtr : slow.put = .ref dest oo)
    (begPtr : c.beg = .ref dest bg)
    (endPtr : c.end_ = .ref dest
      (oo + slow.left.toNat - 257))
    (outputGet : Space.get h dest = some output)
    (outputWrite : Space.ro h dest = false)
    (outputSize : oo + slow.left.toNat ≤ output.size)
    (current : oo ≤ j)
    (beginLe : bg ≤ j)
    (span : j - bg < 2 ^ 32)
    (guard : C.run (Ptr.lt l.out c.end_) h = .ok (true, h)) :
    ∃ result after k,
      C.run (Zlib.Inffast.Proofs.distCont c l) h =
        .ok (result, after) ∧
      result.out = .ref dest k ∧
      oo ≤ k ∧
      BufferFrame h after (fun b => StreamRoot r b ∨ b = zs)
        [⟨slow.put, k - oo⟩] := by
  let distance : UInt32 :=
    l.dist + (l.hold.toUInt32 &&& ((1 : UInt32) <<< l.op) - 1)
  let distanceLocal : Zlib.Inffast.L := { l with dist := distance }
  have distancePacket : FastInputPacket h slow bs distanceLocal :=
    ⟨packet.source, packet.cursor, packet.hold, packet.bits⟩
  have dropped := distancePacket.drop_bits_default_state
    buffers l.op extraBits (by omega)
  let slowNext : IL := { slow with
    hold := slow.hold >>> l.op.toUInt64,
    bits := slow.bits - l.op }
  let fastNext : Zlib.Inffast.L := { distanceLocal with
    hold := distanceLocal.hold >>> l.op.toUInt64,
    bits := distanceLocal.bits - l.op }
  have nextPacket : FastInputPacket h slowNext bs fastNext := dropped.1
  have nextBuffers : DispatchBuffers h r slowNext bs := dropped.2.1
  have nextOut : fastNext.out = .ref dest j := outPtr
  have nextLength : 3 ≤ fastNext.len.toNat ∧
      fastNext.len.toNat ≤ 258 := length
  have nextGuard : C.run (Ptr.lt fastNext.out c.end_) h =
      .ok (true, h) := guard
  obtain ⟨result, after, k, copyRun, out, lower, frame⟩ :=
    nextPacket.copy_match_after_diff_exact_frame invariant
      nextBuffers streamPtr statePtr whaveEq wsizeEq wnextEq
      windowEq left avail nextLength nextOut outputPtr begPtr
      endPtr outputGet outputWrite outputSize current beginLe
      span nextGuard
  have shlRun : C.run (Zlib.Inffast.shl32 1 l.op) h =
      .ok ((1 : UInt32) <<< l.op, h) := by
    exact Zlib.Inffast.Proofs.shl32_ok extraSmall
  have shrRun : C.run (Zlib.Inffast.shr64 l.hold l.op.toUInt64) h =
      .ok (l.hold >>> l.op.toUInt64, h) := by
    apply Zlib.Inffast.Proofs.shr64_ok
    rw [UInt32.toNat_toUInt64]
    omega
  have run : C.run (Zlib.Inffast.Proofs.distCont c l) h =
      .ok (result, after) := by
    change (Zlib.Inffast.Proofs.distCont c l) h =
      .ok (result, after)
    change Zlib.Inffast.shl32 1 l.op h =
      .ok ((1 : UInt32) <<< l.op, h) at shlRun
    change Zlib.Inffast.shr64 l.hold l.op.toUInt64 h =
      .ok (l.hold >>> l.op.toUInt64, h) at shrRun
    unfold Zlib.Inffast.Proofs.distCont
    rw [bind_ok shlRun]
    rw [bind_ok shrRun]
    simpa only [C.run, fastNext, distanceLocal, distance] using copyRun
  exact ⟨result, after, k, run, out, lower, frame⟩

#print axioms FastInputPacket.distCont_exact_frame

end Zlib.Inflate.Proofs
