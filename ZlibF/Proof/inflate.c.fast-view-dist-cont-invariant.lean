import ZlibF.Proof.«inflate.c.fast-view-drop-invariant»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The actual distance-extra-bit suffix executes on caller byte views,
retains the public buffer packet and either copies or enters BAD. -/
theorem FastInputPacket.distCont_default_state
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
    let slowNext : IL := { slow with
      hold := slow.hold >>> l.op.toUInt64,
      bits := slow.bits - l.op }
    ∃ result after,
      C.run (Zlib.Inffast.Proofs.distCont c l) h =
        .ok (result, after) ∧
      FastInputPacket after slowNext bs result ∧
      DispatchBuffers after r slowNext bs ∧
      ByteViewSizes h after ∧
      ((∃ i, result.broke = true ∧
        after = setI
          (r.put h { z with msg := .ref (.str i) 0 }) zs
          { s with mode := BAD } ∧
        DefaultStateJ after r zs
          { z with msg := .ref (.str i) 0 } { s with mode := BAD } ∧
        Space.get after dest = some output ∧
        Space.ro after dest = false) ∨
       (∃ array, DefaultStateJ after r zs z s ∧
        result.out = .ref dest (j + l.len.toNat) ∧
        Space.get after dest = some array ∧
        array.size = output.size ∧
        Space.ro after dest = false ∧
        after = Space.put h dest array ∧
        BufferFrame h after (fun _ => False)
          [⟨slow.put, slow.left.toNat⟩])) := by
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
  have nextLength : 3 ≤ fastNext.len.toNat ∧ fastNext.len.toNat ≤ 258 := length
  have nextGuard : C.run (Ptr.lt fastNext.out c.end_) h = .ok (true, h) := guard
  obtain ⟨result, after, copyRun, resultPacket, resultBuffers,
    sizes, _, _, outcome⟩ :=
    nextPacket.copy_match_after_diff_default_state invariant
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
  refine ⟨result, after, run, resultPacket, resultBuffers,
    sizes, ?_⟩
  rcases outcome with bad | copied
  · exact Or.inl bad
  · rcases copied with ⟨array, _, nextInvariant, out,
        bytes, size, write, heapEq, frame⟩
    exact Or.inr ⟨array, nextInvariant, out, bytes,
      size, write, heapEq, frame⟩

end Zlib.Inflate.Proofs
