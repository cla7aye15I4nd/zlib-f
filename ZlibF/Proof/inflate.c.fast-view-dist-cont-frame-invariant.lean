import ZlibF.Proof.«inflate.c.fast-view-distance-post»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The final distance-extra-bit step preserves the input cursor and
caller output registers while executing the checked distance suffix. -/
theorem FastInputPacket.distCont_frame
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
      FastDistancePost h after r zs z s slowNext bs result
        dest output j l.len.toNat ∧
      stream slowNext bs = (stream slow bs).drop l.op.toNat ∧
      slowNext.put = slow.put ∧
      slowNext.left = slow.left ∧
      slowNext.next = slow.next ∧
      slowNext.have_ = slow.have_ ∧
      result.in_ = l.in_ := by
  let slowNext : IL := { slow with
    hold := slow.hold >>> l.op.toUInt64,
    bits := slow.bits - l.op }
  obtain ⟨result, after, run, post, source⟩ :=
    packet.distCont_post invariant buffers streamPtr statePtr
      whaveEq wsizeEq wnextEq windowEq extraBits extraSmall
      left avail length outPtr outputPtr begPtr endPtr
      outputGet outputWrite outputSize current beginLe span guard
  have inputEq : result.in_ = l.in_ := by
    calc
      result.in_ = slowNext.next := post.1.cursor
      _ = slow.next := rfl
      _ = l.in_ := packet.cursor.symm
  exact ⟨result, after, run, post, source,
    rfl, rfl, rfl, rfl, inputEq⟩

end Zlib.Inflate.Proofs
