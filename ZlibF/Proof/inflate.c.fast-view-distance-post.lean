import ZlibF.Proof.«inflate.c.fast-view-pull-invariant»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The complete caller-view state after a distance copy or a BAD distance.
This is a proof interface for composing the refill branches. -/
def FastDistancePost
    (before after : Heap) (r : ZStreamRef) (zs : Nat)
    (z : ZStream) (s : InflateState)
    (slow : IL) (bs : List UInt8) (result : Zlib.Inffast.L)
    (dest : BRef) (output : Array UInt8) (j length : Nat) : Prop :=
  FastInputPacket after slow bs result ∧
  DispatchBuffers after r slow bs ∧
  ByteViewSizes before after ∧
  ((∃ i, result.broke = true ∧
    after = setI
      (r.put before { z with msg := .ref (.str i) 0 }) zs
      { s with mode := BAD } ∧
    DefaultStateJ after r zs
      { z with msg := .ref (.str i) 0 } { s with mode := BAD } ∧
    Space.get after dest = some output ∧
    Space.ro after dest = false) ∨
   (∃ array, DefaultStateJ after r zs z s ∧
    result.out = .ref dest (j + length) ∧
    Space.get after dest = some array ∧
    array.size = output.size ∧
    Space.ro after dest = false ∧
    after = Space.put before dest array ∧
    BufferFrame before after (fun _ => False)
      [⟨slow.put, slow.left.toNat⟩]))

/-- The distance-extra-bit suffix supplies the shared postcondition and
removes precisely the extra bits from the abstract input stream. -/
theorem FastInputPacket.distCont_post
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
      stream slowNext bs = (stream slow bs).drop l.op.toNat := by
  obtain ⟨result, after, run, nextPacket, nextBuffers,
    sizes, outcome⟩ :=
    packet.distCont_default_state invariant buffers streamPtr
      statePtr whaveEq wsizeEq wnextEq windowEq extraBits
      extraSmall left avail length outPtr outputPtr begPtr
      endPtr outputGet outputWrite outputSize current beginLe
      span guard
  have dropped := DROPBITS_inv packet.source l.op extraBits (by omega)
  exact ⟨result, after, run,
    ⟨nextPacket, nextBuffers, sizes, outcome⟩,
    dropped.2.1⟩

end Zlib.Inflate.Proofs
