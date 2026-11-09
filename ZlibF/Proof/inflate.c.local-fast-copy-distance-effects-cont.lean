import ZlibF.Proof.«inflate.c.local-fast-copy-distance-effects-diff»
import ZlibF.Proof.«inflate.c.local-fast-parser-dist-cont-invariant»
namespace Zlib.Inflate.Local
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

theorem FastInputPacket.distCont_effect
    {h : Heap} {cutoff : Nat} {slow : IL} {bs : List UInt8}
    {l : Zlib.Inffast.L} {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow bs l)
    (invariant : LocalStateJ h cutoff r zs z s)
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
    (guard : C.run (Ptr.lt l.out c.end_) h = .ok (true, h))
    {result : Zlib.Inffast.L} {after : Heap}
    (observed : C.run (Zlib.Inffast.Proofs.distCont c l) h = .ok (result, after)) :
    FastExecEffect h after r zs z s slow dest j l result 0 258 := by
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
  have shlRun : C.run (Zlib.Inffast.shl32 1 l.op) h =
      .ok ((1 : UInt32) <<< l.op, h) := by
    exact Zlib.Inffast.Proofs.shl32_ok extraSmall
  have shrRun : C.run (Zlib.Inffast.shr64 l.hold l.op.toUInt64) h =
      .ok (l.hold >>> l.op.toUInt64, h) := by
    apply Zlib.Inffast.Proofs.shr64_ok
    rw [UInt32.toNat_toUInt64]
    omega
  have copied : C.run (do
      let d ← Ptr.diff fastNext.out c.beg
      Zlib.Inffast.copyMatch c { fastNext with op := d.toUInt64.toUInt32 }) h =
      .ok (result, after) := by
    change (Zlib.Inffast.Proofs.distCont c l) h = .ok (result, after) at observed
    unfold Zlib.Inffast.Proofs.distCont at observed
    change Zlib.Inffast.shl32 1 l.op h = .ok ((1 : UInt32) <<< l.op, h) at shlRun
    change Zlib.Inffast.shr64 l.hold l.op.toUInt64 h = .ok (l.hold >>> l.op.toUInt64, h) at shrRun
    rw [bind_ok shlRun, bind_ok shrRun] at observed
    exact observed
  have effect := Zlib.Inflate.Local.FastInputPacket.copy_match_after_diff_effect nextPacket invariant
    nextBuffers streamPtr statePtr whaveEq wsizeEq wnextEq windowEq left avail
    nextLength nextOut outputPtr begPtr endPtr outputGet outputWrite outputSize
    current beginLe span nextGuard copied
  have bitLe : fastNext.bits.toNat ≤ l.bits.toNat := by
    change (l.bits - l.op).toNat ≤ l.bits.toNat
    rw [Zlib.Inffast.Proofs.u32_toNat_sub (by rw [packet.bits]; exact extraBits)]
    omega
  exact effect.prefix (pulled := 0) rfl rfl rfl (by simp only [fastNext, distanceLocal, inputAdvance_zero])
    (by omega) (by exact Nat.le_trans bitLe (Nat.le_max_left _ _)) (by omega) (by omega)

#print axioms FastInputPacket.distCont_effect
end Zlib.Inflate.Local
