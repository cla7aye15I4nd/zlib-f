import ZlibF.Proof.«inflate.c.fast-view-dolen-refill-exact-frame»
import ZlibF.Proof.«inflate.c.fast-view-dolen-extra-frame-invariant»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec
set_option autoImplicit false

/-- Length extra-bit arithmetic and the actual distance suffix retain the exact output prefix. -/
theorem FastInputPacket.dolenExt_exact_frame
    {h : Heap} {slow : IL}
    {first second third fourth : UInt8}
    {rest : List UInt8} {l : Zlib.Inffast.L}
    {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow
      (first :: second :: third :: fourth :: rest) l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow
      (first :: second :: third :: fourth :: rest))
    (streamPtr : c.strm = some r)
    (statePtr : c.state = some (.tab zs))
    (whaveEq : c.whave = s.whave)
    (wsizeEq : c.wsize = s.wsize)
    (wnextEq : c.wnext = s.wnext)
    (windowEq : c.window = s.window)
    {codeRef : CodeRef} {codes : Array Code}
    {baseOff rootWidth : Nat}
    (dcodePtr : c.dcode = .ref codeRef baseOff)
    (codesGet : Space.get h codeRef = some codes)
    (safe : DistTableSafe codes baseOff rootWidth)
    (mask : c.dmask.toUInt64.toNat = 2 ^ rootWidth - 1)
    (extraWidth : l.op.toNat ≤ 5)
    (extraFits : l.op.toNat ≤ slow.bits.toNat)
    (bitsBound : slow.bits.toNat ≤ 30)
    (left : slow.left ≠ 0)
    (avail : 258 ≤ slow.left.toNat)
    (length : 3 ≤ l.len.toNat ∧
      l.len.toNat + 2 ^ l.op.toNat ≤ 259)
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
      C.run (Zlib.Inffast.Proofs.dolenExt c l) h =
        .ok (result, after) ∧
      result.out = .ref dest k ∧
      oo ≤ k ∧
      BufferFrame h after (fun b => StreamRoot r b ∨ b = zs)
        [⟨slow.put, k - oo⟩] := by
  let extra : Nat := l.hold.toNat % 2 ^ l.op.toNat
  have opSmall : l.op.toNat < 32 := by omega
  have low := Zlib.Inffast.Proofs.hold_low32
    (x := l.hold) (k := l.op) opSmall
  have extraBound : extra < 2 ^ l.op.toNat := by
    exact Nat.mod_lt _ (Nat.pow_pos (by omega))
  have lenSum : l.len.toNat + extra ≤ 258 := by omega
  let delta : UInt32 := l.hold.toUInt32 &&&
    (((1 : UInt32) <<< l.op) - 1)
  have deltaEq : delta.toNat = extra := by
    simpa only [delta, extra] using low
  have lenValue : (l.len + delta).toNat =
      l.len.toNat + extra := by
    rw [Zlib.Inffast.Proofs.u32_toNat_add
      (by rw [deltaEq]; omega), deltaEq]
  have shlRun : Zlib.Inffast.shl32 1 l.op h =
      .ok ((1 : UInt32) <<< l.op, h) :=
    Zlib.Inffast.Proofs.shl32_ok opSmall
  have shrRun : Zlib.Inffast.shr64 l.hold l.op.toUInt64 h =
      .ok (l.hold >>> l.op.toUInt64, h) := by
    apply Zlib.Inffast.Proofs.shr64_ok
    rw [UInt32.toNat_toUInt64]
    omega
  let afterLen : Zlib.Inffast.L := { l with len := l.len + delta }
  have afterLenPacket : FastInputPacket h slow
      (first :: second :: third :: fourth :: rest) afterLen :=
    ⟨packet.source, packet.cursor, packet.hold, packet.bits⟩
  have within : l.op.toNat ≤ slow.bits.toNat := extraFits
  have dropped := afterLenPacket.drop_bits_default_state buffers
    l.op within (by omega)
  let slowDrop : IL := { slow with
    hold := slow.hold >>> l.op.toUInt64,
    bits := slow.bits - l.op }
  let fastDrop : Zlib.Inffast.L := { afterLen with
    hold := afterLen.hold >>> l.op.toUInt64,
    bits := afterLen.bits - l.op }
  have dropPacket : FastInputPacket h slowDrop
      (first :: second :: third :: fourth :: rest) fastDrop :=
    dropped.1
  have dropBuffers : DispatchBuffers h r slowDrop
      (first :: second :: third :: fourth :: rest) :=
    dropped.2.1
  have dropStream : stream slowDrop
      (first :: second :: third :: fourth :: rest) =
      (stream slow
        (first :: second :: third :: fourth :: rest)).drop
          l.op.toNat := dropped.2.2.1
  have dropBits : slowDrop.bits.toNat =
      slow.bits.toNat - l.op.toNat := dropped.2.2.2
  have dropBound : slowDrop.bits.toNat ≤ 30 := by omega
  have dropLength : 3 ≤ fastDrop.len.toNat ∧
      fastDrop.len.toNat ≤ 258 := by
    simpa only [fastDrop, afterLen, lenValue] using
      (show 3 ≤ l.len.toNat + extra ∧
        l.len.toNat + extra ≤ 258 by omega)
  have dropOut : fastDrop.out = .ref dest j := outPtr
  have dropPut : slowDrop.put = .ref dest oo := outputPtr
  have dropEnd : c.end_ = .ref dest
      (oo + slowDrop.left.toNat - 257) := endPtr
  have dropSize : oo + slowDrop.left.toNat ≤ output.size :=
    outputSize
  have dropGuard : C.run (Ptr.lt fastDrop.out c.end_) h =
      .ok (true, h) := guard
  obtain ⟨result, after, k, refillRun, out, lower, frame⟩ :=
    dropPacket.dolenRefill_exact_frame invariant dropBuffers
      streamPtr statePtr whaveEq wsizeEq wnextEq windowEq
      dcodePtr codesGet safe mask dropBound left avail
      dropLength dropOut dropPut begPtr dropEnd outputGet
      outputWrite dropSize current beginLe span dropGuard
  have run : C.run (Zlib.Inffast.Proofs.dolenExt c l) h =
      .ok (result, after) := by
    change (Zlib.Inffast.Proofs.dolenExt c l) h =
      .ok (result, after)
    unfold Zlib.Inffast.Proofs.dolenExt
    rw [bind_ok shlRun]
    rw [bind_ok shrRun]
    simpa only [fastDrop, afterLen, delta, C.run] using refillRun
  exact ⟨result, after, k, run, out, lower,
    by simpa only [slowDrop] using frame⟩

#print axioms FastInputPacket.dolenExt_exact_frame

end Zlib.Inflate.Proofs
