import ZlibF.Proof.«inflate.c.fast-view-dodist-loop-bits-invariant»
import ZlibF.Proof.«inflate.c.fast-view-dolen-dist-frame-invariant»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec
set_option autoImplicit false

/-- Selecting the distance root table leaves the held-bit count unchanged;
the checked distance loop bounds every nonbreaking result. -/
theorem FastInputPacket.dolenDist_bits_default_state
    {h : Heap} {slow : IL} {first second : UInt8}
    {rest : List UInt8} {l : Zlib.Inffast.L}
    {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow (first :: second :: rest) l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow (first :: second :: rest))
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
    (held : 15 ≤ slow.bits.toNat)
    (bitsBound : slow.bits.toNat ≤ 30)
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
    ∃ used slowNext result after,
      C.run (Zlib.Inffast.Proofs.dolenDist c l) h =
        .ok (result, after) ∧
      FastInputPacket after slowNext
        ((first :: second :: rest).drop used) result ∧
      (result.broke = false → slowNext.bits.toNat ≤ 30) := by
  obtain ⟨used, _, slowNext, result, after, _, _, run,
    _, finalPacket, _, _, _, _, _⟩ :=
    packet.dolenDist_frame_default_state invariant buffers
      streamPtr statePtr whaveEq wsizeEq wnextEq windowEq
      dcodePtr codesGet safe mask held left avail length
      outPtr outputPtr begPtr endPtr outputGet outputWrite
      outputSize current beginLe span guard
  let idx : Nat := (l.hold &&& c.dmask.toUInt64).toNat
  have idxEq : idx = l.hold.toNat % 2 ^ rootWidth :=
    Zlib.Inffast.Proofs.u64_and_mask mask
  have idxBound : idx < 2 ^ rootWidth := by
    rw [idxEq]
    exact Nat.mod_lt _ (Nat.pow_pos (by omega))
  have addRun : C.run (Ptr.add c.dcode idx) h =
      .ok (.ref codeRef (baseOff + idx), h) := by
    rw [dcodePtr]
    exact Ptr.add_nat_ok codesGet (by
      have rootSize := safe.2.1
      omega)
  let selected : Zlib.Inffast.L :=
    { l with here := .ref codeRef (baseOff + idx) }
  have selectedPacket : FastInputPacket h slow
      (first :: second :: rest) selected :=
    ⟨packet.source, packet.cursor, packet.hold, packet.bits⟩
  obtain ⟨used0, slowLoop, result0, after0, loopRun,
    loopPacket, loopBound⟩ :=
    selectedPacket.dodist_loop_bits_default_state invariant
      buffers streamPtr statePtr whaveEq wsizeEq wnextEq
      windowEq (by rfl) dcodePtr codesGet safe idxBound
      held bitsBound left avail length outPtr outputPtr
      begPtr endPtr outputGet outputWrite outputSize current
      beginLe span guard
  have run0 : C.run (Zlib.Inffast.Proofs.dolenDist c l) h =
      .ok (result0, after0) := by
    change (Zlib.Inffast.Proofs.dolenDist c l) h =
      .ok (result0, after0)
    unfold Zlib.Inffast.Proofs.dolenDist
    change Ptr.add c.dcode idx h =
      .ok (.ref codeRef (baseOff + idx), h) at addRun
    rw [bind_ok addRun]
    simpa [C.run, selected] using loopRun
  rw [run] at run0
  cases run0
  have sameBits : slowNext.bits = slowLoop.bits :=
    finalPacket.bits.symm.trans loopPacket.bits
  have finalBound : result.broke = false →
      slowNext.bits.toNat ≤ 30 := by
    intro notBroken
    rw [sameBits]
    exact loopBound notBroken
  exact ⟨used, slowNext, result, after, run,
    finalPacket, finalBound⟩

end Zlib.Inflate.Proofs
