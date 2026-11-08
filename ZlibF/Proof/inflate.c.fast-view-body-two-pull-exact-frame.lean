import ZlibF.Proof.«inflate.c.fast-view-dolen-root-complete-four-byte-exact-frame»
import ZlibF.Proof.«inflate.c.fast-view-body-pull-branch-frame-invariant»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec
set_option autoImplicit false

/-- The actual two-pull fast body changes only its returned output prefix. -/
theorem FastInputPacket.fast_body_two_pull_exact_frame
    {h : Heap} {slow : IL}
    {first second third fourth fifth sixth : UInt8}
    {rest : List UInt8} {l : Zlib.Inffast.L}
    {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow
      (first :: second :: third :: fourth :: fifth :: sixth :: rest) l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow
      (first :: second :: third :: fourth :: fifth :: sixth :: rest))
    (streamPtr : c.strm = some r)
    (statePtr : c.state = some (.tab zs))
    (mode : DataTableMode s.mode)
    (whaveEq : c.whave = s.whave)
    (wsizeEq : c.wsize = s.wsize)
    (wnextEq : c.wnext = s.wnext)
    (windowEq : c.window = s.window)
    {codeRef : CodeRef} {codes : Array Code}
    {baseOff rootWidth : Nat}
    (lcodePtr : c.lcode = .ref codeRef baseOff)
    (codesGet : Space.get h codeRef = some codes)
    (safe : LenTableSafe codes baseOff rootWidth)
    (lenMask : c.lmask.toUInt64.toNat = 2 ^ rootWidth - 1)
    {distRef : CodeRef} {distCodes : Array Code}
    {distOff distWidth : Nat}
    (dcodePtr : c.dcode = .ref distRef distOff)
    (distGet : Space.get h distRef = some distCodes)
    (distSafe : DistTableSafe distCodes distOff distWidth)
    (distMask : c.dmask.toUInt64.toNat = 2 ^ distWidth - 1)
    (small : slow.bits.toNat < 15)
    (left : slow.left ≠ 0)
    (avail : 258 ≤ slow.left.toNat)
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
      C.run (Zlib.Inffast.inflate_fast_body c l) h =
        .ok (result, after) ∧
      result.out = .ref dest k ∧
      oo ≤ k ∧
      BufferFrame h after (fun b => StreamRoot r b ∨ b = zs)
        [⟨slow.put, k - oo⟩] := by
  obtain ⟨next1, fast1, slow1, pull1, next1Eq, slow1Eq,
    fast1Eq, packet1, _, buffers1, stream1⟩ :=
    packet.pull_default_state invariant buffers (by omega)
  have small1 : slow1.bits.toNat ≤ 22 := by
    rw [slow1Eq]
    change (slow.bits + 8).toNat ≤ 22
    rw [u32_add8 slow.bits (by omega)]
    omega
  obtain ⟨next2, fast2, slow2, pull2, next2Eq, slow2Eq,
    fast2Eq, packet2, _, buffers2, stream2⟩ :=
    packet1.pull_default_state invariant buffers1 small1
  have bits1 : slow1.bits.toNat = slow.bits.toNat + 8 := by
    rw [slow1Eq]
    exact u32_add8 slow.bits (by omega)
  have bits2 : slow2.bits.toNat = slow1.bits.toNat + 8 := by
    rw [slow2Eq]
    exact u32_add8 slow1.bits (by omega)
  have held2 : 16 ≤ slow2.bits.toNat := by omega
  have bitsBound2 : slow2.bits.toNat ≤ 30 := by omega
  let rootSlice := (fast2.hold &&& c.lmask.toUInt64).toNat
  let selected : Zlib.Inffast.L :=
    { fast2 with here := .ref codeRef (baseOff + rootSlice) }
  obtain ⟨root, addRun, selectedPacket⟩ :=
    packet2.fast_body_root_lookup lcodePtr codesGet safe lenMask
  have out2 : selected.out = .ref dest j := by
    simp only [selected, fast2Eq, fast1Eq,
      Zlib.Inffast.Proofs.pullL]
    exact outPtr
  have put2 : slow2.put = .ref dest oo := by
    simpa only [slow2Eq, slow1Eq, pulled] using outputPtr
  have end2 : c.end_ = .ref dest
      (oo + slow2.left.toNat - 257) := by
    simpa only [slow2Eq, slow1Eq, pulled] using endPtr
  have left2 : slow2.left ≠ 0 := by
    simpa only [slow2Eq, slow1Eq, pulled] using left
  have avail2 : 258 ≤ slow2.left.toNat := by
    simpa only [slow2Eq, slow1Eq, pulled] using avail
  have size2 : oo + slow2.left.toNat ≤ output.size := by
    simpa only [slow2Eq, slow1Eq, pulled] using outputSize
  have guard2 : C.run (Ptr.lt selected.out c.end_) h =
      .ok (true, h) := by
    simpa only [out2, outPtr] using guard
  obtain ⟨result, after, k, loopRun, out, lower, frame⟩ :=
    selectedPacket.dolen_root_complete_four_byte_exact_frame
      invariant buffers2 streamPtr statePtr mode whaveEq
      wsizeEq wnextEq windowEq rfl lcodePtr codesGet
      safe root dcodePtr distGet distSafe distMask held2
      bitsBound2 left2 avail2 out2 put2 begPtr end2
      outputGet outputWrite size2 current beginLe span guard2
  have needsPull : l.bits < 15 := by
    rw [packet.bits]
    exact UInt32.lt_iff_toNat_lt.mpr small
  have bodyRun : C.run (Zlib.Inffast.inflate_fast_body c l) h =
      .ok (result, after) := by
    change (Zlib.Inffast.inflate_fast_body c l) h =
      .ok (result, after)
    unfold Zlib.Inffast.inflate_fast_body
    simp only [needsPull, ite_true]
    change (Zlib.Inffast.pull l >>= fun q =>
      Zlib.Inffast.pull q >>= fun q' =>
        Ptr.add c.lcode
          (q'.hold &&& c.lmask.toUInt64).toNat >>= fun here =>
          cdoWhile (Zlib.Inffast.dolen c)
            (fun current => pure (current.againL, current))
            { q' with here }) h = .ok (result, after)
    change Zlib.Inffast.pull l h = .ok (fast1, h) at pull1
    change Zlib.Inffast.pull fast1 h = .ok (fast2, h) at pull2
    change Ptr.add c.lcode rootSlice h =
      .ok (.ref codeRef (baseOff + rootSlice), h) at addRun
    change (cdoWhile (Zlib.Inffast.dolen c)
      (fun current => pure (current.againL, current))
      selected) h = .ok (result, after) at loopRun
    simp only [bind_app, pull1, pull2, addRun, loopRun,
      rootSlice, selected]
  exact ⟨result, after, k, bodyRun, out, lower,
    by simpa only [put2, outputPtr] using frame⟩

#print axioms FastInputPacket.fast_body_two_pull_exact_frame

end Zlib.Inflate.Proofs
