import ZlibF.Proof.«inflate.c.fast-view-body-output-bridge»
import ZlibF.Proof.«inflate.c.fast-view-dolen-root-complete-four-byte-cursor»
import ZlibF.Proof.«inflate.c.fast-view-body-six-cursor»
import ZlibF.Proof.«inffast.c.body-input-frame»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec
set_option autoImplicit false

/-- The translated fast body reads at most six input bytes on either path,
including the broken returns from the actual length/distance loop. -/
theorem FastInputPacket.fast_body_input_cursor_six
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
    (bitsBound : slow.bits.toNat ≤ 30)
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
    ∃ result after pulled,
      pulled ≤ 6 ∧
      C.run (Zlib.Inffast.inflate_fast_body c l) h =
        .ok (result, after) ∧
      result.in_ = inputAdvance l.in_ pulled := by
  by_cases small : slow.bits.toNat < 15
  · exact packet.fast_body_pull_input_cursor_six invariant buffers
      streamPtr statePtr mode whaveEq wsizeEq wnextEq windowEq
      lcodePtr codesGet safe lenMask dcodePtr distGet distSafe
      distMask small left avail outPtr outputPtr begPtr endPtr
      outputGet outputWrite outputSize current beginLe span guard
  · have enoughBits : ¬ l.bits < 15 := by
      intro lt
      have below : slow.bits.toNat < 15 := by
        rw [← packet.bits]
        simpa using UInt32.lt_iff_toNat_lt.mp lt
      exact small below
    obtain ⟨result, after, _, _, run, _, _, _, _, _⟩ := packet.fast_body_no_pull_output_bound
      invariant buffers streamPtr statePtr mode whaveEq wsizeEq
      wnextEq windowEq lcodePtr codesGet safe lenMask dcodePtr
      distGet distSafe distMask (by omega) bitsBound left avail
      outPtr outputPtr begPtr endPtr outputGet outputWrite
      outputSize current beginLe span guard
    obtain ⟨used, bound, cursor⟩ :=
      (Zlib.Inffast.Proofs.inflate_fast_body_no_initial_pull_cursor
        c l enoughBits) h result after run
    exact ⟨result, after, used, by omega, run, cursor⟩

#print axioms FastInputPacket.fast_body_input_cursor_six
end Zlib.Inflate.Proofs
