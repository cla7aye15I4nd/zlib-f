import ZlibF.Proof.«inflate.c.fast-arbitrary-body-classifier»
import ZlibF.Proof.«inflate.c.fast-view-loop-ready-invariant»
namespace Zlib.Inflate.Proofs.FastArbitraryBody
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inffast.Spec Zlib.Inftrees
open Zlib.Inftrees.Spec.DecodeTableInvariant Zlib.Inftrees.Spec.DecodeTableStability
open Zlib.Inffast.Proofs ZlibF.Math.LZ77Copy
set_option autoImplicit false
set_option maxRecDepth 8192
/-- Actual safety resources and constructor-derived table meaning classify
the full generic fast body on arbitrary current input. Independent token
syntax, valid future and distance availability are all conclusions. -/
theorem fast_body_arbitrary_current
    {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {c : Zlib.Inffast.Ctx} {ref dref : CodeRef} {codes dcodes : Array Code}
    {offset root extent doff droot dextent : Nat} {L D : List Nat}
    {slow : IL} {fast : Zlib.Inffast.L} {bs dict : List UInt8}
    (packet : FastInputPacket h slow bs fast) (buffers : DispatchBuffers h r slow bs)
    (margin : 6 ≤ slow.have_.toNat) (bits : slow.bits.toNat ≤ 30)
    (lptr : c.lcode = .ref ref offset) (lsafe : LenTableSafe codes offset root)
    (lmask : c.lmask.toUInt64.toNat = 2 ^ root - 1)
    (invariant : DefaultStateJ h r zs z s) (get : Space.get h ref = some codes)
    (inv : Inv LENS codes offset root extent L)
    (flags : Zlib.Inftrees.Spec.FastTableFlags.QueryCompatible LENS codes offset root)
    (stable : StableQuery LENS codes offset root)
    (dptr : c.dcode = .ref dref doff) (dget : Space.get h dref = some dcodes)
    (dsafe : DistTableSafe dcodes doff droot) (dmask : c.dmask.toUInt64.toNat = 2 ^ droot - 1)
    (dinv : Inv DISTS dcodes doff droot dextent D)
    (dflags : Zlib.Inftrees.Spec.FastTableFlags.QueryCompatible DISTS dcodes doff droot)
    (streamPtr : c.strm = some r) (statePtr : c.state = some (.tab zs))
    (mode : DataTableMode s.mode)
    (left : slow.left ≠ 0) (avail : 258 ≤ slow.left.toNat)
    (whave : c.whave.toNat ≤ c.wsize.toNat) (wnext : c.wnext.toNat ≤ c.wsize.toNat) (wsize : c.wsize.toNat ≤ 32768)
    {dest : BRef} {output saved : Array UInt8} {oo bg j woff : Nat}
    (outPtr : fast.out = .ref dest j) (put : slow.put = .ref dest oo) (begPtr : c.beg = .ref dest bg)
    (endPtr : c.end_ = .ref dest (oo + slow.left.toNat - 257))
    (outputGet : Space.get h dest = some output) (write : Space.ro h dest = false)
    (size : oo + slow.left.toNat ≤ output.size) (current : oo ≤ j) (beginLe : bg ≤ j) (span : j - bg < 2 ^ 32)
    (guard : C.run (Ptr.lt fast.out c.end_) h = .ok (true, h))
    (windowData : c.whave ≠ 0 → ∃ window, window ≠ dest ∧ c.window = .ref window woff ∧
      Space.get h window = some saved ∧ woff + c.wsize.toNat ≤ saved.size)
    (dictionary : MatchHistory.saved saved c.wsize.toNat c.wnext.toNat c.whave.toNat woff = dict)
    (dictCount : dict.length = c.whave.toNat) :
    BodyResult h r zs z s c slow fast bs dict L D dest output j bg := by
  obtain ⟨cut⟩ := body_length_source_cut packet invariant buffers margin bits lptr get lsafe inv stable lmask
  have capacity : 48 ≤ (stream slow bs).length := by
    simp only [stream, List.length_append, natBits_length, bytesBits_length]
    have count := buffers.bits.have_eq
    omega
  exact cut.classify_result invariant get inv flags stable capacity dptr dget dsafe dmask dinv dflags
    streamPtr statePtr mode left avail whave wnext wsize outPtr put begPtr endPtr outputGet write size
    current beginLe span guard windowData dictionary dictCount

#print axioms fast_body_arbitrary_current
end Zlib.Inflate.Proofs.FastArbitraryBody
