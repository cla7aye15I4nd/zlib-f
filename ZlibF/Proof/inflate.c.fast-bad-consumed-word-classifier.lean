import ZlibF.Proof.«inflate.c.fast-base-bad-consumed-word»
namespace Zlib.Inflate.Proofs.FastArbitraryBody
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inffast.Spec Zlib.Inftrees
open Zlib.Inftrees.Spec.DecodeTableInvariant Zlib.Inftrees.Spec.DecodeTableStability
open Zlib.Inffast.Proofs ZlibF.Math.LZ77Copy
set_option autoImplicit false
set_option maxRecDepth 8192
/-- Exhaustive actual source behavior either stays outside BAD or produces
a DROP-consumed word rejected under every completion. Constructor/fixed
QueryTake facts are internal representation producers, not public inputs. -/
theorem BodyLengthCut.nonbad_or_rejected
    {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {c : Zlib.Inffast.Ctx} {ref dref : CodeRef} {codes dcodes : Array Code}
    {offset root extent doff droot dextent : Nat} {L D : List Nat}
    {slow : IL} {fast : Zlib.Inffast.L} {bs dict : List UInt8}
    (cut : BodyLengthCut h r c ref codes offset root slow fast bs)
    (invariant : DefaultStateJ h r zs z s) (get : Space.get h ref = some codes)
    (inv : Inv LENS codes offset root extent L)
    (flags : Zlib.Inftrees.Spec.FastTableFlags.QueryCompatible LENS codes offset root)
    (lstable : StableQuery LENS codes offset root)
    (ltake : Zlib.Inftrees.Proofs.QueryTakeSource.QueryTake LENS codes offset root)
    (capacity : 48 ≤ (stream slow bs).length)
    (dptr : c.dcode = .ref dref doff) (dget : Space.get h dref = some dcodes)
    (dsafe : DistTableSafe dcodes doff droot) (dmask : c.dmask.toUInt64.toNat = 2 ^ droot - 1)
    (dinv : Inv DISTS dcodes doff droot dextent D)
    (dflags : Zlib.Inftrees.Spec.FastTableFlags.QueryCompatible DISTS dcodes doff droot)
    (dstable : StableQuery DISTS dcodes doff droot)
    (dtake : Zlib.Inftrees.Proofs.QueryTakeSource.QueryTake DISTS dcodes doff droot)
    (mode : DataTableMode s.mode)
    (streamPtr : c.strm = some r) (statePtr : c.state = some (.tab zs))
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
    BodyNonBad h r zs c fast ∨ BadWordResult h r zs z s c slow fast bs dict (writtenBytes output j (j - bg)) L D := by

  let entry := codes.getD cut.selection.index default
  by_cases literal : entry.op = 0
  · obtain ⟨result, after, finalSlow, byte, actual, _input, _out, _heap, _get, _packet, currentState, _buffers, _token⟩ :=
      cut.literal_source (D := D) invariant get inv literal left avail outPtr put endPtr outputGet write size current beginLe guard dict
    exact Or.inl ⟨result, after, z, s, actual, currentState.good, data_mode_ne_bad mode⟩
  · by_cases base : entry.op &&& 16 ≠ 0
    · exact cut.base_nonbad_or_rejected invariant get inv flags base capacity dptr dget dsafe dmask dinv dflags
        dstable dtake mode streamPtr statePtr left avail whave wnext wsize outPtr put begPtr endPtr outputGet write size
        current beginLe span guard windowData dictionary dictCount
    · have noBase : entry.op &&& 16 = 0 := Classical.not_not.mp base
      have terminal : entry.op &&& 64 ≠ 0 := by
        have shape := cut.selection.leaf.2
        rcases shape with ordinary | length | rejected
        · exact False.elim (literal ordinary)
        · exact False.elim (length.1 noBase)
        · exact rejected.2
      by_cases ending : entry.op &&& 32 ≠ 0
      · have accepted : Zlib.Inftrees.Spec.DecodeSoundness.LeafAccepted LENS entry := by
          simp only [Zlib.Inftrees.Spec.DecodeSoundness.LeafAccepted, ite_true]
          exact Or.inl (by simpa only [bne_iff_ne] using ending)
        obtain ⟨result, finalSlow, actual, _input, _broke, _out, _packet, currentState, _buffers, _token⟩ :=
          cut.eob_source (D := D) invariant get statePtr mode inv accepted literal noBase dict (writtenBytes output j (j - bg))
        exact Or.inl ⟨result, _, z, {s with mode := TYPE}, actual, currentState.good, by change TYPE ≠ BAD; decide⟩
      · have noEnd : entry.op &&& 32 = 0 := Classical.not_not.mp ending
        have rejected : ¬ Zlib.Inftrees.Spec.DecodeSoundness.LeafAccepted LENS entry := by
          simp only [Zlib.Inftrees.Spec.DecodeSoundness.LeafAccepted, ite_true]
          intro accepted
          rcases accepted with endCode | valid
          · have nz : entry.op &&& 32 ≠ 0 := by simpa only [bne_iff_ne] using endCode
            exact nz noEnd
          · exact terminal valid
        exact Or.inr (cut.invalid_consumed_word invariant get streamPtr statePtr inv lstable ltake rejected noBase
          dict (writtenBytes output j (j - bg)))

theorem fast_body_nonbad_or_rejected_word
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
    (lstable : StableQuery LENS codes offset root)
    (ltake : Zlib.Inftrees.Proofs.QueryTakeSource.QueryTake LENS codes offset root)
    (dptr : c.dcode = .ref dref doff) (dget : Space.get h dref = some dcodes)
    (dsafe : DistTableSafe dcodes doff droot) (dmask : c.dmask.toUInt64.toNat = 2 ^ droot - 1)
    (dinv : Inv DISTS dcodes doff droot dextent D)
    (dflags : Zlib.Inftrees.Spec.FastTableFlags.QueryCompatible DISTS dcodes doff droot)
    (dstable : StableQuery DISTS dcodes doff droot)
    (dtake : Zlib.Inftrees.Proofs.QueryTakeSource.QueryTake DISTS dcodes doff droot)
    (mode : DataTableMode s.mode)
    (streamPtr : c.strm = some r) (statePtr : c.state = some (.tab zs))
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
    BodyNonBad h r zs c fast ∨ BadWordResult h r zs z s c slow fast bs dict (writtenBytes output j (j - bg)) L D := by

  obtain ⟨cut⟩ := body_length_source_cut packet invariant buffers margin bits lptr get lsafe inv lstable lmask
  have capacity : 48 ≤ (stream slow bs).length := by
    simp only [stream, List.length_append, natBits_length, bytesBits_length]
    have count := buffers.bits.have_eq
    omega
  exact cut.nonbad_or_rejected invariant get inv flags lstable ltake capacity dptr dget dsafe dmask dinv dflags
    dstable dtake mode streamPtr statePtr left avail whave wnext wsize outPtr put begPtr endPtr outputGet write size
    current beginLe span guard windowData dictionary dictCount

#print axioms BodyLengthCut.nonbad_or_rejected
#print axioms fast_body_nonbad_or_rejected_word
end Zlib.Inflate.Proofs.FastArbitraryBody
